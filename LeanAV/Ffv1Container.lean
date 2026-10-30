import LeanAV.Ffv1

namespace LeanAV.Ffv1Container

structure Stream where
  width : Nat
  height : Nat
  timeNum : Nat := 1
  timeDen : Nat := 25
  sarNum : Nat := 0
  sarDen : Nat := 1
  config : ByteArray
  packets : Array ByteArray
  keyframes : Array Bool := #[]
  deriving Inhabited, DecidableEq

private def packetIsKeyframe (s : Stream) (idx : Nat) : Bool :=
  if h : idx < s.keyframes.size then s.keyframes[idx]
  else
    let p := s.packets[idx]?.getD ByteArray.empty
    let rd := LeanAV.Ffv1.RangeDecoder.init p
    if rd.failed then true else (rd.getStateBit #[128] 0).1

private def bytes (s : String) : ByteArray := s.toUTF8
private def zeros (n : Nat) : ByteArray := ByteArray.mk (Array.replicate n 0)
private def be (n v : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for i in [:n] do out := out.push (v / 256 ^ (n - i - 1) % 256).toUInt8
  return out
private def le (n v : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for i in [:n] do out := out.push (v / 256 ^ i % 256).toUInt8
  return out
private def uint (b : ByteArray) (p n : Nat) (little : Bool := false) : Nat := Id.run do
  let mut v := 0
  for i in [:n] do
    let j := if little then n - i - 1 else i
    v := v * 256 + (b[p + j]?.getD 0).toNat
  return v
private def text (b : ByteArray) (p n : Nat) : String :=
  match String.fromUTF8? (b.extract p (p + n)) with
  | some s => s
  | none => ""
private def slice (b : ByteArray) (p n : Nat) : Except String ByteArray :=
  if p > b.size || n > b.size - p then .error "Truncated container payload"
  else .ok (b.extract p (p + n))
private def ratio (n d : Nat) : Nat × Nat :=
  let g := Nat.gcd n d
  (n / g, d / g)

/-- Resolve Matroska video track `(sarNum, sarDen)` from `(width, height)`, optional
    `DisplayWidth`/`DisplayHeight` (`0x54B0`/`0x54BA`), and `DisplayUnit` (`0x54B2`, default `0`). -/
def resolveMkvSar (width height : Nat) (dwOpt dhOpt : Option Nat) (unit : Nat) :
    Except String (Nat × Nat) := do
  if unit > 4 then throw "Invalid Matroska display unit"
  let dw := dwOpt.getD (if unit == 0 then width else 0)
  let dh := dhOpt.getD (if unit == 0 then height else 0)
  if (dwOpt.isSome || dhOpt.isSome) && (dw == 0 || dh == 0) then
    throw "Invalid Matroska display dimensions"
  if dwOpt.isNone && dhOpt.isNone then
    return if unit == 4 then (0, 1) else (1, 1)
  else if dw > 0 && dh > 0 && width > 0 && height > 0 then
    return ratio (dw * height) (dh * width)
  else
    return if unit == 4 then (0, 1) else (1, 1)

/-- Compute `(dwOpt, dhOpt, unitOpt)` emitted by `muxMkv` for `(width, height, sarNum, sarDen)`. -/
def encodeMkvDisplay (width height sarNum sarDen : Nat) : Option Nat × Option Nat × Option Nat :=
  if sarNum == 0 then (none, none, some 4)
  else if ratio sarNum sarDen == (1, 1) then (none, none, none)
  else
    let (dw, dh) := ratio (width * sarNum) (height * sarDen)
    (some dw, some dh, some 3)
private def validate (s : Stream) : Except String Unit := do
  if s.width == 0 || s.height == 0 || s.width > 65535 || s.height > 65535 then
    throw "Invalid container dimensions"
  if s.timeNum == 0 || s.timeDen == 0 || s.timeNum > 0xFFFFFFFF ||
      s.timeDen > 0xFFFFFFFF || s.sarDen == 0 || s.sarNum > 0xFFFFFFFF ||
      s.sarDen > 0xFFFFFFFF then throw "Invalid container rational"
  if s.config.size > 1048576 then throw "FFV1 configuration too large"
  if s.config.isEmpty then throw "FFV1 version 0/1 stream requires configuration record"
  if s.config.size < 6 || LeanAV.Ffv1.crc32 s.config != 0 then
    throw "Invalid FFV1 configuration checksum"
  let _ ← LeanAV.Ffv1.parseConfiguration s.config
  for p in s.packets do
    if p.isEmpty then throw "Empty FFV1 packet"

private structure Node where
  id : Nat
  pos : Nat
  stop : Nat
  deriving Inhabited

private def vint (b : ByteArray) (p stop : Nat) (identifier : Bool := false) :
    Except String (Nat × Nat × Bool) := do
  if p >= stop || stop > b.size then throw "Truncated EBML integer"
  let first := uint b p 1
  let mut size := 0
  for i in [:8] do
    if size == 0 && first &&& (128 / 2 ^ i) != 0 then size := i + 1
  if size == 0 || (identifier && size > 4) || size > stop - p then
    throw "Invalid EBML integer"
  let raw := uint b p size
  let value := if identifier then raw else raw - 2 ^ (7 * size)
  return (value, p + size, !identifier && value == 2 ^ (7 * size) - 1)

private def ebmlNodes (b : ByteArray) (start stop : Nat) : Except String (Array Node) := do
  if start > stop || stop > b.size then throw "Invalid EBML bounds"
  let mut pos := start
  let mut out := #[]
  for _ in [:stop - start + 1] do
    if pos < stop then
      let (id, p, _) ← vint b pos stop true
      let (size, payload, unknown) ← vint b p stop
      if unknown && id != 0x18538067 && id != 0x1F43B675 then
        throw "Unsupported unknown EBML size"
      let endPos := if unknown then stop else payload + size
      if endPos > stop then throw "Truncated EBML element"
      out := out.push { id, pos := payload, stop := endPos }
      pos := endPos
  if pos != stop then throw "Invalid EBML extent"
  return out

private def child (ns : Array Node) (id : Nat) : Except String Node :=
  match ns.find? (·.id == id) with
  | some n => .ok n
  | none => .error s!"Missing container element {id}"
private def nodeBytes (b : ByteArray) (n : Node) : ByteArray := b.extract n.pos n.stop
private def nodeUInt (b : ByteArray) (n : Node) : Except String Nat := do
  if n.stop <= n.pos || n.stop - n.pos > 8 then throw "Invalid EBML unsigned integer"
  return uint b n.pos (n.stop - n.pos)
private def optUInt (b : ByteArray) (ns : Array Node) (id fallback : Nat) : Except String Nat :=
  match ns.find? (·.id == id) with
  | some n => nodeUInt b n
  | none => .ok fallback

private def durationRatio (ns : Nat) : Nat × Nat := Id.run do
  if ns == 0 then return (1, 25)
  for (n, d) in (#[(1001, 24000), (1001, 30000), (1001, 60000), (1001, 120000),
      (1001, 48000), (1001, 15000), (1, 24), (1, 25), (1, 30), (1, 50), (1, 60),
      (1, 120), (1, 15), (1, 10), (1, 90), (1, 144), (1, 240)] : Array (Nat × Nat)) do
    if ns == 1000000000 * n / d || ns == (1000000000 * n + d / 2) / d then
      return (n, d)
  if ns == 1 then return (1, 1000000000)
  let mut loN := ns - 1
  let mut loD := 1000000000
  let mut hiN := ns + 1
  let mut hiD := 1000000000
  let mut p0 := 0
  let mut q0 := 1
  let mut p1 := 1
  let mut q1 := 0
  for _ in [:64] do
    if loD > 0 && hiD > 0 then
      let aLo := loN / loD
      let aHi := (hiN - 1) / hiD
      if aLo < aHi then
        let a := aLo + 1
        return ratio (a * p1 + p0) (a * q1 + q0)
      let nextP := aLo * p1 + p0
      let nextQ := aLo * q1 + q0
      p0 := p1; p1 := nextP
      q0 := q1; q1 := nextQ
      let nextLoN := hiD
      let nextLoD := hiN - aLo * hiD
      let nextHiN := loD
      let nextHiD := loN - aLo * loD
      loN := nextLoN; loD := nextLoD
      hiN := nextHiN; hiD := nextHiD
  return ratio ns 1000000000

private def bitmap (s : Stream) : ByteArray :=
  le 4 (40 + s.config.size) ++ le 4 s.width ++ le 4 s.height ++ le 2 1 ++ le 2 24 ++
  bytes "FFV1" ++ le 4 (s.width * s.height * 3) ++ zeros 16 ++ s.config

private def parseBitmap (b : ByteArray) : Except String (Nat × Nat × ByteArray) := do
  if b.size < 40 || uint b 0 4 true < 40 || uint b 0 4 true > b.size then
    throw "Invalid BITMAPINFOHEADER"
  if text b 16 4 != "FFV1" then throw "not FFV1"
  let w := uint b 4 4 true
  let rawH := uint b 8 4 true
  let h := if rawH >= 0x80000000 then 0x100000000 - rawH else rawH
  if w == 0 || h == 0 || w >= 0x80000000 || h >= 0x80000000 then
    throw "Invalid bitmap dimensions"
  return (w, h, b.extract 40 b.size)

private def readMkvBlock (b : ByteArray) (n : Node) (track : Nat) :
    Except String (Option ByteArray) := do
  let (t, p, _) ← vint b n.pos n.stop
  if n.stop < p + 3 then throw "Truncated Matroska block"
  if t != track then return none
  if uint b (p + 2) 1 &&& 6 != 0 then throw "Unsupported Matroska lacing"
  if p + 3 == n.stop then throw "Empty Matroska block"
  return some (b.extract (p + 3) n.stop)

def demuxMkv (b : ByteArray) : Except String Stream := do
  let top ← ebmlNodes b 0 b.size
  let hdr ← child top 0x1A45DFA3
  let _ ← ebmlNodes b hdr.pos hdr.stop
  if let some dt := (← ebmlNodes b hdr.pos hdr.stop).find? (·.id == 0x4282) then
    let dtStr := (text b dt.pos (dt.stop - dt.pos)).takeWhile (fun c => c != Char.ofNat 0) |>.toString
    if dtStr != "matroska" && dtStr != "webm" then throw "Unsupported EBML DocType"
  let seg ← child top 0x18538067
  let ns ← ebmlNodes b seg.pos seg.stop
  let tracks ← child ns 0x1654AE6B
  let entries ← ebmlNodes b tracks.pos tracks.stop
  let mut selected : Option (Stream × Nat) := none
  let mut hasAudioOrOtherVideo := false
  for entry in entries do
    if entry.id == 0xAE then
      let es ← ebmlNodes b entry.pos entry.stop
      let number ← optUInt b es 0xD7 0
      let typ ← optUInt b es 0x83 0
      let codec ← child es 0x86
      let codecName := text b codec.pos (codec.stop - codec.pos)
      if typ == 2 || typ == 17 then hasAudioOrOtherVideo := true
      if typ == 1 && codecName != "V_FFV1" && codecName != "V_MS/VFW/FOURCC" then
        hasAudioOrOtherVideo := true
      if typ == 1 && (codecName == "V_FFV1" || codecName == "V_MS/VFW/FOURCC") then
        let cp := (es.find? (·.id == 0x63A2)).map (nodeBytes b) |>.getD ByteArray.empty
        let mut config := cp
        let mut isFfv1 := true
        if codecName == "V_MS/VFW/FOURCC" then
          if cp.size < 40 then throw "Truncated Matroska bitmap header"
          if text cp 16 4 != "FFV1" then
            isFfv1 := false
            hasAudioOrOtherVideo := true
          else
            let (_, _, cfg) ← parseBitmap cp
            config := cfg
        if isFfv1 && !selected.isNone then hasAudioOrOtherVideo := true
        if isFfv1 && selected.isNone then
          if number == 0 then throw "Invalid Matroska track number"
          let video ← child es 0xE0
          let vs ← ebmlNodes b video.pos video.stop
          let width ← optUInt b vs 0xB0 0
          let height ← optUInt b vs 0xBA 0
          let dwOpt ← match vs.find? (·.id == 0x54B0) with
            | some n => some <$> nodeUInt b n
            | none => pure none
          let dhOpt ← match vs.find? (·.id == 0x54BA) with
            | some n => some <$> nodeUInt b n
            | none => pure none
          let unit ← optUInt b vs 0x54B2 0
          let (sn, sd) ← resolveMkvSar width height dwOpt dhOpt unit
          let duration ← optUInt b es 0x23E383 40000000
          if duration == 0 then throw "Invalid Matroska DefaultDuration"
          let (tn, td) := durationRatio duration
          let initStream : Stream := {
            width := width
            height := height
            timeNum := tn
            timeDen := td
            sarNum := sn
            sarDen := sd
            config := config
            packets := #[]
          }
          selected := some (initStream, number)
  let some (initial, track) := selected | throw "not FFV1"
  if hasAudioOrOtherVideo then throw "multi-stream container"
  let mut s := initial
  for cluster in ns do
    if cluster.id == 0x1F43B675 then
      let cs ← ebmlNodes b cluster.pos cluster.stop
      for block in cs do
        let mut blocks := #[block]
        if block.id == 0xA0 then
          blocks ← ebmlNodes b block.pos block.stop
        for item in blocks do
          if item.id == 0xA3 || item.id == 0xA1 then
            let packet ← readMkvBlock b item track
            if let some p := packet then s := { s with packets := s.packets.push p }
  validate s
  return s

private def ebml (id : Nat) (payload : ByteArray) : ByteArray :=
  let n := max 1 ((id.log2 + 8) / 8)
  be n id ++ be 8 (2 ^ 56 + payload.size) ++ payload
private def eu (id v : Nat) : ByteArray := ebml id (be (max 1 ((v.log2 + 8) / 8)) v)

def muxMkv (s : Stream) : Except String ByteArray := do
  validate s
  let header := ebml 0x1A45DFA3 (eu 0x4286 1 ++ eu 0x42F7 1 ++ eu 0x42F2 4 ++
    eu 0x42F3 8 ++ ebml 0x4282 (bytes "matroska") ++ eu 0x4287 4 ++ eu 0x4285 2)
  let info := ebml 0x1549A966 (eu 0x2AD7B1 1000000 ++
    ebml 0x4D80 (bytes "LeanAV") ++ ebml 0x5741 (bytes "LeanAV"))
  let dispFields :=
    match encodeMkvDisplay s.width s.height s.sarNum s.sarDen with
    | (none, none, some u) => eu 0x54B2 u
    | (some dw, some dh, some u) => eu 0x54B0 dw ++ eu 0x54BA dh ++ eu 0x54B2 u
    | _ => ByteArray.empty
  let video := ebml 0xE0 (eu 0xB0 s.width ++ eu 0xBA s.height ++ dispFields)
  let duration := (1000000000 * s.timeNum + s.timeDen / 2) / s.timeDen
  if duration == 0 then throw "Matroska frame duration below one nanosecond"
  let tracks := ebml 0x1654AE6B (ebml 0xAE (eu 0xD7 1 ++ eu 0x73C5 1 ++ eu 0x83 1 ++
    eu 0x9C 0 ++ ebml 0x86 (bytes "V_MS/VFW/FOURCC") ++
    eu 0x23E383 duration ++ video ++ ebml 0x63A2 (bitmap s)))
  let mut clusters := ByteArray.empty
  for i in [:s.packets.size] do
    let kfFlag := if packetIsKeyframe s i then 0x80 else 0x00
    let block := (be 1 0x81 ++ zeros 2 ++ be 1 kfFlag) ++ s.packets[i]!
    clusters := clusters ++ ebml 0x1F43B675
      (eu 0xE7 (i * s.timeNum * 1000 / s.timeDen) ++ ebml 0xA3 block)
  return header ++ ebml 0x18538067 (info ++ tracks ++ clusters)

private def four (s : String) : Nat := uint (bytes s) 0 4
private def boxes (b : ByteArray) (start stop : Nat) : Except String (Array Node) := do
  if start > stop || stop > b.size then throw "Invalid MOV bounds"
  let mut pos := start
  let mut out := #[]
  for _ in [:((stop - start) / 8 + 1)] do
    if pos < stop then
      if stop - pos < 8 then throw "Truncated MOV box"
      let short := uint b pos 4
      let hdr := if short == 1 then 16 else 8
      if stop - pos < hdr then throw "Truncated MOV extended box"
      let size := if short == 0 then stop - pos else if short == 1 then uint b (pos + 8) 8 else short
      if size < hdr || size > stop - pos then throw "Invalid MOV box size"
      out := out.push { id := uint b (pos + 4) 4, pos := pos + hdr, stop := pos + size }
      pos := pos + size
  if pos != stop then throw "Invalid MOV box extent"
  return out
private def descend (b : ByteArray) (ns : Array Node) (name : String) : Except String (Array Node) := do
  let n ← child ns (four name)
  boxes b n.pos n.stop
private def need (n : Node) (count : Nat) : Except String Unit :=
  if count > n.stop - n.pos then .error "Truncated container table" else .ok ()
private def table (b : ByteArray) (n : Node) (head stride : Nat) : Except String Nat := do
  need n head
  let count := uint b (n.pos + head - 4) 4
  if count > (n.stop - n.pos - head) / stride then throw "Truncated MOV table entries"
  return count

private def movTrack (b : ByteArray) (track : Node) (media : Array Node) : Except String (Option Stream) := do
  let ts ← boxes b track.pos track.stop
  let mdia ← descend b ts "mdia"
  let handler ← child mdia (four "hdlr")
  need handler 12
  if text b (handler.pos + 8) 4 != "vide" then return none
  let minf ← descend b mdia "minf"
  let stbl ← descend b minf "stbl"
  let stsd ← child stbl (four "stsd")
  need stsd 8
  let descriptions ← boxes b (stsd.pos + 8) stsd.stop
  if descriptions.size != uint b (stsd.pos + 4) 4 then throw "Invalid MOV stsd count"
  let some entry := descriptions.find? (·.id == four "FFV1") | return none
  need entry 78
  let width := uint b (entry.pos + 24) 2
  let height := uint b (entry.pos + 26) 2
  let extras ← boxes b (entry.pos + 78) entry.stop
  let config := (extras.find? (·.id == four "glbl")).map (nodeBytes b) |>.getD ByteArray.empty
  let mut sn := 0
  let mut sd := 1
  if let some pasp := extras.find? (·.id == four "pasp") then
    need pasp 8
    sn := uint b pasp.pos 4
    sd := uint b (pasp.pos + 4) 4
  let mdhd ← child mdia (four "mdhd")
  need mdhd 4
  let version := uint b mdhd.pos 1
  if version > 1 then throw "Invalid MOV mdhd version"
  need mdhd (if version == 1 then 32 else 20)
  let scale := uint b (mdhd.pos + if version == 1 then 20 else 12) 4
  if scale == 0 then throw "Invalid MOV media timescale"
  let stsz ← child stbl (four "stsz")
  need stsz 12
  let uniform := uint b (stsz.pos + 4) 4
  let count := uint b (stsz.pos + 8) 4
  if count > b.size then throw "MOV sample count exceeds file size"
  if uniform == 0 then need stsz (12 + 4 * count)
  let stts ← child stbl (four "stts")
  let nt ← table b stts 8 8
  let mut total := 0
  let mut delta := 0
  for i in [:nt] do
    let num := uint b (stts.pos + 8 + 8 * i) 4
    let d := uint b (stts.pos + 12 + 8 * i) 4
    if num == 0 || d == 0 then throw "Invalid MOV stts run"
    if delta != 0 && delta != d then throw "Unsupported variable frame duration"
    delta := d
    total := total + num
  if total != count then throw "MOV stts sample count mismatch"
  let (tn, td) := if count == 0 then (1, 25) else ratio delta scale
  let stsc ← child stbl (four "stsc")
  let nc ← table b stsc 8 12
  let offsets ← match stbl.find? (·.id == four "co64") with
    | some n => pure n
    | none => child stbl (four "stco")
  let stride := if offsets.id == four "co64" then 8 else 4
  let no ← table b offsets 8 stride
  let mut runs : Array (Nat × Nat) := #[]
  let mut descIndex := 0
  for d in [:descriptions.size] do
    if descriptions[d]!.id == four "FFV1" && descIndex == 0 then descIndex := d + 1
  let mut previous := 0
  for i in [:nc] do
    let p := stsc.pos + 8 + 12 * i
    let first := uint b p 4
    let num := uint b (p + 4) 4
    if first <= previous || first > no || num == 0 || uint b (p + 8) 4 != descIndex then
      throw "Invalid MOV stsc mapping"
    if i == 0 && first != 1 then throw "MOV stsc must start at chunk one"
    previous := first
    runs := runs.push (first, num)
  if count > 0 && (runs.isEmpty || no == 0) then throw "Missing MOV sample chunks"
  let mut ri := 0
  let mut sample := 0
  let mut packets := #[]
  for i in [:no] do
    if ri + 1 < runs.size && runs[ri + 1]!.1 <= i + 1 then ri := ri + 1
    if runs.isEmpty then throw "Empty MOV chunk mapping"
    let mut off := uint b (offsets.pos + 8 + stride * i) stride
    let num := runs[ri]!.2
    if num > count - sample then throw "MOV chunk sample count overflow"
    for _ in [:num] do
      let size := if uniform == 0 then uint b (stsz.pos + 12 + sample * 4) 4 else uniform
      if size == 0 then throw "Empty MOV sample"
      if !(media.any (fun n => off >= n.pos && off + size <= n.stop)) then
        throw "MOV sample outside mdat"
      let packet ← slice b off size
      packets := packets.push packet
      off := off + size
      sample := sample + 1
  if sample != count then throw "Incomplete MOV chunk mapping"
  let s : Stream := {
    width := width
    height := height
    timeNum := tn
    timeDen := td
    sarNum := sn
    sarDen := sd
    config := config
    packets := packets
  }
  validate s
  return some s

def demuxMov (b : ByteArray) : Except String Stream := do
  let top ← boxes b 0 b.size
  let moov ← descend b top "moov"
  let media := top.filter (·.id == four "mdat")
  let mut result := none
  let mut trakCount := 0
  for t in moov do
    if t.id == four "trak" then
      trakCount := trakCount + 1
      let s ← movTrack b t media
      if result.isNone then result := s
  let some s := result | throw "not FFV1"
  if trakCount > 1 then throw "multi-stream container"
  return s

private def box (name : String) (payload : ByteArray) : ByteArray :=
  be 4 (payload.size + 8) ++ bytes name ++ payload
private def fullBox (name : String) (payload : ByteArray) : ByteArray := box name (zeros 4 ++ payload)
private def matrix : ByteArray := be 4 65536 ++ zeros 12 ++ be 4 65536 ++ zeros 12 ++ be 4 0x40000000

def muxMov (s : Stream) : Except String ByteArray := do
  validate s
  let duration := s.packets.size * s.timeNum
  if duration > 0xFFFFFFFF then throw "MOV duration exceeds 32-bit limit"
  let ftyp := box "ftyp" (bytes "qt  " ++ be 4 512 ++ bytes "qt  ")
  let mut payload := ByteArray.empty
  let mut sizes := ByteArray.empty
  for p in s.packets do
    payload := payload ++ p
    sizes := sizes ++ be 4 p.size
  if payload.size > 0xFFFFFF00 then throw "MOV exceeds 32-bit mux limit"
  let sampleHeader := zeros 6 ++ be 2 1 ++ zeros 16 ++ be 2 s.width ++ be 2 s.height ++
    be 4 0x480000 ++ be 4 0x480000 ++ zeros 4 ++ be 2 1 ++ zeros 32 ++ be 2 24 ++ be 2 65535
  let pasp := if s.sarNum == 0 then ByteArray.empty else box "pasp" (be 4 s.sarNum ++ be 4 s.sarDen)
  let entry := box "FFV1" (sampleHeader ++ box "glbl" s.config ++ pasp)
  let stsd := fullBox "stsd" (be 4 1 ++ entry)
  let stts := fullBox "stts" (if s.packets.isEmpty then zeros 4 else
    be 4 1 ++ be 4 s.packets.size ++ be 4 s.timeNum)
  let mut syncIndices : Array Nat := #[]
  for i in [:s.packets.size] do
    if packetIsKeyframe s i then syncIndices := syncIndices.push (i + 1)
  let stss :=
    if syncIndices.size == s.packets.size then ByteArray.empty
    else
      let syncBody := syncIndices.foldl (fun acc idx => acc ++ be 4 idx) (be 4 syncIndices.size)
      fullBox "stss" syncBody
  let stsc := fullBox "stsc" (if s.packets.isEmpty then zeros 4 else
    be 4 1 ++ be 4 1 ++ be 4 s.packets.size ++ be 4 1)
  let stsz := fullBox "stsz" (zeros 4 ++ be 4 s.packets.size ++ sizes)
  let stco := fullBox "stco" (if s.packets.isEmpty then zeros 4 else be 4 1 ++ be 4 (ftyp.size + 8))
  let stbl := box "stbl" (stsd ++ stts ++ stss ++ stsc ++ stsz ++ stco)
  let dinf := box "dinf" (fullBox "dref" (be 4 1 ++ box "url " (be 4 1)))
  let minf := box "minf" (box "vmhd" (be 4 1 ++ zeros 8) ++ dinf ++ stbl)
  let mdhd := fullBox "mdhd" (zeros 8 ++ be 4 s.timeDen ++ be 4 duration ++ be 2 0x7FFF ++ zeros 2)
  let hdlr := fullBox "hdlr" (zeros 4 ++ bytes "vide" ++ zeros 12 ++ bytes "LeanAV" ++ zeros 1)
  let mdia := box "mdia" (mdhd ++ hdlr ++ minf)
  let tkhd := box "tkhd" (be 4 3 ++ zeros 8 ++ be 4 1 ++ zeros 4 ++ be 4 duration ++
    zeros 16 ++ matrix ++ be 4 (s.width * 65536) ++ be 4 (s.height * 65536))
  let mvhd := fullBox "mvhd" (zeros 8 ++ be 4 s.timeDen ++ be 4 duration ++ be 4 65536 ++
    be 2 256 ++ zeros 10 ++ matrix ++ zeros 24 ++ be 4 2)
  return ftyp ++ box "mdat" payload ++ box "moov" (mvhd ++ box "trak" (tkhd ++ mdia))

private def riffNodes (b : ByteArray) (start stop : Nat) : Except String (Array Node) := do
  if start > stop || stop > b.size then throw "Invalid RIFF bounds"
  let mut pos := start
  let mut out := #[]
  for _ in [:((stop - start) / 8 + 1)] do
    if pos < stop then
      if stop - pos < 8 then throw "Truncated RIFF chunk"
      let size := uint b (pos + 4) 4 true
      let endPos := pos + 8 + size
      if endPos > stop || endPos + size % 2 > stop then throw "Invalid RIFF chunk extent"
      out := out.push { id := uint b pos 4, pos := pos + 8, stop := endPos }
      pos := endPos + size % 2
  if pos != stop then throw "Invalid RIFF padding"
  return out
private def listNodes (b : ByteArray) (n : Node) : Except String (Array Node) := do
  need n 4
  riffNodes b (n.pos + 4) n.stop
private def isList (b : ByteArray) (name : String) (n : Node) : Bool :=
  n.id == four "LIST" && n.stop >= n.pos + 4 && text b n.pos 4 == name

private def aviPackets (fuel : Nat) (b : ByteArray) (ns : Array Node) (tag : String) :
    Except String (Array ByteArray) := do
  match fuel with
  | 0 => throw "AVI nesting limit exceeded"
  | fuel + 1 =>
    let mut out := #[]
    for n in ns do
      if n.id == four tag || n.id == four (tag.take 2 |>.toString.append "db") then
        if n.pos == n.stop then throw "Empty AVI video chunk"
        out := out.push (nodeBytes b n)
      else if n.id == four "LIST" then
        let cs ← listNodes b n
        let ps ← aviPackets fuel b cs tag
        out := out ++ ps
    return out

def demuxAvi (b : ByteArray) : Except String Stream := do
  if b.size < 12 || text b 0 4 != "RIFF" || text b 8 4 != "AVI " then
    throw "Invalid AVI signature"
  let endPos := uint b 4 4 true + 8
  if endPos != b.size then throw "Unsupported or truncated AVI RIFF extent"
  let top ← riffNodes b 12 endPos
  let some hdrl := top.find? (isList b "hdrl") | throw "Missing AVI hdrl"
  let hs ← listNodes b hdrl
  let mut index := 0
  let mut selected : Option (Stream × String × Nat) := none
  for n in hs do
    if isList b "strl" n then
      let cs ← listNodes b n
      let sh ← child cs (four "strh")
      need sh 56
      if text b sh.pos 4 == "vids" then
        let sf ← child cs (four "strf")
        need sf 40
        if text b (sf.pos + 16) 4 == "FFV1" && selected.isNone then
          let (width, height, config) ← parseBitmap (nodeBytes b sf)
          let tnRaw := uint b (sh.pos + 20) 4 true
          let tdRaw := uint b (sh.pos + 24) 4 true
          let (tn, td) := if tnRaw > 0 && tdRaw > 0 then ratio tnRaw tdRaw else (tnRaw, tdRaw)
          let count := uint b (sh.pos + 32) 4 true
          let mut sn := 0
          let mut sd := 1
          if let some vp := cs.find? (·.id == four "vprp") then
            need vp 36
            let darDen := uint b (vp.pos + 20) 2 true
            let darNum := uint b (vp.pos + 22) 2 true
            if darDen > 0 && darNum > 0 then
              let r := ratio (darNum * height) (darDen * width)
              sn := r.1
              sd := r.2
          if index >= 100 then throw "Unsupported AVI stream index"
          let tag := s!"{index / 10}{index % 10}dc"
          let initStream : Stream := {
            width := width
            height := height
            timeNum := tn
            timeDen := td
            sarNum := sn
            sarDen := sd
            config := config
            packets := #[]
          }
          selected := some (initStream, tag, count)
      index := index + 1
  let some (initial, tag, count) := selected | throw "not FFV1"
  if index > 1 then throw "multi-stream container"
  let mut packets := #[]
  let mut found := false
  for n in top do
    if isList b "movi" n then
      found := true
      let cs ← listNodes b n
      packets := packets ++ (← aviPackets 16 b cs tag)
  if !found then throw "Missing AVI movi"
  if packets.size != count then throw "AVI frame count mismatch"
  let s := { initial with packets := packets }
  validate s
  return s

private def chunk (name : String) (payload : ByteArray) : ByteArray :=
  bytes name ++ le 4 payload.size ++ payload ++ zeros (payload.size % 2)
private def riffList (name : String) (payload : ByteArray) : ByteArray := chunk "LIST" (bytes name ++ payload)

def muxAvi (s : Stream) : Except String ByteArray := do
  validate s
  let count := s.packets.size
  let largest := s.packets.foldl (fun n p => max n p.size) 0
  let (tnNorm, tdNorm) := ratio s.timeNum s.timeDen
  let avih := chunk "avih" (le 4 (1000000 * tnNorm / tdNorm) ++ zeros 8 ++ le 4 16 ++
    le 4 count ++ zeros 4 ++ le 4 1 ++ le 4 largest ++ le 4 s.width ++ le 4 s.height ++ zeros 16)
  let sh := chunk "strh" (bytes "vidsFFV1" ++ zeros 12 ++ le 4 tnNorm ++ le 4 tdNorm ++
    zeros 4 ++ le 4 count ++ le 4 largest ++ le 4 0xFFFFFFFF ++ zeros 8 ++ le 2 s.width ++ le 2 s.height)
  let vprpChunk ←
    if s.sarNum == 0 then pure ByteArray.empty
    else
      let (dn, dd) := ratio (s.width * s.sarNum) (s.height * s.sarDen)
      if dn > 65535 || dd > 65535 then throw "AVI display aspect ratio exceeds 16-bit limit"
      pure (chunk "vprp" (zeros 8 ++ le 4 (s.timeDen / s.timeNum) ++ le 4 s.width ++ le 4 s.height ++
        le 2 dd ++ le 2 dn ++ le 4 s.width ++ le 4 s.height ++ le 4 1 ++
        le 4 s.height ++ le 4 s.width ++ le 4 s.height ++ le 4 s.width ++ zeros 16))
  let hdrl := riffList "hdrl" (avih ++ riffList "strl" (sh ++ chunk "strf" (bitmap s) ++ vprpChunk))
  let mut movi := ByteArray.empty
  let mut idx := ByteArray.empty
  for i in [:s.packets.size] do
    let p := s.packets[i]!
    let kf := if packetIsKeyframe s i then 16 else 0
    idx := idx ++ bytes "00dc" ++ le 4 kf ++ le 4 (movi.size + 4) ++ le 4 p.size
    movi := movi ++ chunk "00dc" p
  let payload := bytes "AVI " ++ hdrl ++ riffList "movi" movi ++ chunk "idx1" idx
  if payload.size > 0xFFFFFFFF then throw "AVI exceeds RIFF size limit"
  return chunk "RIFF" payload

structure Y4MFrameSequence where
  width : Nat
  height : Nat
  timeNum : Nat := 1
  timeDen : Nat := 25
  sarNum : Nat := 0
  sarDen : Nat := 1
  pixelFormat : LeanAV.Ffv1.Ffv1PixelFormat := .yuv420p
  frames : Array ByteArray
  deriving Inhabited, DecidableEq

private def line (b : ByteArray) (start : Nat) : Except String (String × Nat) := do
  if start >= b.size then throw "Missing Y4M line"
  let mut stop := start
  for i in [start:min b.size (start + 4097)] do
    if stop == i && b[i]?.getD 0 != 10 then stop := i + 1
  if stop >= b.size || stop - start > 4096 || b[stop]?.getD 0 != 10 then
    throw "Truncated or oversized Y4M line"
  let raw := b.extract start stop
  let some s := String.fromUTF8? raw | throw "Invalid Y4M text"
  return (s, stop + 1)
private def parseNat (s : String) : Except String Nat :=
  match s.toNat? with
  | some n => .ok n
  | none => .error "Invalid Y4M integer"
private def parseRatio (s : String) : Except String (Nat × Nat) := do
  match s.splitOn ":" with
  | [a, b] => return (← parseNat a, ← parseNat b)
  | _ => throw "Invalid Y4M rational"

def parseY4M (b : ByteArray) : Except String Y4MFrameSequence := do
  let (header, start) ← line b 0
  let tokens := header.splitOn " "
  if tokens.head? != some "YUV4MPEG2" then throw "Invalid Y4M signature"
  let mut s : Y4MFrameSequence := { width := 0, height := 0, frames := #[] }
  for token in tokens.drop 1 do
    let value := (token.drop 1).toString
    if token.startsWith "W" then s := { s with width := ← parseNat value }
    else if token.startsWith "H" then s := { s with height := ← parseNat value }
    else if token.startsWith "F" then
      let (den, num) ← parseRatio value
      s := { s with timeNum := num, timeDen := den }
    else if token.startsWith "A" then
      let (num, den) ← parseRatio value
      s := { s with sarNum := num, sarDen := if num == 0 && den == 0 then 1 else den }
    else if token.startsWith "C" then
      if value == "mono" then s := { s with pixelFormat := .gray }
      else if value != "420" && value != "420jpeg" && value != "420mpeg2" && value != "420paldv" then
        throw "Unsupported Y4M pixel format"
    else if token.startsWith "I" && value != "p" && value != "?" then
      throw "Unsupported interlaced Y4M"
  if s.width > 65535 || s.height > 65535 || s.timeNum == 0 || s.timeDen == 0 || s.sarDen == 0 then
    throw "Invalid Y4M dimensions or rational"
  let some size := s.pixelFormat.frameByteSize s.width s.height | throw "Invalid Y4M frame size"
  let mut pos := start
  let mut frames := #[]
  for _ in [:b.size / (size + 6) + 1] do
    if pos < b.size then
      let (marker, next) ← line b pos
      if marker != "FRAME" && !marker.startsWith "FRAME " then throw "Invalid Y4M frame marker"
      let frame ← slice b next size
      frames := frames.push frame
      pos := next + size
  if pos != b.size then throw "Invalid Y4M trailing data"
  return { s with frames := frames }

def writeY4M (s : Y4MFrameSequence) : Except String ByteArray := do
  if s.pixelFormat != .yuv420p && s.pixelFormat != .gray then throw "Unsupported Y4M pixel format"
  if s.timeNum == 0 || s.timeDen == 0 || s.sarDen == 0 || s.width > 65535 || s.height > 65535 then
    throw "Invalid Y4M dimensions or rational"
  let some size := s.pixelFormat.frameByteSize s.width s.height | throw "Invalid Y4M frame size"
  let chroma := if s.pixelFormat == .gray then "Cmono" else "C420jpeg XYSCSS=420JPEG"
  let sarStr := if s.sarNum == 0 then "A0:0" else s!"A{s.sarNum}:{s.sarDen}"
  let mut out := bytes s!"YUV4MPEG2 W{s.width} H{s.height} F{s.timeDen}:{s.timeNum} Ip {sarStr} {chroma}\n"
  for f in s.frames do
    if f.size != size then throw "Y4M frame byte length mismatch"
    out := out ++ bytes "FRAME\n" ++ f
  return out

def demux (b : ByteArray) : Except String Stream :=
  if b.size >= 4 && uint b 0 4 == 0x1A45DFA3 then demuxMkv b
  else if b.size >= 4 && text b 0 4 == "RIFF" then demuxAvi b
  else if b.size >= 8 && (["ftyp", "moov", "mdat", "wide", "free", "skip"].contains (text b 4 4)) then demuxMov b
  else .error "Unrecognized FFV1 container"

def mux (format : String) (s : Stream) : Except String ByteArray :=
  let low := String.ofList <| format.toList.map (fun c =>
    if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c)
  if low == "mkv" || low == "matroska" then muxMkv s
  else if low == "mov" then muxMov s
  else if low == "avi" then muxAvi s
  else .error "Unsupported FFV1 container format"

end LeanAV.Ffv1Container
