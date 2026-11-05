import LeanAV.Spec

namespace LeanAV.Ffv1

private def crc32ByteStep : Nat → UInt32 → UInt32
  | 0, crc => crc
  | k + 1, crc =>
    let next := if crc &&& 0x80000000 != 0 then
      (crc <<< 1) ^^^ 0x04C11DB7 else crc <<< 1
    crc32ByteStep k next

private def crc32ListLoop : List UInt8 → UInt32 → UInt32
  | [], crc => crc
  | b :: bs, crc => crc32ListLoop bs (crc32ByteStep 8 (crc ^^^ (b.toUInt32 <<< 24)))

def crc32 (bytes : ByteArray) : UInt32 :=
  crc32ListLoop bytes.data.toList 0

def appendCrc (bytes : ByteArray) : ByteArray :=
  let crc := crc32 bytes
  (((bytes.push (crc >>> 24).toUInt8).push (crc >>> 16).toUInt8).push
    (crc >>> 8).toUInt8).push crc.toUInt8

private def defaultOnePass1Loop : Nat → Nat → Nat → Array Nat → Array Nat
  | 0, _, _, states => states
  | rem + 1, p, last, states =>
    let p8 := (p + 0x800000) / 0x1000000
    let next := max (last + 1) p8
    let states1 :=
      if 0 < last && last ≤ 255 && next ≤ 248 then
        states.set! last next
      else states
    let pNext := p + ((0x100000000 - p) * 0x0CCCCCCC + 0x80000000) / 0x100000000
    defaultOnePass1Loop rem pNext next states1

private def defaultOnePass2Loop : Nat → Nat → Array Nat → Array Nat
  | 0, _, states => states
  | rem + 1, i, states =>
    let states1 :=
      if states.getD i 0 == 0 then
        let probability := i * 0x1000000
        let updated := probability +
          ((0x100000000 - probability) * 0x0CCCCCCC + 0x80000000) / 0x100000000
        states.set! i (min 248 (max (i + 1) ((updated + 0x800000) / 0x1000000)))
      else states
    defaultOnePass2Loop rem (i + 1) states1

def defaultOneStates : Array Nat :=
  let s1 := defaultOnePass1Loop 128 0x80000000 0 (Array.replicate 256 0)
  defaultOnePass2Loop 241 8 s1

structure Transitions where
  one : Array Nat
  zero : Array Nat
  deriving Inhabited

def Transitions.fromOne (one : Array Nat) : Transitions :=
  let zero := Array.ofFn fun (i : Fin 256) =>
    if i.val == 0 then 0 else (256 - one.getD (256 - i.val) 0) % 256
  { one, zero }

def defaultTransitions : Transitions := Transitions.fromOne defaultOneStates

structure RangeEncoder where
  low : Nat := 0
  range : Nat := 0xFF00
  outstanding : Option Nat := none
  outstandingCount : Nat := 0
  output : ByteArray := ByteArray.empty
  transitions : Transitions := defaultTransitions
  deriving Inhabited

def RangeEncoder.renorm (initial : RangeEncoder) : RangeEncoder := Id.run do
  let mut r := initial
  for _ in [:2] do
    if r.range < 256 then
      match r.outstanding with
      | none => r := { r with outstanding := some (r.low / 256) }
      | some b =>
        if r.low ≤ 0xFF00 || r.low ≥ 0x10000 then
          let carry := r.low ≥ 0x10000
          let mut out := r.output.push (b + if carry then 1 else 0).toUInt8
          for _ in [:r.outstandingCount] do
            out := out.push (if carry then 0 else 255)
          let nextOutstanding := some ((r.low / 256) % 256)
          r := { r with output := out, outstandingCount := 0, outstanding := nextOutstanding }
        else
          r := { r with outstandingCount := r.outstandingCount + 1 }
      r := { r with low := (r.low % 256) * 256, range := r.range * 256 }
  return r

def RangeEncoder.putBit (r : RangeEncoder) (state : Nat) (bit : Bool) : RangeEncoder × Nat :=
  let part := r.range * state / 256
  let next := if bit then
    { r with low := r.low + r.range - part, range := part }
    else { r with range := r.range - part }
  (next.renorm, if bit then r.transitions.one[state]! else r.transitions.zero[state]!)

def RangeEncoder.putStateBit (r : RangeEncoder) (states : Array Nat) (index : Nat)
    (bit : Bool) : RangeEncoder × Array Nat :=
  let (r, state) := r.putBit states[index]! bit
  (r, states.set! index state)

def RangeEncoder.putSymbol (initial : RangeEncoder) (initialStates : Array Nat)
    (value : Int) (signed : Bool) : RangeEncoder × Array Nat := Id.run do
  let (r0, s0) := initial.putStateBit initialStates 0 (value == 0)
  if value == 0 then return (r0, s0)
  let mut r := r0
  let mut states := s0
  let a := value.natAbs
  let e := a.log2
  for i in [:e] do
    let next := r.putStateBit states (1 + min i 9) true
    r := next.1
    states := next.2
  let next := r.putStateBit states (1 + min e 9) false
  r := next.1
  states := next.2
  for j in [:e] do
    let i := e - 1 - j
    let next := r.putStateBit states (22 + min i 9) ((a / 2 ^ i) % 2 == 1)
    r := next.1
    states := next.2
  if signed then
    let next := r.putStateBit states (11 + min e 10) (value < 0)
    r := next.1
    states := next.2
  return (r, states)

def RangeEncoder.finish (initial : RangeEncoder) (sentinel : Bool) : ByteArray := Id.run do
  let mut r := initial
  if sentinel then
    r := { r with range := r.range - r.range * 129 / 256 }
    r := r.renorm
  r := { r with range := 255, low := r.low + 255 }
  r := r.renorm
  r := { r with range := 255 }
  return r.renorm.output

structure RangeDecoder where
  input : ByteArray
  position : Nat := 2
  low : Nat
  range : Nat := 0xFF00
  transitions : Transitions := defaultTransitions
  failed : Bool := false
  deriving Inhabited

def RangeDecoder.init (input : ByteArray) : RangeDecoder :=
  let low := input[0]?.getD 0 |>.toNat
  let low := low * 256 + (input[1]?.getD 0).toNat
  { input, low := min low 0xFF00, failed := input.size < 2 }

def RangeDecoder.refill (r : RangeDecoder) : RangeDecoder :=
  if r.range < 256 then
    let nextLow := r.low * 256 + (r.input[r.position]?.getD 0).toNat
    let nextFailed := r.failed || r.position > r.input.size + 1
    { r with range := r.range * 256, low := nextLow, position := r.position + 1, failed := nextFailed }
  else r

def RangeDecoder.getBit (r : RangeDecoder) (state : Nat) : Bool × Nat × RangeDecoder :=
  let part := r.range * state / 256
  let remaining := r.range - part
  if r.low < remaining then
    (false, r.transitions.zero[state]!, ({ r with range := remaining } : RangeDecoder).refill)
  else
    (true, r.transitions.one[state]!,
      ({ r with low := r.low - remaining, range := part } : RangeDecoder).refill)

def RangeDecoder.getStateBit (r : RangeDecoder) (states : Array Nat)
    (index : Nat) : Bool × Array Nat × RangeDecoder :=
  let (bit, state, r) := r.getBit states[index]!
  (bit, states.set! index state, r)

def RangeDecoder.getSymbol (initial : RangeDecoder) (initialStates : Array Nat)
    (signed : Bool) : Int × Array Nat × RangeDecoder := Id.run do
  let (zero, s0, r0) := initial.getStateBit initialStates 0
  if zero then return (0, s0, r0)
  let mut r := r0
  let mut states := s0
  let mut e := 0
  let mut stopped := false
  for _ in [:32] do
    if !stopped then
      let (bit, s, next) := r.getStateBit states (1 + min e 9)
      r := next
      states := s
      if bit then e := e + 1 else stopped := true
  if !stopped then return (0, states, { r with failed := true })
  let mut a : Nat := 1
  for j in [:e] do
    let i := e - 1 - j
    let (bit, s, next) := r.getStateBit states (22 + min i 9)
    r := next
    states := s
    a := a * 2 + if bit then 1 else 0
  if signed then
    let (negative, s, next) := r.getStateBit states (11 + min e 10)
    return (if negative then -(Int.ofNat a) else Int.ofNat a, s, next)
  return (Int.ofNat a, states, r)

structure QuantizationSet where
  tables : Array (Array Int)
  contextCount : Nat
  initialStates : Array (Array Nat) := #[]
  deriving Inhabited

structure Configuration where
  microVersion : Nat
  coder : Nat
  transitions : Transitions
  colorspace : Nat
  bits : Nat
  chroma : Bool
  horizontalShift : Nat
  verticalShift : Nat
  alpha : Bool
  horizontalSlices : Nat
  verticalSlices : Nat
  quantization : Array QuantizationSet
  errorCorrection : Nat
  intra : Nat
  deriving Inhabited

def Configuration.planeCount (cfg : Configuration) : Nat :=
  2 + if cfg.alpha then 1 else 0

def readQuantizationTable (initial : RangeDecoder) (scale : Nat) :
    Except String (Array Int × Nat × RangeDecoder) := do
  let mut decoder := initial
  let mut states := Array.replicate 32 128
  let mut table := Array.replicate 256 (0 : Int)
  let mut position := 0
  let mut value := 0
  for _ in [:128] do
    if position < 128 then
      let (encodedRun, nextStates, next) := decoder.getSymbol states false
      decoder := next
      states := nextStates
      let run := encodedRun.toNat + 1
      if decoder.failed || run > 128 - position then
        throw "Invalid FFV1 quantization run"
      for i in [position:position + run] do
        let entry := Int.ofNat (scale * value)
        table := table.set! i entry
        if i > 0 then table := table.set! (256 - i) (-entry)
      position := position + run
      value := value + 1
  table := table.set! 128 (-table[127]!)
  return (table, scale * (2 * value - 1), decoder)

def parseConfiguration (bytes : ByteArray) : Except String Configuration := do
  if bytes.size < 6 || bytes.size > 1048576 || crc32 bytes != 0 then
    throw "Invalid FFV1 configuration checksum or size"
  let mut decoder := RangeDecoder.init (bytes.extract 0 (bytes.size - 4))
  let mut states := Array.replicate 32 128
  let (version, s, d) := decoder.getSymbol states false
  states := s
  decoder := d
  if version != 3 then throw "Only FFV1 version 3 is supported"
  let (micro, s, d) := decoder.getSymbol states false
  states := s
  decoder := d
  let (coder, s, d) := decoder.getSymbol states false
  states := s
  decoder := d
  if coder > 2 then throw "Unsupported FFV1 entropy coder"
  let mut transitions := defaultOneStates
  if coder == 2 then
    for i in [1:256] do
      let (delta, s, d) := decoder.getSymbol states true
      states := s
      decoder := d
      let next := (Int.emod (Int.ofNat defaultOneStates[i]! + delta) 256).toNat
      if next == 0 || next == 256 then throw "Invalid FFV1 probability transition"
      transitions := transitions.set! i next
  let (colorspace, s, d) := decoder.getSymbol states false
  states := s
  decoder := d
  let (bits, s, d) := decoder.getSymbol states false
  states := s
  decoder := d
  let (chroma, s, d) := decoder.getStateBit states 0
  states := s
  decoder := d
  let (horizontalShift, s, d) := decoder.getSymbol states false
  states := s
  decoder := d
  let (verticalShift, s, d) := decoder.getSymbol states false
  states := s
  decoder := d
  let (alpha, s, d) := decoder.getStateBit states 0
  states := s
  decoder := d
  let (horizontalSlices, s, d) := decoder.getSymbol states false
  states := s
  decoder := d
  let (verticalSlices, s, d) := decoder.getSymbol states false
  states := s
  decoder := d
  let (quantizationCount, s, d) := decoder.getSymbol states false
  states := s
  decoder := d
  if colorspace > 1 || (bits != 0 && bits != 8) || alpha ||
      horizontalShift > 1 || verticalShift > 1 then
    throw "Unsupported FFV1 pixel format"
  if colorspace == 0 && chroma && (horizontalShift != 1 || verticalShift != 1) then
    throw "Only gray, yuv420p, and 8-bit RGB are supported"
  if horizontalSlices >= 1024 || verticalSlices >= 1024 ||
      (horizontalSlices + 1) * (verticalSlices + 1) > 1024 ||
      quantizationCount < 1 || quantizationCount > 8 then
    throw "Invalid FFV1 configuration dimensions"
  let mut quantization := #[]
  for _ in [:quantizationCount.toNat] do
    let mut tables := #[]
    let mut scale := 1
    for _ in [:5] do
      let (table, nextScale, next) ← readQuantizationTable decoder scale
      if nextScale > 65535 then throw "FFV1 context limit exceeded"
      tables := tables.push table
      scale := nextScale
      decoder := next
    quantization := quantization.push { tables, contextCount := (scale + 1) / 2 }
  for q in [:quantization.size] do
    let (coded, s, d) := decoder.getStateBit states 0
    states := s
    decoder := d
    let count := quantization[q]!.contextCount
    let mut initialStates := Array.replicate count (Array.replicate 32 128)
    if coded then
      let mut deltaStates := Array.replicate 32 (Array.replicate 32 128)
      for j in [:count] do
        let mut row := initialStates[j]!
        for k in [:32] do
          let predicted := if j > 0 then initialStates[j - 1]![k]! else 128
          let (delta, s, d) := decoder.getSymbol deltaStates[k]! true
          decoder := d
          deltaStates := deltaStates.set! k s
          let value := (Int.emod (Int.ofNat predicted + delta) 256).toNat
          if value == 0 || value == 256 then throw "Invalid FFV1 initial probability"
          row := row.set! k value
        initialStates := initialStates.set! j row
    quantization := quantization.set! q { quantization[q]! with initialStates }
  let (errorCorrection, s, d) := decoder.getSymbol states false
  states := s
  decoder := d
  let mut intra := 0
  if micro > 2 then
    let (value, _, d) := decoder.getSymbol states false
    intra := value.toNat
    decoder := d
  if decoder.failed || errorCorrection > 1 || intra > 1 then
    throw "Invalid FFV1 configuration tail"
  return {
    microVersion := micro.toNat
    coder := coder.toNat
    transitions := Transitions.fromOne transitions
    colorspace := colorspace.toNat
    bits := 8
    chroma
    horizontalShift := horizontalShift.toNat
    verticalShift := verticalShift.toNat
    alpha
    horizontalSlices := horizontalSlices.toNat + 1
    verticalSlices := verticalSlices.toNat + 1
    quantization
    errorCorrection := errorCorrection.toNat
    intra }

def version2OneStates : Array Nat :=
  #[0, 10, 10, 10, 10, 16, 16, 16, 28, 16, 16, 29, 42, 49, 20, 49,
    59, 25, 26, 26, 27, 31, 33, 33, 33, 34, 34, 37, 67, 38, 39, 39,
    40, 40, 41, 79, 43, 44, 45, 45, 48, 48, 64, 50, 51, 52, 88, 52,
    53, 74, 55, 57, 58, 58, 74, 60, 101, 61, 62, 84, 66, 66, 68, 69,
    87, 82, 71, 97, 73, 73, 82, 75, 111, 77, 94, 78, 87, 81, 83, 97,
    85, 83, 94, 86, 99, 89, 90, 99, 111, 92, 93, 134, 95, 98, 105, 98,
    105, 110, 102, 108, 102, 118, 103, 106, 106, 113, 109, 112, 114, 112, 116, 125,
    115, 116, 117, 117, 126, 119, 125, 121, 121, 123, 145, 124, 126, 131, 127, 129,
    165, 130, 132, 138, 133, 135, 145, 136, 137, 139, 146, 141, 143, 142, 144, 148,
    147, 155, 151, 149, 151, 150, 152, 157, 153, 154, 156, 168, 158, 162, 161, 160,
    172, 163, 169, 164, 166, 184, 167, 170, 177, 174, 171, 173, 182, 176, 180, 178,
    175, 189, 179, 181, 186, 183, 192, 185, 200, 187, 191, 188, 190, 197, 193, 196,
    197, 194, 195, 196, 198, 202, 199, 201, 210, 203, 207, 204, 205, 206, 208, 214,
    209, 211, 221, 212, 213, 215, 224, 216, 217, 218, 219, 220, 222, 228, 223, 225,
    226, 224, 227, 229, 240, 230, 231, 232, 233, 234, 235, 236, 238, 239, 237, 242,
    241, 243, 242, 244, 245, 246, 247, 248, 249, 250, 251, 252, 252, 253, 254, 255]

def version2Transitions : Transitions := Transitions.fromOne version2OneStates

def log2Run : Array Nat :=
  #[0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3,
    4, 4, 5, 5, 6, 6, 7, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    16, 17, 18, 19, 20, 21, 22, 23, 24]

def buildSymmetricQuantTable (runs : Array Nat) (scale : Nat) : Array Int := Id.run do
  let mut table := Array.replicate 256 (0 : Int)
  let mut pos := 0
  let mut val := 0
  for run in runs do
    for i in [pos:pos + run] do
      let entry := Int.ofNat (scale * val)
      table := table.set! i entry
      if i > 0 then table := table.set! (256 - i) (-entry)
    pos := pos + run
    val := val + 1
  table := table.set! 128 (-table[127]!)
  return table

def quant5Runs : Array Nat := #[1, 3, 124]
def quant11Runs : Array Nat := #[1, 1, 3, 7, 23, 93]

def defaultQuantizationSets : Array QuantizationSet :=
  let q0 : QuantizationSet := {
    tables := #[
      buildSymmetricQuantTable quant11Runs 1,
      buildSymmetricQuantTable quant11Runs 11,
      buildSymmetricQuantTable quant11Runs 121,
      Array.replicate 256 0,
      Array.replicate 256 0
    ]
    contextCount := (11 * 11 * 11 + 1) / 2
    initialStates := Array.replicate ((11 * 11 * 11 + 1) / 2) (Array.replicate 32 128)
  }
  let q1 : QuantizationSet := {
    tables := #[
      buildSymmetricQuantTable quant11Runs 1,
      buildSymmetricQuantTable quant11Runs 11,
      buildSymmetricQuantTable quant5Runs 121,
      buildSymmetricQuantTable quant5Runs 605,
      buildSymmetricQuantTable quant5Runs 3025
    ]
    contextCount := (11 * 11 * 5 * 5 * 5 + 1) / 2
    initialStates := Array.replicate ((11 * 11 * 5 * 5 * 5 + 1) / 2) (Array.replicate 32 128)
  }
  #[q0, q1]

def writeQuantizationTable (initial : RangeEncoder) (tbl : Array Int) : RangeEncoder := Id.run do
  let mut enc := initial
  let mut st := Array.replicate 32 128
  let mut last := 0
  for i in [1:128] do
    if tbl[i]! != tbl[i - 1]! then
      let (e, s) := enc.putSymbol st (Int.ofNat (i - last - 1)) false
      enc := e
      st := s
      last := i
  let (e, _) := enc.putSymbol st (Int.ofNat (128 - last - 1)) false
  return e

def encodeConfiguration (cfg : Configuration) : ByteArray := Id.run do
  let mut enc : RangeEncoder := {}
  let mut st := Array.replicate 32 128
  let (e, s) := enc.putSymbol st 3 false
  enc := e; st := s
  let (e, s) := enc.putSymbol st (Int.ofNat cfg.microVersion) false
  enc := e; st := s
  let (e, s) := enc.putSymbol st (Int.ofNat cfg.coder) false
  enc := e; st := s
  if cfg.coder == 2 then
    for i in [1:256] do
      let delta := Int.ofNat cfg.transitions.one[i]! - Int.ofNat defaultOneStates[i]!
      let (e, s) := enc.putSymbol st delta true
      enc := e; st := s
  let (e, s) := enc.putSymbol st (Int.ofNat cfg.colorspace) false
  enc := e; st := s
  let (e, s) := enc.putSymbol st (Int.ofNat cfg.bits) false
  enc := e; st := s
  let (e, s) := enc.putStateBit st 0 cfg.chroma
  enc := e; st := s
  let (e, s) := enc.putSymbol st (Int.ofNat cfg.horizontalShift) false
  enc := e; st := s
  let (e, s) := enc.putSymbol st (Int.ofNat cfg.verticalShift) false
  enc := e; st := s
  let (e, s) := enc.putStateBit st 0 cfg.alpha
  enc := e; st := s
  let (e, s) := enc.putSymbol st (Int.ofNat (cfg.horizontalSlices - 1)) false
  enc := e; st := s
  let (e, s) := enc.putSymbol st (Int.ofNat (cfg.verticalSlices - 1)) false
  enc := e; st := s
  let (e, s) := enc.putSymbol st (Int.ofNat cfg.quantization.size) false
  enc := e; st := s
  for qset in cfg.quantization do
    for tbl in qset.tables do
      enc := writeQuantizationTable enc tbl
  for _ in cfg.quantization do
    let (e, s) := enc.putStateBit st 0 false
    enc := e; st := s
  let (e, s) := enc.putSymbol st (Int.ofNat cfg.errorCorrection) false
  enc := e; st := s
  if cfg.microVersion > 2 then
    let (e, _) := enc.putSymbol st (Int.ofNat cfg.intra) false
    enc := e
  return appendCrc (enc.finish false)

structure GolombReader where
  input : ByteArray
  bitPos : Nat := 0
  deriving Inhabited

def GolombReader.getBit (r : GolombReader) : Nat × GolombReader :=
  let byteIdx := r.bitPos / 8
  let bitIdx := 7 - (r.bitPos % 8)
  let b := if byteIdx < r.input.size then ((r.input[byteIdx]!.toNat >>> bitIdx) &&& 1) else 0
  (b, { r with bitPos := r.bitPos + 1 })

def GolombReader.getBits (initial : GolombReader) (n : Nat) : Nat × GolombReader := Id.run do
  let mut r := initial
  let mut v := 0
  for _ in [:n] do
    let (b, next) := r.getBit
    r := next
    v := v * 2 + b
  return (v, r)

def GolombReader.getUrGolomb (initial : GolombReader) (k limit escLen : Nat) : Nat × GolombReader := Id.run do
  let mut r := initial
  for zeros in [:limit] do
    let (b, next) := r.getBit
    r := next
    if b == 1 then
      let (rem, next2) := if k > 0 then r.getBits k else (0, r)
      return ((zeros <<< k) + rem, next2)
  let (esc, next) := r.getBits escLen
  return (esc + limit - 1, next)

@[inline]
def srGolombMapToNat (i : Int) : Nat :=
  if i < 0 then ((-i).toNat * 2 - 1) else (i.toNat * 2)

@[inline]
def srGolombMapFromNat (v : Nat) : Int :=
  let half := Int.ofNat (v / 2)
  if v % 2 == 1 then -(half + 1) else half

def GolombReader.getSrGolomb (r : GolombReader) (k limit escLen : Nat) : Int × GolombReader :=
  let (v, next) := r.getUrGolomb k limit escLen
  (srGolombMapFromNat v, next)

structure GolombWriter where
  output : ByteArray := ByteArray.empty
  curByte : Nat := 0
  bitCount : Nat := 0
  deriving Inhabited

def GolombWriter.putBit (w : GolombWriter) (bit : Nat) : GolombWriter :=
  let nextByte := w.curByte * 2 + (bit &&& 1)
  if w.bitCount == 7 then
    { output := w.output.push nextByte.toUInt8, curByte := 0, bitCount := 0 }
  else
    { w with curByte := nextByte, bitCount := w.bitCount + 1 }

def GolombWriter.putBits (initial : GolombWriter) (n val : Nat) : GolombWriter := Id.run do
  let mut w := initial
  for j in [:n] do
    let shift := n - 1 - j
    w := w.putBit ((val >>> shift) &&& 1)
  return w

def GolombWriter.putUrGolomb (w : GolombWriter) (i k limit escLen : Nat) : GolombWriter :=
  let e := i >>> k
  if e < limit then
    w.putBits (e + k + 1) ((1 <<< k) + (i &&& ((1 <<< k) - 1)))
  else
    w.putBits (limit + escLen) (i - limit + 1)

def GolombWriter.putSrGolomb (w : GolombWriter) (i : Int) (k limit escLen : Nat) : GolombWriter :=
  w.putUrGolomb (srGolombMapToNat i) k limit escLen

def GolombWriter.flush (w : GolombWriter) : ByteArray :=
  if w.bitCount == 0 then w.output
  else w.output.push ((w.curByte <<< (8 - w.bitCount)) &&& 0xFF).toUInt8

structure VlcState where
  drift : Int := 0
  errorSum : Nat := 4
  bias : Int := 0
  count : Nat := 1
  deriving Inhabited, DecidableEq, Repr

@[inline]
def foldSigned (diff : Int) (bits : Nat) : Int :=
  let m := Int.ofNat (1 <<< bits)
  let half := Int.ofNat (1 <<< (bits - 1))
  let d := Int.emod diff m
  if d >= half then d - m else d

@[inline]
def asr1Int (x : Int) : Int :=
  Int.fdiv x 2

def VlcState.update (st : VlcState) (v : Int) : VlcState :=
  let err0 := st.errorSum + v.natAbs
  let drift0 := st.drift + v
  let (count1, drift1, err1) :=
    if st.count == 128 then (st.count / 2, asr1Int drift0, err0 / 2)
    else (st.count, drift0, err0)
  let count2 := count1 + 1
  let cInt := Int.ofNat count2
  let (bias2, drift2) :=
    if drift1 <= -cInt then
      (max (st.bias - 1) (-128), max (drift1 + cInt) (-cInt + 1))
    else if drift1 > 0 then
      (min (st.bias + 1) 127, min (drift1 - cInt) 0)
    else
      (st.bias, drift1)
  { drift := drift2, errorSum := err1, bias := bias2, count := count2 }

def VlcState.computeK (st : VlcState) : Nat := Id.run do
  let mut i := st.count
  let mut k := 0
  for _ in [:16] do
    if i < st.errorSum then
      k := k + 1
      i := i + i
  return k

def getVlcSymbol (r : GolombReader) (st : VlcState) (bits : Nat) : Int × VlcState × GolombReader :=
  let k := st.computeK
  let (v0, next) := r.getSrGolomb k 12 bits
  let v := if 2 * st.drift + Int.ofNat st.count < 0 then -v0 - 1 else v0
  let ret := foldSigned (v + st.bias) bits
  (ret, st.update v, next)

def putVlcSymbol (w : GolombWriter) (st : VlcState) (val : Int) (bits : Nat) : GolombWriter × VlcState :=
  let v := foldSigned (val - st.bias) bits
  let k := st.computeK
  let code := if 2 * st.drift + Int.ofNat st.count < 0 then -v - 1 else v
  let nextW := w.putSrGolomb code k 12 bits
  (nextW, st.update v)

@[inline]
def rctForward (r g b : Int) : Int × Int × Int :=
  let bRct := b - g
  let rRct := r - g
  let yRct := g + Int.fdiv (bRct + rRct) 4
  (yRct, bRct + 256, rRct + 256)

@[inline]
def rctInverse (yRct c1 c2 : Int) : Int × Int × Int :=
  let bRct := c1 - 256
  let rRct := c2 - 256
  let g := yRct - Int.fdiv (bRct + rRct) 4
  (rRct + g, g, bRct + g)

@[inline]
def medianPredInt (l t lt : Int) : Int :=
  max (min l t) (min (max l t) (l + t - lt))

@[inline]
def log2RunAt (idx : Nat) : Nat :=
  log2Run[min idx (log2Run.size - 1)]!

def decodeLine (coder : Nat) (rd0 : RangeDecoder) (gb0 : GolombReader) (w : Nat)
    (p1 p2 : Array Int) (qtbls : Array (Array Int))
    (ac0 : Array (Array Nat)) (vlc0 : Array VlcState)
    (runIdx0 bits : Nat) :
    Array Int × RangeDecoder × GolombReader × Array (Array Nat) × Array VlcState × Nat := Id.run do
  let mask := Int.ofNat ((1 <<< bits) - 1)
  let mut rd := rd0
  let mut gb := gb0
  let mut ac := ac0
  let mut vlc := vlc0
  let mut cur := Array.replicate w (0 : Int)
  let mut runCount : Int := 0
  let mut runMode : Nat := 0
  let mut runIndex : Nat := runIdx0
  let mut x : Nat := 0
  for _ in [:w] do
    if x < w then
      let t := p1[x]!
      let tt := p2[x]!
      let rt := if x + 1 < w then p1[x + 1]! else p1[w - 1]!
      let l0 := if x >= 1 then cur[x - 1]! else p1[0]!
      let lt0 := if x >= 1 then p1[x - 1]! else p2[0]!
      let ll := if x >= 2 then cur[x - 2]! else (if x == 1 then p1[0]! else 0)
      let d0 := (Int.emod (l0 - lt0) 256).toNat
      let d1 := (Int.emod (lt0 - t) 256).toNat
      let d2 := (Int.emod (t - rt) 256).toNat
      let d3 := (Int.emod (ll - l0) 256).toNat
      let d4 := (Int.emod (tt - t) 256).toNat
      let ctxSigned :=
        qtbls[0]![d0]! + qtbls[1]![d1]! + qtbls[2]![d2]! + qtbls[3]![d3]! + qtbls[4]![d4]!
      let negSign := ctxSigned < 0
      let ctx := min ctxSigned.natAbs (ac.size - 1)
      let mut diff : Int := 0
      if coder != 0 then
        let (d, s, nextRd) := rd.getSymbol ac[ctx]! true
        diff := d
        ac := ac.set! ctx s
        rd := nextRd
        let sample := Int.emod (medianPredInt l0 t lt0 + (if negSign then -diff else diff)) (mask + 1)
        cur := cur.set! x sample
        x := x + 1
      else
        if ctx == 0 && runMode == 0 then
          runMode := 1
        if runMode != 0 then
          if runCount == 0 && runMode == 1 then
            let (b, nextGb) := gb.getBit
            gb := nextGb
            if b == 1 then
              let rc := 1 <<< (log2RunAt runIndex)
              runCount := Int.ofNat rc
              if x + rc <= w && runIndex + 1 < log2Run.size then
                runIndex := runIndex + 1
            else
              let l2 := log2RunAt runIndex
              let (rc, nextGb2) := if l2 > 0 then gb.getBits l2 else (0, gb)
              gb := nextGb2
              runCount := Int.ofNat rc
              if runIndex > 0 then
                runIndex := runIndex - 1
              runMode := 2
          if l0 == lt0 then
            let steps := min (runCount - 1).toNat (w - x - 1)
            for _ in [:steps] do
              if runCount > 1 && x + 1 < w then
                cur := cur.set! x p1[x]!
                x := x + 1
                runCount := runCount - 1
          else
            let steps := min (runCount - 1).toNat (w - x - 1)
            for _ in [:steps] do
              if runCount > 1 && x + 1 < w then
                let li := if x >= 1 then cur[x - 1]! else p1[0]!
                let ti := p1[x]!
                let lti := if x >= 1 then p1[x - 1]! else p2[0]!
                cur := cur.set! x (Int.emod (medianPredInt li ti lti) (mask + 1))
                x := x + 1
                runCount := runCount - 1
          runCount := runCount - 1
          if runCount < 0 then
            runMode := 0
            runCount := 0
            let (d, stNext, nextGb3) := getVlcSymbol gb vlc[ctx]! bits
            vlc := vlc.set! ctx stNext
            gb := nextGb3
            diff := if d >= 0 then d + 1 else d
          else
            diff := 0
        else
          let (d, stNext, nextGb) := getVlcSymbol gb vlc[ctx]! bits
          vlc := vlc.set! ctx stNext
          gb := nextGb
          diff := d
        let tx := p1[x]!
        let lx := if x >= 1 then cur[x - 1]! else p1[0]!
        let ltx := if x >= 1 then p1[x - 1]! else p2[0]!
        let sample := Int.emod (medianPredInt lx tx ltx + (if negSign then -diff else diff)) (mask + 1)
        cur := cur.set! x sample
        x := x + 1
  return (cur, rd, gb, ac, vlc, runIndex)

def encodeLine (coder : Nat) (re0 : RangeEncoder) (pb0 : GolombWriter) (w : Nat)
    (cur p1 p2 : Array Int) (qtbls : Array (Array Int))
    (ac0 : Array (Array Nat)) (vlc0 : Array VlcState)
    (runIdx0 bits : Nat) :
    RangeEncoder × GolombWriter × Array (Array Nat) × Array VlcState × Nat := Id.run do
  let mut re := re0
  let mut pb := pb0
  let mut ac := ac0
  let mut vlc := vlc0
  let mut runIndex : Nat := runIdx0
  let mut runCount : Nat := 0
  let mut runMode : Nat := 0
  for x in [:w] do
    let t := p1[x]!
    let tt := p2[x]!
    let rt := if x + 1 < w then p1[x + 1]! else p1[w - 1]!
    let l := if x >= 1 then cur[x - 1]! else p1[0]!
    let lt := if x >= 1 then p1[x - 1]! else p2[0]!
    let ll := if x >= 2 then cur[x - 2]! else (if x == 1 then p1[0]! else 0)
    let d0 := (Int.emod (l - lt) 256).toNat
    let d1 := (Int.emod (lt - t) 256).toNat
    let d2 := (Int.emod (t - rt) 256).toNat
    let d3 := (Int.emod (ll - l) 256).toNat
    let d4 := (Int.emod (tt - t) 256).toNat
    let ctxSigned :=
      qtbls[0]![d0]! + qtbls[1]![d1]! + qtbls[2]![d2]! + qtbls[3]![d3]! + qtbls[4]![d4]!
    let diffRaw := cur[x]! - medianPredInt l t lt
    let diffSigned := if ctxSigned < 0 then -diffRaw else diffRaw
    let ctx := min ctxSigned.natAbs (ac.size - 1)
    let mut diff := foldSigned diffSigned bits
    if coder != 0 then
      let (nextRe, s) := re.putSymbol ac[ctx]! diff true
      re := nextRe
      ac := ac.set! ctx s
    else
      if ctx == 0 then
        runMode := 1
      if runMode != 0 then
        if diff != 0 then
          for _ in [:w + 1] do
            let step := 1 <<< (log2RunAt runIndex)
            if runCount >= step then
              runCount := runCount - step
              if runIndex + 1 < log2Run.size then
                runIndex := runIndex + 1
              pb := pb.putBits 1 1
          let l2 := log2RunAt runIndex
          pb := pb.putBits (1 + l2) runCount
          if runIndex > 0 then
            runIndex := runIndex - 1
          runCount := 0
          runMode := 0
          if diff > 0 then
            diff := diff - 1
        else
          runCount := runCount + 1
      if runMode == 0 then
        let (nextPb, stNext) := putVlcSymbol pb vlc[ctx]! diff bits
        pb := nextPb
        vlc := vlc.set! ctx stNext
  if coder == 0 && runMode != 0 then
    for _ in [:w + 1] do
      let step := 1 <<< (log2RunAt runIndex)
      if runCount >= step then
        runCount := runCount - step
        if runIndex + 1 < log2Run.size then
          runIndex := runIndex + 1
        pb := pb.putBits 1 1
    if runCount > 0 then
      pb := pb.putBits 1 1
  return (re, pb, ac, vlc, runIndex)

def decodePlane (coder : Nat) (rd0 : RangeDecoder) (gb0 : GolombReader) (w h : Nat)
    (qtbls : Array (Array Int)) (ac0 : Array (Array Nat)) (vlc0 : Array VlcState)
    (bits : Nat) :
    Array (Array Int) × RangeDecoder × GolombReader × Array (Array Nat) × Array VlcState := Id.run do
  let mut rd := rd0
  let mut gb := gb0
  let mut ac := ac0
  let mut vlc := vlc0
  let mut runIdx := 0
  let zeroRow := Array.replicate w (0 : Int)
  let mut rows : Array (Array Int) := Array.emptyWithCapacity h
  for y in [:h] do
    let p1 := if y >= 1 then rows[y - 1]! else zeroRow
    let p2 := if y >= 2 then rows[y - 2]! else zeroRow
    if w == 0 then
      rows := rows.push #[]
    else
      let (cur, nextRd, nextGb, nextAc, nextVlc, nextRun) :=
        decodeLine coder rd gb w p1 p2 qtbls ac vlc runIdx bits
      rows := rows.push cur
      rd := nextRd
      gb := nextGb
      ac := nextAc
      vlc := nextVlc
      runIdx := nextRun
  return (rows, rd, gb, ac, vlc)

def encodePlane (coder : Nat) (re0 : RangeEncoder) (pb0 : GolombWriter)
    (rows : Array (Array Int)) (qtbls : Array (Array Int))
    (ac0 : Array (Array Nat)) (vlc0 : Array VlcState) (bits : Nat) :
    RangeEncoder × GolombWriter × Array (Array Nat) × Array VlcState := Id.run do
  let h := rows.size
  let w := if h > 0 then rows[0]!.size else 0
  let mut re := re0
  let mut pb := pb0
  let mut ac := ac0
  let mut vlc := vlc0
  let mut runIdx := 0
  let zeroRow := Array.replicate w (0 : Int)
  for y in [:h] do
    let p1 := if y >= 1 then rows[y - 1]! else zeroRow
    let p2 := if y >= 2 then rows[y - 2]! else zeroRow
    if w > 0 then
      let (nextRe, nextPb, nextAc, nextVlc, nextRun) :=
        encodeLine coder re pb w rows[y]! p1 p2 qtbls ac vlc runIdx bits
      re := nextRe
      pb := nextPb
      ac := nextAc
      vlc := nextVlc
      runIdx := nextRun
  return (re, pb, ac, vlc)

inductive Ffv1PixelFormat where
  | yuv420p
  | gray
  | rgb24
  | bgr0
  deriving Repr, DecidableEq, Inhabited

def Ffv1PixelFormat.parse (s : String) : Option Ffv1PixelFormat :=
  if s == "yuv420p" then some .yuv420p
  else if s == "gray" || s == "gray8" then some .gray
  else if s == "rgb24" then some .rgb24
  else if s == "bgr0" then some .bgr0
  else none

def Ffv1PixelFormat.toString : Ffv1PixelFormat → String
  | .yuv420p => "yuv420p"
  | .gray => "gray"
  | .rgb24 => "rgb24"
  | .bgr0 => "bgr0"

def Ffv1PixelFormat.frameByteSize (fmt : Ffv1PixelFormat) (w h : Nat) : Option Nat :=
  if w == 0 || h == 0 then none
  else match fmt with
  | .yuv420p =>
    if w % 2 != 0 || h % 2 != 0 then none
    else some (w * h + 2 * ((w / 2) * (h / 2)))
  | .gray => some (w * h)
  | .rgb24 => some (w * h * 3)
  | .bgr0 => some (w * h * 4)

def convertBgr0ToRgb24 (bgr0 : ByteArray) : ByteArray := Id.run do
  let pxCount := bgr0.size / 4
  let mut out := ByteArray.emptyWithCapacity (pxCount * 3)
  for i in [:pxCount] do
    let base := i * 4
    let b := bgr0[base]!
    let g := bgr0[base + 1]!
    let r := bgr0[base + 2]!
    out := ((out.push r).push g).push b
  return out

def convertRgb24ToBgr0 (rgb24 : ByteArray) : ByteArray := Id.run do
  let pxCount := rgb24.size / 3
  let mut out := ByteArray.emptyWithCapacity (pxCount * 4)
  for i in [:pxCount] do
    let base := i * 3
    let r := rgb24[base]!
    let g := rgb24[base + 1]!
    let b := rgb24[base + 2]!
    out := (((out.push b).push g).push r).push 0
  return out

structure SliceStateEntry where
  sx : Nat
  sy : Nat
  sw : Nat
  sh : Nat
  acPlanes : Array (Array (Array Nat))
  vlcPlanes : Array (Array VlcState)
  deriving Inhabited

abbrev GopState := Array SliceStateEntry

def GopState.lookup (st : GopState) (sx sy sw sh : Nat) : Option SliceStateEntry :=
  st.find? (fun e => e.sx == sx && e.sy == sy && e.sw == sw && e.sh == sh)

def GopState.upsert (st : GopState) (entry : SliceStateEntry) : GopState :=
  match st.findIdx? (fun e => e.sx == entry.sx && e.sy == entry.sy && e.sw == entry.sw && e.sh == entry.sh) with
  | some idx => st.set! idx entry
  | none => st.push entry

def splitV3Slices (pkt : ByteArray) (ec : Nat) : Except String (Array ByteArray) := do
  let trailer := if ec != 0 then 8 else 3
  if pkt.size < trailer then
    throw "FFV1 packet shorter than slice trailer"
  let mut posEnd := pkt.size
  let mut revSlices : Array ByteArray := #[]
  for _ in [:1025] do
    if posEnd > 0 then
      if posEnd < trailer then
        throw "Truncated FFV1 slice trailer"
      let tOff := posEnd - trailer
      let b0 := pkt[tOff]!.toNat
      let b1 := pkt[tOff + 1]!.toNat
      let b2 := pkt[tOff + 2]!.toNat
      let bodySize := (b0 <<< 16) ||| (b1 <<< 8) ||| b2
      let fullSize := bodySize + trailer
      if bodySize < 2 || fullSize > posEnd then
        throw "Invalid FFV1 slice size in trailer"
      let sl := pkt.extract (posEnd - fullSize) posEnd
      if ec != 0 && crc32 sl != 0 then
        throw "FFV1 slice CRC-32 mismatch"
      revSlices := revSlices.push sl
      posEnd := posEnd - fullSize
  if posEnd != 0 || revSlices.isEmpty then
    throw "Malformed FFV1 slice partition"
  return revSlices.reverse

def Configuration.defaultDecodedPixFmt (cfg : Configuration) : Ffv1PixelFormat :=
  if cfg.colorspace == 1 then .bgr0
  else if cfg.chroma then .yuv420p
  else .gray

def decodeFrameV3 (cfg : Configuration) (width height : Nat) (pkt : ByteArray)
    (gop0 : GopState := #[]) (outPixFmt : Option Ffv1PixelFormat := none) :
    Except String (ByteArray × Bool × GopState) := do
  if width == 0 || height == 0 || width > 16384 || height > 16384 then
    throw "Invalid FFV1 frame dimensions"
  if cfg.colorspace == 0 && cfg.chroma && (width % 2 != 0 || height % 2 != 0) then
    throw "Odd dimensions for yuv420p FFV1 frame"
  let targetFmt := outPixFmt.getD cfg.defaultDecodedPixFmt
  if (cfg.colorspace == 1 && targetFmt != .bgr0 && targetFmt != .rgb24) ||
     (cfg.colorspace == 0 && cfg.chroma && targetFmt != .yuv420p) ||
     (cfg.colorspace == 0 && !cfg.chroma && targetFmt != .gray) then
    throw "Incompatible output pixel format for FFV1 stream"
  let slices ← splitV3Slices pkt cfg.errorCorrection
  let trailer := if cfg.errorCorrection != 0 then 8 else 3
  let planeCount := cfg.planeCount
  let mut gop := gop0
  let mut isKeyframe := true
  let cwTotal := if cfg.chroma then (width + (1 <<< cfg.horizontalShift) - 1) >>> cfg.horizontalShift else 0
  let chTotal := if cfg.chroma then (height + (1 <<< cfg.verticalShift) - 1) >>> cfg.verticalShift else 0
  let mut yBuf := if cfg.colorspace == 0 then Array.replicate (width * height) (0 : UInt8) else #[]
  let mut uBuf := if cfg.colorspace == 0 && cfg.chroma then Array.replicate (cwTotal * chTotal) (0 : UInt8) else #[]
  let mut vBuf := if cfg.colorspace == 0 && cfg.chroma then Array.replicate (cwTotal * chTotal) (0 : UInt8) else #[]
  let mut bgr0Buf := if cfg.colorspace == 1 then Array.replicate (width * height * 4) (0 : UInt8) else #[]

  for sIdx in [:slices.size] do
    let slFull := slices[sIdx]!
    let mut rd := RangeDecoder.init slFull
    if sIdx == 0 then
      let (kfBit, _, rdNext) := rd.getStateBit #[128] 0
      isKeyframe := kfBit
      rd := rdNext
      if !isKeyframe && cfg.intra != 0 then
        throw "Non-keyframe packet in intra-only FFV1 stream"
    if cfg.coder == 2 then
      rd := { rd with transitions := cfg.transitions }
    let mut stHdr := Array.replicate 32 128
    let (sxI, s1, r1) := rd.getSymbol stHdr false
    stHdr := s1; rd := r1
    let (syI, s2, r2) := rd.getSymbol stHdr false
    stHdr := s2; rd := r2
    let (swM1, s3, r3) := rd.getSymbol stHdr false
    stHdr := s3; rd := r3
    let (shM1, s4, r4) := rd.getSymbol stHdr false
    stHdr := s4; rd := r4
    let sx := sxI.toNat
    let sy := syI.toNat
    let sw := swM1.toNat + 1
    let sh := shM1.toNat + 1
    if sx + sw > cfg.horizontalSlices || sy + sh > cfg.verticalSlices then
      throw "FFV1 slice coordinates out of bounds"
    let mut qIndices : Array Nat := Array.emptyWithCapacity planeCount
    for _ in [:planeCount] do
      let (qiI, sn, rn) := rd.getSymbol stHdr false
      stHdr := sn; rd := rn
      let qi := qiI.toNat
      if qi >= cfg.quantization.size then
        throw "FFV1 quant_table_index out of bounds"
      qIndices := qIndices.push qi
    let (_, s5, r5) := rd.getSymbol stHdr false
    stHdr := s5; rd := r5
    let (_, s6, r6) := rd.getSymbol stHdr false
    stHdr := s6; rd := r6
    let (_, _, r7) := rd.getSymbol stHdr false
    rd := r7
    if rd.failed then
      throw "Malformed FFV1 slice header"

    let x0 := (width * sx) / cfg.horizontalSlices
    let y0 := (height * sy) / cfg.verticalSlices
    let sliceW := (width * (sx + sw)) / cfg.horizontalSlices - x0
    let sliceH := (height * (sy + sh)) / cfg.verticalSlices - y0
    if sliceW == 0 || sliceH == 0 then
      throw "Empty FFV1 slice geometry"

    let mut gb : GolombReader := { input := ByteArray.empty, bitPos := 0 }
    if cfg.coder == 0 then
      if cfg.microVersion > 1 then
        let (_, _, rSent) := rd.getStateBit #[129] 0
        rd := rSent
      let acByteCount := rd.position - 1
      let bodyEnd := slFull.size - trailer
      if acByteCount > bodyEnd then
        throw "FFV1 Golomb payload offset exceeds slice body"
      gb := { input := slFull.extract acByteCount bodyEnd, bitPos := 0 }

    let (acPlanes0, vlcPlanes0) ←
      if isKeyframe then
        let mut acP : Array (Array (Array Nat)) := #[]
        let mut vlcP : Array (Array VlcState) := #[]
        for pI in [:planeCount] do
          let qset := cfg.quantization[qIndices[pI]!]!
          acP := acP.push qset.initialStates
          vlcP := vlcP.push (Array.replicate qset.contextCount {})
        pure (acP, vlcP)
      else
        match gop.lookup sx sy sw sh with
        | some prev =>
          let mut okSizes := prev.acPlanes.size == planeCount && prev.vlcPlanes.size == planeCount
          for pI in [:planeCount] do
            let qset := cfg.quantization[qIndices[pI]!]!
            if okSizes then
              okSizes := prev.acPlanes[pI]!.size == qset.contextCount &&
                         prev.vlcPlanes[pI]!.size == qset.contextCount
          if !okSizes then
            throw "FFV1 inter-frame slice context count mismatch"
          pure (prev.acPlanes, prev.vlcPlanes)
        | none =>
          throw "Missing reference GOP slice state for FFV1 non-keyframe"

    let mut acPlanes := acPlanes0
    let mut vlcPlanes := vlcPlanes0

    if cfg.colorspace == 0 then
      let qt0 := cfg.quantization[qIndices[0]!]!.tables
      let (rowsY, rdY, gbY, acY, vlcY) :=
        decodePlane cfg.coder rd gb sliceW sliceH qt0 acPlanes[0]! vlcPlanes[0]! 8
      rd := rdY; gb := gbY
      acPlanes := acPlanes.set! 0 acY
      vlcPlanes := vlcPlanes.set! 0 vlcY
      for dy in [:sliceH] do
        let row := rowsY[dy]!
        let dstBase := (y0 + dy) * width + x0
        for dx in [:sliceW] do
          yBuf := yBuf.set! (dstBase + dx) row[dx]!.toNat.toUInt8
      if cfg.chroma then
        let cw := (sliceW + (1 <<< cfg.horizontalShift) - 1) >>> cfg.horizontalShift
        let ch := (sliceH + (1 <<< cfg.verticalShift) - 1) >>> cfg.verticalShift
        let cx := x0 >>> cfg.horizontalShift
        let cy := y0 >>> cfg.verticalShift
        let qt1 := cfg.quantization[qIndices[1]!]!.tables
        let (rowsU, rdU, gbU, acU, vlcU) :=
          decodePlane cfg.coder rd gb cw ch qt1 acPlanes[1]! vlcPlanes[1]! 8
        let (rowsV, rdV, gbV, acV, vlcV) :=
          decodePlane cfg.coder rdU gbU cw ch qt1 acU vlcU 8
        rd := rdV; gb := gbV
        acPlanes := acPlanes.set! 1 acV
        vlcPlanes := vlcPlanes.set! 1 vlcV
        for dy in [:ch] do
          let rowU := rowsU[dy]!
          let rowV := rowsV[dy]!
          let dstBase := (cy + dy) * cwTotal + cx
          for dx in [:cw] do
            uBuf := uBuf.set! (dstBase + dx) rowU[dx]!.toNat.toUInt8
            vBuf := vBuf.set! (dstBase + dx) rowV[dx]!.toNat.toUInt8
    else
      let nComp := 3
      let zeroLine := Array.replicate sliceW (0 : Int)
      let mut hist1 := Array.replicate nComp zeroLine
      let mut hist2 := Array.replicate nComp zeroLine
      let mut runIdx := 0
      for dy in [:sliceH] do
        let mut curComp : Array (Array Int) := Array.emptyWithCapacity nComp
        for comp in [:nComp] do
          let pIdx := (comp + 1) / 2
          let qt := cfg.quantization[qIndices[pIdx]!]!.tables
          let p1 := hist1[comp]!
          let p2 := hist2[comp]!
          let (cur, nextRd, nextGb, nextAc, nextVlc, nextRun) :=
            decodeLine cfg.coder rd gb sliceW p1 p2 qt acPlanes[pIdx]! vlcPlanes[pIdx]! runIdx 9
          rd := nextRd; gb := nextGb; runIdx := nextRun
          acPlanes := acPlanes.set! pIdx nextAc
          vlcPlanes := vlcPlanes.set! pIdx nextVlc
          hist2 := hist2.set! comp p1
          hist1 := hist1.set! comp cur
          curComp := curComp.push cur
        let c0 := curComp[0]!
        let c1 := curComp[1]!
        let c2 := curComp[2]!
        for dx in [:sliceW] do
          let (rRec, gRec, bRec) := rctInverse c0[dx]! c1[dx]! c2[dx]!
          let bByte := (Int.emod bRec 256).toNat.toUInt8
          let gByte := (Int.emod gRec 256).toNat.toUInt8
          let rByte := (Int.emod rRec 256).toNat.toUInt8
          let pxOff := ((y0 + dy) * width + (x0 + dx)) * 4
          bgr0Buf := bgr0Buf.set! pxOff bByte
          bgr0Buf := bgr0Buf.set! (pxOff + 1) gByte
          bgr0Buf := bgr0Buf.set! (pxOff + 2) rByte
          bgr0Buf := bgr0Buf.set! (pxOff + 3) 0

    if rd.failed then
      throw "FFV1 range decoder error in slice payload"
    gop := gop.upsert { sx, sy, sw, sh, acPlanes, vlcPlanes }

  let rawOut :=
    if cfg.colorspace == 0 then
      if cfg.chroma then ByteArray.mk (yBuf ++ uBuf ++ vBuf)
      else ByteArray.mk yBuf
    else
      let bgr0 := ByteArray.mk bgr0Buf
      if targetFmt == .rgb24 then convertBgr0ToRgb24 bgr0 else bgr0
  return (rawOut, isKeyframe, gop)

def sliceGridForCount : Nat → Option (Nat × Nat)
  | 1 => some (1, 1)
  | 4 => some (2, 2)
  | 6 => some (3, 2)
  | 9 => some (3, 3)
  | 12 => some (4, 3)
  | 15 => some (5, 3)
  | 16 => some (4, 4)
  | 20 => some (5, 4)
  | 24 => some (6, 4)
  | 25 => some (5, 5)
  | 28 => some (7, 4)
  | 30 => some (6, 5)
  | 35 => some (7, 5)
  | 36 => some (6, 6)
  | 40 => some (8, 5)
  | 42 => some (7, 6)
  | 45 => some (9, 5)
  | 48 => some (8, 6)
  | 49 => some (7, 7)
  | 54 => some (9, 6)
  | 56 => some (8, 7)
  | 60 => some (10, 6)
  | 63 => some (9, 7)
  | 64 => some (8, 8)
  | _ => none

def parseCoderOption (s : String) : Option Nat :=
  let low := String.ofList <| s.toList.map (fun c =>
    if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c)
  if low == "0" || low == "rice" then some 0
  else if low == "-2" || low == "range_def" then some 1
  else if low == "1" || low == "ac" || low == "2" || low == "range_tab" then some 2
  else none

def makeEncoderConfiguration (pixFmt : Ffv1PixelFormat) (coder : Nat := 2)
    (numSlices : Nat := 4) (ec : Nat := 1) (gopSize : Nat := 12) :
    Except String Configuration := do
  if coder > 2 then
    throw "Invalid FFV1 coder code"
  if ec > 1 then
    throw "Invalid FFV1 slicecrc mode"
  let (nh, nv) ← match sliceGridForCount numSlices with
    | some p => pure p
    | none => throw s!"Unsupported FFV1 slice count: {numSlices}"
  let (cs, chroma, lh, lv) := match pixFmt with
    | .yuv420p => (0, true, 1, 1)
    | .gray => (0, false, 0, 0)
    | .rgb24 | .bgr0 => (1, true, 0, 0)
  return {
    microVersion := 4
    coder
    transitions := if coder == 2 then version2Transitions else defaultTransitions
    colorspace := cs
    bits := 8
    chroma
    horizontalShift := lh
    verticalShift := lv
    alpha := false
    horizontalSlices := nh
    verticalSlices := nv
    quantization := defaultQuantizationSets
    errorCorrection := ec
    intra := if gopSize == 1 then 1 else 0
  }

def encodeFrameV3 (cfg : Configuration) (width height : Nat) (pixFmt : Ffv1PixelFormat)
    (rawFrame : ByteArray) (ctxModel : Nat := 0) (isKeyframe : Bool := true)
    (gop0 : GopState := #[]) : Except String (ByteArray × GopState) := do
  if width == 0 || height == 0 || width > 16384 || height > 16384 then
    throw "Invalid FFV1 frame dimensions"
  if width < cfg.horizontalSlices || height < cfg.verticalSlices then
    throw "Frame dimensions smaller than FFV1 slice grid"
  if ctxModel >= cfg.quantization.size then
    throw "Invalid FFV1 context model index"
  let expectedBytes ← match pixFmt.frameByteSize width height with
    | some sz => pure sz
    | none => throw "Invalid dimensions for pixel format"
  if rawFrame.size != expectedBytes then
    throw "Raw frame byte length mismatch"
  if !isKeyframe && cfg.intra != 0 then
    throw "Cannot emit inter-frame in intra-only FFV1 configuration"

  let planeCount := cfg.planeCount
  let qset := cfg.quantization[ctxModel]!
  let qtbls := qset.tables
  let cwTotal := if cfg.chroma then (width + (1 <<< cfg.horizontalShift) - 1) >>> cfg.horizontalShift else 0
  let chTotal := if cfg.chroma then (height + (1 <<< cfg.verticalShift) - 1) >>> cfg.verticalShift else 0
  let yOff := 0
  let uOff := width * height
  let vOff := uOff + cwTotal * chTotal
  let mut outPkt := ByteArray.empty
  let mut gop := gop0

  for sy in [:cfg.verticalSlices] do
    for sx in [:cfg.horizontalSlices] do
      let sIdx := sy * cfg.horizontalSlices + sx
      let x0 := (width * sx) / cfg.horizontalSlices
      let y0 := (height * sy) / cfg.verticalSlices
      let swPx := (width * (sx + 1)) / cfg.horizontalSlices - x0
      let shPx := (height * (sy + 1)) / cfg.verticalSlices - y0
      let mut re : RangeEncoder := {}
      if sIdx == 0 then
        let (reNext, _) := re.putStateBit #[128] 0 isKeyframe
        re := reNext
      if cfg.coder == 2 then
        re := { re with transitions := cfg.transitions }
      let mut stHdr := Array.replicate 32 128
      let (r1, s1) := re.putSymbol stHdr (Int.ofNat sx) false
      re := r1; stHdr := s1
      let (r2, s2) := re.putSymbol stHdr (Int.ofNat sy) false
      re := r2; stHdr := s2
      let (r3, s3) := re.putSymbol stHdr 0 false
      re := r3; stHdr := s3
      let (r4, s4) := re.putSymbol stHdr 0 false
      re := r4; stHdr := s4
      for _ in [:planeCount] do
        let (rn, sn) := re.putSymbol stHdr (Int.ofNat ctxModel) false
        re := rn; stHdr := sn
      let (r5, s5) := re.putSymbol stHdr 3 false
      re := r5; stHdr := s5
      let (r6, s6) := re.putSymbol stHdr 0 false
      re := r6; stHdr := s6
      let (r7, _) := re.putSymbol stHdr 1 false
      re := r7

      let hdrBytes := if cfg.coder == 0 then re.finish true else ByteArray.empty
      let mut pb : GolombWriter := {}

      let (acPlanes0, vlcPlanes0) ←
        if isKeyframe then
          pure (
            Array.replicate planeCount qset.initialStates,
            Array.replicate planeCount (Array.replicate qset.contextCount {})
          )
        else
          match gop.lookup sx sy 1 1 with
          | some prev => pure (prev.acPlanes, prev.vlcPlanes)
          | none => throw "Missing reference GOP slice state for FFV1 inter-frame encode"

      let mut acPlanes := acPlanes0
      let mut vlcPlanes := vlcPlanes0

      if cfg.colorspace == 0 then
        let mut subY : Array (Array Int) := Array.emptyWithCapacity shPx
        for dy in [:shPx] do
          let mut row : Array Int := Array.emptyWithCapacity swPx
          let srcBase := yOff + (y0 + dy) * width + x0
          for dx in [:swPx] do
            row := row.push (Int.ofNat rawFrame[srcBase + dx]!.toNat)
          subY := subY.push row
        let (reY, pbY, acY, vlcY) :=
          encodePlane cfg.coder re pb subY qtbls acPlanes[0]! vlcPlanes[0]! 8
        re := reY; pb := pbY
        acPlanes := acPlanes.set! 0 acY
        vlcPlanes := vlcPlanes.set! 0 vlcY
        if cfg.chroma then
          let cw := (swPx + (1 <<< cfg.horizontalShift) - 1) >>> cfg.horizontalShift
          let ch := (shPx + (1 <<< cfg.verticalShift) - 1) >>> cfg.verticalShift
          let cx := x0 >>> cfg.horizontalShift
          let cy := y0 >>> cfg.verticalShift
          let mut subU : Array (Array Int) := Array.emptyWithCapacity ch
          let mut subV : Array (Array Int) := Array.emptyWithCapacity ch
          for dy in [:ch] do
            let mut rowU : Array Int := Array.emptyWithCapacity cw
            let mut rowV : Array Int := Array.emptyWithCapacity cw
            let srcU := uOff + (cy + dy) * cwTotal + cx
            let srcV := vOff + (cy + dy) * cwTotal + cx
            for dx in [:cw] do
              rowU := rowU.push (Int.ofNat rawFrame[srcU + dx]!.toNat)
              rowV := rowV.push (Int.ofNat rawFrame[srcV + dx]!.toNat)
            subU := subU.push rowU
            subV := subV.push rowV
          let (reU, pbU, acU, vlcU) :=
            encodePlane cfg.coder re pb subU qtbls acPlanes[1]! vlcPlanes[1]! 8
          let (reV, pbV, acV, vlcV) :=
            encodePlane cfg.coder reU pbU subV qtbls acU vlcU 8
          re := reV; pb := pbV
          acPlanes := acPlanes.set! 1 acV
          vlcPlanes := vlcPlanes.set! 1 vlcV
      else
        let nComp := 3
        let zeroLine := Array.replicate swPx (0 : Int)
        let mut hist1 := Array.replicate nComp zeroLine
        let mut hist2 := Array.replicate nComp zeroLine
        let mut runIdx := 0
        for dy in [:shPx] do
          let mut c0 : Array Int := Array.emptyWithCapacity swPx
          let mut c1 : Array Int := Array.emptyWithCapacity swPx
          let mut c2 : Array Int := Array.emptyWithCapacity swPx
          for dx in [:swPx] do
            let pxIdx := (y0 + dy) * width + (x0 + dx)
            let (rv, gv, bv) :=
              if pixFmt == .rgb24 then
                let base := pxIdx * 3
                (Int.ofNat rawFrame[base]!.toNat,
                 Int.ofNat rawFrame[base + 1]!.toNat,
                 Int.ofNat rawFrame[base + 2]!.toNat)
              else
                let base := pxIdx * 4
                (Int.ofNat rawFrame[base + 2]!.toNat,
                 Int.ofNat rawFrame[base + 1]!.toNat,
                 Int.ofNat rawFrame[base]!.toNat)
            let (yRct, cbRct, crRct) := rctForward rv gv bv
            c0 := c0.push yRct
            c1 := c1.push cbRct
            c2 := c2.push crRct
          let comps := #[c0, c1, c2]
          for comp in [:nComp] do
            let pIdx := (comp + 1) / 2
            let p1 := hist1[comp]!
            let p2 := hist2[comp]!
            let cur := comps[comp]!
            let (nextRe, nextPb, nextAc, nextVlc, nextRun) :=
              encodeLine cfg.coder re pb swPx cur p1 p2 qtbls acPlanes[pIdx]! vlcPlanes[pIdx]! runIdx 9
            re := nextRe; pb := nextPb; runIdx := nextRun
            acPlanes := acPlanes.set! pIdx nextAc
            vlcPlanes := vlcPlanes.set! pIdx nextVlc
            hist2 := hist2.set! comp p1
            hist1 := hist1.set! comp cur

      let body := if cfg.coder != 0 then re.finish true else hdrBytes ++ pb.flush
      let sz := body.size
      let sz3 := (((ByteArray.empty.push ((sz >>> 16) &&& 0xFF).toUInt8).push
        ((sz >>> 8) &&& 0xFF).toUInt8).push (sz &&& 0xFF).toUInt8)
      let slOut :=
        if cfg.errorCorrection != 0 then
          appendCrc ((body ++ sz3).push 0)
        else
          body ++ sz3
      outPkt := outPkt ++ slOut
      gop := gop.upsert { sx, sy, sw := 1, sh := 1, acPlanes, vlcPlanes }

  return (outPkt, gop)

end LeanAV.Ffv1
