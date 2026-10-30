import LeanAV.Spec

namespace LeanAV.Md5

open LeanAV.Spec

@[inline]
private def rotl32 (x : UInt32) (n : UInt32) : UInt32 :=
  (x <<< n) ||| (x >>> ((32 : UInt32) - n))

@[inline]
private def byteAtOrZero (ba : ByteArray) (i : Nat) : UInt8 :=
  ba.data.getD i 0

@[inline]
private def readUInt32LE (ba : ByteArray) (off : Nat) : UInt32 :=
  (byteAtOrZero ba off).toUInt32 |||
  ((byteAtOrZero ba (off + 1)).toUInt32 <<< 8) |||
  ((byteAtOrZero ba (off + 2)).toUInt32 <<< 16) |||
  ((byteAtOrZero ba (off + 3)).toUInt32 <<< 24)

private def md5Shifts : Array UInt32 := #[
  7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22,
  5,  9, 14, 20, 5,  9, 14, 20, 5,  9, 14, 20, 5,  9, 14, 20,
  4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23,
  6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21
]

private def md5Table : Array UInt32 := #[
  0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee,
  0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
  0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be,
  0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
  0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa,
  0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
  0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed,
  0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
  0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c,
  0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
  0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05,
  0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
  0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039,
  0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
  0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1,
  0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391
]

structure Md5State where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  deriving Repr, DecidableEq, Inhabited

def md5InitState : Md5State :=
  { a := 0x67452301, b := 0xefcdab89, c := 0x98badcfe, d := 0x10325476 }

private def compressRoundStep (buf : ByteArray) (blockOff : Nat) (i : Nat)
    (a b c d : UInt32) : UInt32 × UInt32 × UInt32 × UInt32 :=
  let (f, g) : UInt32 × Nat :=
    if i < 16 then
      ((b &&& c) ||| ((~~~b) &&& d), i)
    else if i < 32 then
      ((d &&& b) ||| ((~~~d) &&& c), (5 * i + 1) % 16)
    else if i < 48 then
      (b ^^^ c ^^^ d, (3 * i + 5) % 16)
    else
      (c ^^^ (b ||| (~~~d)), (7 * i) % 16)
  let m := readUInt32LE buf (blockOff + 4 * g)
  let k := md5Table.getD i 0
  let s := md5Shifts.getD i 0
  let sum := f + a + k + m
  (d, b + rotl32 sum s, b, c)

private def compressRoundLoop (buf : ByteArray) (blockOff : Nat) :
    Nat → Nat → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 × UInt32 × UInt32 × UInt32
  | 0, _, a, b, c, d => (a, b, c, d)
  | rem + 1, i, a, b, c, d =>
    let (a', b', c', d') := compressRoundStep buf blockOff i a b c d
    compressRoundLoop buf blockOff rem (i + 1) a' b' c' d'

private def compressBlock (st : Md5State) (buf : ByteArray) (blockOff : Nat) : Md5State :=
  let (a, b, c, d) := compressRoundLoop buf blockOff 64 0 st.a st.b st.c st.d
  { a := st.a + a, b := st.b + b, c := st.c + c, d := st.d + d }

private def padMessage (msg : ByteArray) : ByteArray :=
  let bitLen : UInt64 := msg.data.size.toUInt64 * 8
  let rem := (msg.data.size + 1) % 64
  let zeros := if rem <= 56 then 56 - rem else 120 - rem
  let lenArr : Array UInt8 := #[
    (bitLen &&& 0xff).toUInt8,
    ((bitLen >>> 8) &&& 0xff).toUInt8,
    ((bitLen >>> 16) &&& 0xff).toUInt8,
    ((bitLen >>> 24) &&& 0xff).toUInt8,
    ((bitLen >>> 32) &&& 0xff).toUInt8,
    ((bitLen >>> 40) &&& 0xff).toUInt8,
    ((bitLen >>> 48) &&& 0xff).toUInt8,
    ((bitLen >>> 56) &&& 0xff).toUInt8
  ]
  { data := (msg.data.push 0x80) ++ Array.replicate zeros 0 ++ lenArr }

@[inline]
def packDigest16 (st : Md5State) : ByteArray :=
  { data := #[
    (st.a &&& 0xff).toUInt8,
    ((st.a >>> 8) &&& 0xff).toUInt8,
    ((st.a >>> 16) &&& 0xff).toUInt8,
    ((st.a >>> 24) &&& 0xff).toUInt8,
    (st.b &&& 0xff).toUInt8,
    ((st.b >>> 8) &&& 0xff).toUInt8,
    ((st.b >>> 16) &&& 0xff).toUInt8,
    ((st.b >>> 24) &&& 0xff).toUInt8,
    (st.c &&& 0xff).toUInt8,
    ((st.c >>> 8) &&& 0xff).toUInt8,
    ((st.c >>> 16) &&& 0xff).toUInt8,
    ((st.c >>> 24) &&& 0xff).toUInt8,
    (st.d &&& 0xff).toUInt8,
    ((st.d >>> 8) &&& 0xff).toUInt8,
    ((st.d >>> 16) &&& 0xff).toUInt8,
    ((st.d >>> 24) &&& 0xff).toUInt8
  ] }

private def compressBlocksLoop (padded : ByteArray) : Nat → Nat → Md5State → Md5State
  | 0, _, st => st
  | rem + 1, blk, st =>
    compressBlocksLoop padded rem (blk + 1) (compressBlock st padded (blk * 64))

private def md5CoreState (bytes : ByteArray) : Md5State :=
  let padded := padMessage bytes
  compressBlocksLoop padded (padded.data.size / 64) 0 md5InitState

def md5 (bytes : ByteArray) : ByteArray :=
  packDigest16 (md5CoreState bytes)

@[inline]
private def hexNibString (n : UInt8) : String :=
  match (n &&& 0x0f).toNat with
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3"
  | 4 => "4" | 5 => "5" | 6 => "6" | 7 => "7"
  | 8 => "8" | 9 => "9" | 10 => "a" | 11 => "b"
  | 12 => "c" | 13 => "d" | 14 => "e" | _ => "f"

private def hexBytesList : List UInt8 → String
  | [] => ""
  | b :: bs => hexNibString (b >>> 4) ++ hexNibString b ++ hexBytesList bs

def bytesToLowerHex (digest : ByteArray) : String :=
  hexBytesList digest.data.toList

def md5Hex (bytes : ByteArray) : String :=
  bytesToLowerHex (md5 bytes)

def formatMd5Muxer (bytes : ByteArray) : String :=
  "MD5=" ++ md5Hex bytes ++ "\n"

private def spacesString : Nat → String
  | 0 => ""
  | n + 1 => " " ++ spacesString n

@[inline]
private def padLeftSpacesAscii (s : String) (width : Nat) : String :=
  let len := s.toUTF8.data.size
  if len >= width then s
  else spacesString (width - len) ++ s

def reduceTimebase (tbNum tbDen : Nat) : Nat × Nat :=
  if tbNum == 0 || tbDen == 0 then (1, 25)
  else
    let g := Nat.gcd tbNum tbDen
    (tbNum / g, tbDen / g)

def reduceSar (sarNum sarDen : Nat) : Nat × Nat :=
  if sarNum == 0 || sarDen == 0 then (0, 1)
  else
    let g := Nat.gcd sarNum sarDen
    (sarNum / g, sarDen / g)

private def formatFrameLinesList : List ByteArray → Nat → String → String
  | [], _, acc => acc
  | frm :: rest, i, acc =>
    let idxStr := Nat.repr i
    let dtsStr := padLeftSpacesAscii idxStr 10
    let ptsStr := padLeftSpacesAscii idxStr 10
    let durStr := "       1"
    let szStr := padLeftSpacesAscii (Nat.repr frm.data.size) 8
    let hStr := md5Hex frm
    let row := "0, " ++ dtsStr ++ ", " ++ ptsStr ++ ", " ++ durStr ++ ", " ++ szStr ++ ", " ++ hStr ++ "\n"
    formatFrameLinesList rest (i + 1) (acc ++ row)

def formatFrameMd5Muxer (width height tbNum tbDen sarNum sarDen : Nat)
    (frames : Array ByteArray) : String :=
  let (rTbNum, rTbDen) := reduceTimebase tbNum tbDen
  let (rSarNum, rSarDen) := reduceSar sarNum sarDen
  let hdr :=
    "#format: frame checksums\n" ++
    "#version: 2\n" ++
    "#hash: MD5\n" ++
    "#software: Lavf60.16.100\n" ++
    "#tb 0: " ++ Nat.repr rTbNum ++ "/" ++ Nat.repr rTbDen ++ "\n" ++
    "#media_type 0: video\n" ++
    "#codec_id 0: rawvideo\n" ++
    "#dimensions 0: " ++ Nat.repr width ++ "x" ++ Nat.repr height ++ "\n" ++
    "#sar 0: " ++ Nat.repr rSarNum ++ "/" ++ Nat.repr rSarDen ++ "\n" ++
    "#stream#, dts,        pts, duration,     size, hash\n"
  formatFrameLinesList frames.toList 0 hdr

@[inline]
def isLowerHexByte (b : UInt8) : Bool :=
  (b >= 48 && b <= 57) || (b >= 97 && b <= 102)

def isValidMd5MuxerBytes (bs : Array UInt8) : Bool :=
  bs.size == 37 &&
  bs.getD 0 0 == 77 &&
  bs.getD 1 0 == 68 &&
  bs.getD 2 0 == 53 &&
  bs.getD 3 0 == 61 &&
  bs.getD 36 0 == 10 &&
  (List.range 32).all (fun i => isLowerHexByte (bs.getD (4 + i) 0))

def Md5MuxerBytesSafe (bs : Array UInt8) : Prop :=
  isValidMd5MuxerBytes bs = true

set_option maxRecDepth 200000 in
def md5MuxerBytesGateSpec : AVGateSpec (Array UInt8) Md5MuxerBytesSafe where
  gate := isValidMd5MuxerBytes
  sound _ h := h
  complete _ h := h
  posWitness := (formatMd5Muxer { data := #[] }).toUTF8.data
  negWitness := ("MD5=d41d8cd98f00b204e9800998ecf8427G\n").toUTF8.data
  nonVacuous := by decide
  tight := by decide

theorem md5_muxer_bytes_rejects_malformed (bs : Array UInt8)
    (h_bad : ¬ Md5MuxerBytesSafe bs) :
    isValidMd5MuxerBytes bs = false :=
  md5MuxerBytesGateSpec.rejects_unsafe bs h_bad

theorem md5_digest_size (b : ByteArray) : (md5 b).size = 16 := by
  unfold md5 packDigest16 ByteArray.size
  rfl

set_option maxRecDepth 200000 in
theorem md5Hex_rfc1321_vectors :
    md5Hex "".toUTF8 = "d41d8cd98f00b204e9800998ecf8427e" ∧
    md5Hex "abc".toUTF8 = "900150983cd24fb0d6963f7d28e17f72" ∧
    md5Hex "message digest".toUTF8 = "f96b697d7cb7938d525a2f31aaf161d0" := by
  decide

set_option maxRecDepth 200000 in
theorem formatMd5Muxer_rfc1321_abc :
    formatMd5Muxer "abc".toUTF8 = "MD5=900150983cd24fb0d6963f7d28e17f72\n" := by
  decide

theorem reduceTimebase_fallback_zero (n d : Nat) (h : n = 0 ∨ d = 0) :
    reduceTimebase n d = (1, 25) := by
  unfold reduceTimebase
  rcases h with rfl | rfl <;> simp

theorem reduceSar_fallback_zero (n d : Nat) (h : n = 0 ∨ d = 0) :
    reduceSar n d = (0, 1) := by
  unfold reduceSar
  rcases h with rfl | rfl <;> simp

set_option maxRecDepth 200000 in
theorem formatFrameMd5Muxer_ffmpeg_2x2_exact :
    formatFrameMd5Muxer 2 2 2 50 0 1 #[{ data := Array.replicate 12 0 }] =
      "#format: frame checksums\n" ++
      "#version: 2\n" ++
      "#hash: MD5\n" ++
      "#software: Lavf60.16.100\n" ++
      "#tb 0: 1/25\n" ++
      "#media_type 0: video\n" ++
      "#codec_id 0: rawvideo\n" ++
      "#dimensions 0: 2x2\n" ++
      "#sar 0: 0/1\n" ++
      "#stream#, dts,        pts, duration,     size, hash\n" ++
      "0,          0,          0,        1,       12, 8dd6bb7329a71449b0a1b292b5999164\n" := by
  decide

end LeanAV.Md5
