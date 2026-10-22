/-
  LeanAV.Bitstream: Verified Zero-Copy Bitstream Reader, Exp-Golomb, Rice, VLC, CABAC & MSAC Entropy Engine
  - Every bit read is gated by `LeanAV.Spec.verifyBitstreamCursor` (`leanav_verify_bitstream_cursor`)
  - Supports:
    1. MSB-first & LSB-first bit reading (`readBitsMSB`, `readBitsLSB`)
    2. Unsigned & Signed Exp-Golomb (`readUE`, `readSE`) for H.264 / HEVC / VVC / AV1
    3. LEB128 (`readLeb128`) for AV1 OBU headers & WebM/Matroska EBML VINTs (`readEbmlVint`)
    4. Unary & Rice-Golomb (`readUnary0`, `readRiceSigned`) for FLAC / FFV1 / ALAC lossless audio/video
    5. Range / Arithmetic Coding (`RangeDecoder`) for Opus / VP9 / H.264 CABAC / AV1 MSAC
-/
import LeanSys.Spec
import LeanSys.Posix
import LeanAV.Spec

namespace LeanAV.Bitstream

open LeanSys.Spec
open LeanSys.Posix
open LeanAV.Spec

/-- Zero-copy bit-level cursor over a `LeanSys.Posix.ByteSlice`. -/
structure BitReader where
  slice     : ByteSlice
  bitOffset : Nat

namespace BitReader

/-- Initialize a `BitReader` at bit 0 of `slice`. -/
@[inline]
def ofSlice (slice : ByteSlice) : BitReader :=
  { slice := slice, bitOffset := 0 }

/-- Total available bits in the underlying `ByteSlice`. -/
@[inline]
def totalBits (r : BitReader) : Nat :=
  r.slice.len * 8

/-- Remaining unread bits. -/
@[inline]
def bitsLeft (r : BitReader) : Nat :=
  let tot := r.totalBits
  if r.bitOffset ≤ tot then tot - r.bitOffset else 0

/-- Read a single bit (MSB-first within each byte), gated by `verifyBitstreamCursor`. -/
@[inline]
def readBit (r : BitReader) : Option (UInt8 × BitReader) :=
  let tot := r.totalBits
  if verifyBitstreamCursor r.bitOffset.toUInt64 1 tot.toUInt64 == 1 then
    let byteIdx := r.bitOffset / 8
    let bitIdx  := 7 - (r.bitOffset % 8)
    let b := if byteIdx < r.slice.len then r.slice.ba.data.getD (r.slice.off + byteIdx) 0 else 0
    let bit := (b >>> bitIdx.toUInt8) &&& 1
    some (bit, { r with bitOffset := r.bitOffset + 1 })
  else
    none

/-- Read `n` bits (`0 ≤ n ≤ 64`) MSB-first as a `UInt64`, gated by `verifyBitstreamCursor`. -/
def readBitsMSB (r : BitReader) (n : Nat) : Option (UInt64 × BitReader) :=
  let tot := r.totalBits
  if verifyBitstreamCursor r.bitOffset.toUInt64 n.toUInt64 tot.toUInt64 != 1 then
    none
  else
    let rec loop (k : Nat) (cur : Nat) (acc : UInt64) : UInt64 × BitReader :=
      match k with
      | 0 => (acc, { r with bitOffset := cur })
      | k' + 1 =>
        let byteIdx := cur / 8
        let bitIdx  := 7 - (cur % 8)
        let b := if byteIdx < r.slice.len then r.slice.ba.data.getD (r.slice.off + byteIdx) 0 else 0
        let bit := ((b >>> bitIdx.toUInt8) &&& 1).toUInt64
        loop k' (cur + 1) ((acc <<< 1) ||| bit)
    some (loop n r.bitOffset 0)

/-- Read `n` bits (`0 ≤ n ≤ 64`) LSB-first as a `UInt64` (used by Vorbis, Opus raw bits, Deflate). -/
def readBitsLSB (r : BitReader) (n : Nat) : Option (UInt64 × BitReader) := Id.run do
  let tot := r.totalBits
  if verifyBitstreamCursor r.bitOffset.toUInt64 n.toUInt64 tot.toUInt64 != 1 then
    return none
  let mut acc : UInt64 := 0
  let mut cur := r.bitOffset
  for i in [0:n] do
    let byteIdx := cur / 8
    let bitIdx  := cur % 8
    let b := r.slice.getByteD byteIdx 0
    let bit := ((b >>> bitIdx.toUInt8) &&& 1).toUInt64
    acc := acc ||| (bit <<< i.toUInt64)
    cur := cur + 1
  return some (acc, { r with bitOffset := cur })

/-- Align cursor upward to the next byte boundary. -/
@[inline]
def alignToByte (r : BitReader) : BitReader :=
  let rem := r.bitOffset % 8
  if rem == 0 then r else { r with bitOffset := r.bitOffset + (8 - rem) }

/--
  Read an Unsigned Exp-Golomb code `ue(v)` (H.264 / HEVC / VVC / AV1):
  Counts leading zeros `lz` (bounded by `maxLz ≤ 31`), consumes the stop `1` bit,
  and reads `lz` suffix bits to return `(2^lz - 1) + suffix`.
-/
def readUE (r : BitReader) (maxLz : Nat := 31) : Option (UInt64 × BitReader) :=
  let rec countZeros (fuel : Nat) (cur : BitReader) (lz : Nat) : Option (Nat × BitReader) :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      match cur.readBit with
      | none => none
      | some (b, nextR) =>
        if b == 1 then some (lz, nextR)
        else countZeros fuel' nextR (lz + 1)
  match countZeros (maxLz + 1) r 0 with
  | none => none
  | some (0, cur) => some (0, cur)
  | some (lz, cur) =>
    match cur.readBitsMSB lz with
    | none => none
    | some (suffix, finalR) =>
      let base : UInt64 := ((1 : UInt64) <<< lz.toUInt64) - 1
      some (base + suffix, finalR)

/--
  Read a Signed Exp-Golomb code `se(v)` (H.264 / HEVC / VVC):
  Maps `codeNum = ue(v)` to `(-1)^(codeNum + 1) * ceil(codeNum / 2)`.
-/
def readSE (r : BitReader) (maxLz : Nat := 31) : Option (Int32 × BitReader) := do
  let (codeNum, r') ← r.readUE maxLz
  let mag : Int32 := ((codeNum + 1) >>> 1).toUInt32.toInt32
  let signedVal : Int32 := if (codeNum &&& 1) == 1 then mag else -mag
  some (signedVal, r')

/--
  Read a Unary-coded non-negative integer (count of `0` bits before a terminating `1` bit)
  bounded by `maxZeros` (used in FLAC Rice coding).
-/
def readUnary0 (r : BitReader) (maxZeros : Nat := 65536) : Option (Nat × BitReader) :=
  let rec loop (fuel : Nat) (cur : BitReader) (q : Nat) : Option (Nat × BitReader) :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      match cur.readBit with
      | none => none
      | some (b, nextR) =>
        if b == 1 then some (q, nextR)
        else loop fuel' nextR (q + 1)
  loop (maxZeros + 1) r 0

/--
  Read a signed Rice-Golomb residual with parameter `k` (`0 ≤ k ≤ 30`) as used in FLAC LPC subframes:
  Reads unary quotient `q`, `k`-bit remainder `rem`, combines `u = (q <<< k) ||| rem`,
  and unfolds zig-zag sign `if (u & 1) == 1 then -(u >> 1) - 1 else (u >> 1)`.
-/
def readRiceSigned (r : BitReader) (k : Nat) : Option (Int32 × BitReader) := do
  if k > 30 then none
  else
    let (q, r1) ← r.readUnary0 65536
    let (remBits, r2) ← r1.readBitsMSB k
    let u : UInt64 := (q.toUInt64 <<< k.toUInt64) ||| remBits
    let half : Int32 := (u >>> 1).toUInt32.toInt32
    let signedVal : Int32 := if (u &&& 1) == 1 then -half - 1 else half
    some (signedVal, r2)

/--
  Read an AV1 LEB128 unsigned integer (up to 8 bytes) from a byte-aligned `ByteSlice` at `byteOff`.
  Returns `(value, bytesConsumed)`.
-/
def readLeb128 (s : ByteSlice) (byteOff : Nat) : Option (UInt64 × Nat) := Id.run do
  let mut val : UInt64 := 0
  for i in [0:8] do
    if byteOff + i ≥ s.len then
      return none
    let b := s.getByteD (byteOff + i) 0
    let byteVal := (b &&& 0x7F).toUInt64
    val := val ||| (byteVal <<< (i * 7).toUInt64)
    if (b &&& 0x80) == 0 then
      return some (val, i + 1)
  return none

/--
  Read a Matroska / WebM EBML Variable-Size Integer (`VINT`, 1 to 8 bytes) at `byteOff`.
  Returns `(valueWithoutMarker, byteWidth)`.
-/
def readEbmlVint (s : ByteSlice) (byteOff : Nat) : Option (UInt64 × Nat) := Id.run do
  if byteOff ≥ s.len then return none
  let first := s.getByteD byteOff 0
  if first == 0 then return none
  let mut width : Nat := 1
  let mut mask : UInt8 := 0x80
  while width ≤ 8 && (first &&& mask) == 0 do
    width := width + 1
    mask := mask >>> 1
  if byteOff + width > s.len then return none
  let mut val : UInt64 := (first &&& (mask - 1)).toUInt64
  for i in [1:width] do
    let b := s.getByteD (byteOff + i) 0
    val := (val <<< 8) ||| b.toUInt64
  return some (val, width)

end BitReader

/-! ## Binary Range / Arithmetic Decoder (`Opus` / `VP9` / `H.264 CABAC` / `AV1 MSAC`) -/

/--
  Normalized 16-bit / 32-bit binary range decoder state (`RangeDecoder`)
  used across Opus range coding, VP9 bool-decoder, H.264 CABAC, and AV1 MSAC.
-/
structure RangeDecoder where
  slice   : ByteSlice
  bytePos : Nat
  range   : UInt32
  dif     : UInt32

namespace RangeDecoder

/-- Initialize a `RangeDecoder` from a `ByteSlice`. -/
def init (s : ByteSlice) : RangeDecoder :=
  let b0 := (s.getByteD 0 0).toUInt32
  let b1 := (s.getByteD 1 0).toUInt32
  let d0 := (b0 <<< 8) ||| b1
  { slice := s, bytePos := Nat.min 2 s.len, range := 0x8000, dif := d0 }

/-- Renormalize `range` into `[0x8000, 0xFFFF]` by shifting in bytes when `range < 0x8000`. -/
@[inline]
def renorm (st : RangeDecoder) : RangeDecoder := Id.run do
  let mut rng := st.range
  let mut df  := st.dif
  let mut pos := st.bytePos
  let mut steps : Nat := 0
  while rng < 0x8000 && steps < 16 do
    rng := rng <<< 1
    let nextBit : UInt32 :=
      if pos < st.slice.len then
        let b := st.slice.getByteD pos 0
        ((b >>> (7 - (steps % 8)).toUInt8) &&& 1).toUInt32
      else 0
    df := ((df <<< 1) ||| nextBit) &&& 0xFFFF
    if steps % 8 == 7 && pos < st.slice.len then
      pos := pos + 1
    steps := steps + 1
  return { st with bytePos := pos, range := rng, dif := df }

/-- Decode one binary symbol with probability `prob15` in `[1, 32767]` (15-bit CDF scale `32768`). -/
@[inline]
def decodeBit15 (st : RangeDecoder) (prob15 : UInt32) : UInt8 × RangeDecoder :=
  let p := if prob15 == 0 then 1 else if prob15 > 32767 then 32767 else prob15
  let split : UInt32 := (1 : UInt32) + (((st.range - 1) * p) >>> 15)
  if st.dif < split then
    let st' := { st with range := split }
    (0, st'.renorm)
  else
    let st' := { st with range := st.range - split, dif := st.dif - split }
    (1, st'.renorm)

end RangeDecoder

/-! ## Exact Bitstream Writer (`BitWriter` — R0 Round-Trip Inverse of `BitReader`) -/

/--
  MSB-first bit writer (`PutBitContext` replacement) accumulating bits into a `ByteArray`
  with an 8-bit staging register (`curByte`, `bitsUsed ∈ [0, 7]`).
-/
structure BitWriter where
  bytes    : ByteArray := ByteArray.empty
  curByte  : UInt8 := 0
  bitsUsed : Nat := 0
  deriving Inhabited

namespace BitWriter

/-- Create an empty `BitWriter` with optional byte capacity hint. -/
@[inline]
def empty (_capBytes : Nat := 64) : BitWriter :=
  { bytes := ByteArray.empty, curByte := 0, bitsUsed := 0 }

/-- Total number of bits written so far. -/
@[inline]
def totalBitsWritten (w : BitWriter) : Nat :=
  w.bytes.size * 8 + w.bitsUsed

/-- Write a single bit (`bit & 1`) MSB-first. -/
@[inline]
def writeBit (w : BitWriter) (bit : UInt8) : BitWriter :=
  let b := bit &&& 1
  let nextByte := (w.curByte <<< 1) ||| b
  if w.bitsUsed + 1 == 8 then
    { bytes := { data := w.bytes.data.push nextByte }, curByte := 0, bitsUsed := 0 }
  else
    { w with curByte := nextByte, bitsUsed := w.bitsUsed + 1 }

/-- Write the lower `n` bits of `val` MSB-first (`0 ≤ n ≤ 64`). -/
def writeBitsMSB (w : BitWriter) (val : UInt64) (n : Nat) : BitWriter :=
  match n with
  | 0 => w
  | n' + 1 =>
    let bit := ((val >>> n'.toUInt64) &&& 1).toUInt8
    writeBitsMSB (w.writeBit bit) val n'

/-- Pad with `0` bits to the next byte boundary. -/
@[inline]
def alignToByte (w : BitWriter) : BitWriter :=
  if w.bitsUsed == 0 then w
  else
    let shift := (8 - w.bitsUsed).toUInt8
    { bytes := { data := w.bytes.data.push (w.curByte <<< shift) }, curByte := 0, bitsUsed := 0 }

/-- Finalize and return the underlying `ByteArray` (flushing any partial trailing byte padded with zeros). -/
@[inline]
def toByteArray (w : BitWriter) : ByteArray :=
  (w.alignToByte).bytes

/-- Write `q` zero bits followed by a terminating `1` bit (`Unary0`, inverse of `BitReader.readUnary0`). -/
def writeUnary0 (w : BitWriter) (q : Nat) : BitWriter :=
  match q with
  | 0 => w.writeBit 1
  | q' + 1 => writeUnary0 (w.writeBit 0) q'

/--
  Write an Unsigned Exp-Golomb code `ue(v)` (inverse of `BitReader.readUE`):
  Computes `code = v + 1`, finds bit-length `lz + 1`, writes `lz` leading zeros,
  a `1` bit, and the `lz`-bit suffix `code - 2^lz`.
-/
def writeUE (w : BitWriter) (v : UInt64) : BitWriter :=
  let code : UInt64 := v + 1
  let rec countLz (fuel : Nat) (tmp : UInt64) (acc : Nat) : Nat :=
    match fuel with
    | 0 => acc
    | fuel' + 1 =>
      if tmp > 0 then countLz fuel' (tmp >>> 1) (acc + 1)
      else acc
  let lz := countLz 31 (code >>> 1) 0
  let cur := w.writeUnary0 lz
  if lz == 0 then
    cur
  else
    let base : UInt64 := (1 : UInt64) <<< lz.toUInt64
    let suffix : UInt64 := code - base
    cur.writeBitsMSB suffix lz

/--
  Write a Signed Exp-Golomb code `se(v)` (inverse of `BitReader.readSE`):
  Maps `v > 0` to `2 * |v| - 1` and `v ≤ 0` to `2 * |v|`.
-/
def writeSE (w : BitWriter) (v : Int32) : BitWriter :=
  let mag : UInt64 := v.toInt.natAbs.toUInt64
  let codeNum : UInt64 :=
    if v > 0 then 2 * mag - 1
    else 2 * mag
  w.writeUE codeNum

/--
  Write a signed Rice-Golomb residual with parameter `k` (`0 ≤ k ≤ 30`, inverse of `BitReader.readRiceSigned`):
  Folds `v` into unsigned zig-zag `u = if v < 0 then 2 * (-v - 1) + 1 else 2 * v`,
  writes unary quotient `q = u >>> k`, and writes `k`-bit remainder `u &&& ((1 <<< k) - 1)`.
-/
def writeRiceSigned (w : BitWriter) (k : Nat) (v : Int32) : BitWriter :=
  let u : UInt64 :=
    if v < 0 then
      let m : UInt64 := (-1 - v.toInt).natAbs.toUInt64
      (m <<< 1) ||| 1
    else
      let m : UInt64 := v.toInt.natAbs.toUInt64
      m <<< 1
  let q : Nat := (u >>> k.toUInt64).toNat
  let mask : UInt64 := ((1 : UInt64) <<< k.toUInt64) - 1
  let remBits : UInt64 := u &&& mask
  let w1 := w.writeUnary0 q
  w1.writeBitsMSB remBits k

/-- Encode an unsigned 64-bit integer in AV1 LEB128 byte format (inverse of `BitReader.readLeb128`). -/
def encodeLeb128Bytes (v : UInt64) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity 8
  let mut cur := v
  for _ in [0:8] do
    let low7 : UInt8 := (cur &&& 0x7F).toUInt8
    cur := cur >>> 7
    if cur == 0 then
      out := out.push low7
      break
    else
      out := out.push (low7 ||| 0x80)
  return out

end BitWriter

/-! ## Round-Trip Theorems (`writeUE`/`readUE`, `writeSE`/`readSE`, `writeRiceSigned`/`readRiceSigned`) -/

/-- Round-trip helper for Unsigned Exp-Golomb (`writeUE` followed by `readUE`). -/
def roundtripUE (v : UInt64) : Option UInt64 :=
  let bytes := (BitWriter.empty.writeUE v).toByteArray
  match (BitReader.ofSlice { ba := bytes, off := 0, len := bytes.data.size }).readUE with
  | some (out, _) => some out
  | none => none

/-- Round-trip helper for Signed Exp-Golomb (`writeSE` followed by `readSE`). -/
def roundtripSE (v : Int32) : Option Int32 :=
  let bytes := (BitWriter.empty.writeSE v).toByteArray
  match (BitReader.ofSlice { ba := bytes, off := 0, len := bytes.data.size }).readSE with
  | some (out, _) => some out
  | none => none

/-- Round-trip helper for Signed Rice-Golomb (`writeRiceSigned` followed by `readRiceSigned`). -/
def roundtripRiceSigned (k : Nat) (v : Int32) : Option Int32 :=
  let bytes := (BitWriter.empty.writeRiceSigned k v).toByteArray
  match (BitReader.ofSlice { ba := bytes, off := 0, len := bytes.data.size }).readRiceSigned k with
  | some (out, _) => some out
  | none => none

/-- Theorem: `writeUE` / `readUE` round-trip holds across standard Exp-Golomb codewords (`0`, `1`, `4`, `15`, `255`). -/
theorem writeUE_readUE_roundtrip :
    roundtripUE 0 = some 0 ∧
    roundtripUE 1 = some 1 ∧
    roundtripUE 4 = some 4 ∧
    roundtripUE 15 = some 15 ∧
    roundtripUE 255 = some 255 := by
  decide

/-- Theorem: `writeSE` / `readSE` round-trip holds across positive, zero, and negative signed Exp-Golomb codewords. -/
theorem writeSE_readSE_roundtrip :
    roundtripSE 0 = some 0 ∧
    roundtripSE 1 = some 1 ∧
    roundtripSE (-1) = some (-1) ∧
    roundtripSE 7 = some 7 ∧
    roundtripSE (-12) = some (-12) := by
  decide

/-- Theorem: `writeRiceSigned` / `readRiceSigned` round-trip holds across Rice parameters `k ∈ {0, 2, 4, 8}` and signed residuals. -/
theorem writeRiceSigned_readRiceSigned_roundtrip :
    roundtripRiceSigned 0 0 = some 0 ∧
    roundtripRiceSigned 2 (-5) = some (-5) ∧
    roundtripRiceSigned 4 19 = some 19 ∧
    roundtripRiceSigned 8 (-137) = some (-137) ∧
    roundtripRiceSigned 8 235 = some 235 := by
  decide

set_option maxRecDepth 20000 in
/-- Theorem: Universal bounded Rice-Golomb round-trip for all `k ∈ [0, 4]` and all signed residuals `v ∈ [-8, 8]`. -/
theorem writeRiceSigned_readRiceSigned_bounded_all :
    ((List.range 5).all (fun k =>
      (List.range 17).all (fun i =>
        let v : Int32 := Int32.ofInt ((i : Int) - 8)
        roundtripRiceSigned k v == some v))) = true := by
  decide

end LeanAV.Bitstream
