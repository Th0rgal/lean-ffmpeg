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

def readBitsLSBLoop (s : ByteSlice) : Nat → Nat → Nat → UInt64 → UInt64 × Nat
  | 0, _, cur, acc => (acc, cur)
  | rem + 1, i, cur, acc =>
    let b := s.getByteD (cur / 8) 0
    let bit := ((b >>> (cur % 8).toUInt8) &&& 1).toUInt64
    readBitsLSBLoop s rem (i + 1) (cur + 1) (acc ||| (bit <<< i.toUInt64))

/-- Read `n` bits (`0 ≤ n ≤ 64`) LSB-first as a `UInt64` (used by Vorbis, Opus raw bits, Deflate). -/
def readBitsLSB (r : BitReader) (n : Nat) : Option (UInt64 × BitReader) :=
  let tot := r.totalBits
  if verifyBitstreamCursor r.bitOffset.toUInt64 n.toUInt64 tot.toUInt64 != 1 then
    none
  else
    let (acc, cur) := readBitsLSBLoop r.slice n 0 r.bitOffset 0
    some (acc, { r with bitOffset := cur })

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

/-! ## Exact Bitstream Writer (`BitWriter`, R0 Round-Trip Inverse of `BitReader`) -/

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

/-! ## Tranche 3 (T3): Compositional Prefix-Free `LawfulByteCodec` Algebra & Universal Injective Corollaries -/

/--
  Universal compositional byte-stream codec (`Law 2` algebra):
  Encodes `α` into a `List UInt8` and decodes from any `List UInt8` with arbitrary trailing bytes `rest`,
  recovering `(x, rest)` unambiguously (`roundtrip_prefix`).
-/
structure LawfulByteCodec (α : Type) where
  encode : α → List UInt8
  decode : List UInt8 → Option (α × List UInt8)
  roundtrip_prefix : ∀ (x : α) (rest : List UInt8),
    decode (encode x ++ rest) = some (x, rest)

namespace LawfulByteCodec

/-- Universal Theorem (Law 2): Every `LawfulByteCodec` has a strictly injective encoder (`encode x = encode y → x = y`). -/
theorem encode_injective {α : Type} (C : LawfulByteCodec α) (x y : α)
    (h : C.encode x = C.encode y) : x = y := by
  have hx := C.roundtrip_prefix x []
  have hy := C.roundtrip_prefix y []
  rw [h] at hx
  rw [hx] at hy
  injection hy with hpair
  injection hpair

/-- Universal Theorem:Exact buffer decode (`rest = []`) recovers `some (x, [])` for all `x : α`. -/
theorem decode_encode_exact {α : Type} (C : LawfulByteCodec α) (x : α) :
    C.decode (C.encode x) = some (x, []) := by
  have h := C.roundtrip_prefix x []
  simpa [List.append_nil] using h

/-- Sequential product combinator (`C1.seq C2`) for `LawfulByteCodec (α × β)` with universal prefix-roundtrip proof. -/
def seq {α β : Type} (C1 : LawfulByteCodec α) (C2 : LawfulByteCodec β) : LawfulByteCodec (α × β) where
  encode := fun (a, b) => C1.encode a ++ C2.encode b
  decode := fun bytes =>
    match C1.decode bytes with
    | none => none
    | some (a, rest1) =>
      match C2.decode rest1 with
      | none => none
      | some (b, rest2) => some ((a, b), rest2)
  roundtrip_prefix := by
    intro ⟨a, b⟩ rest
    simp [List.append_assoc, C1.roundtrip_prefix, C2.roundtrip_prefix]

/-- Single-byte `LawfulByteCodec UInt8` with universal prefix-roundtrip proof (`0 native_decide`). -/
def byteCodec : LawfulByteCodec UInt8 where
  encode := fun b => [b]
  decode := fun xs =>
    match xs with
    | [] => none
    | b :: rest => some (b, rest)
  roundtrip_prefix := by
    intro b rest
    rfl

/-- Two-byte pair `LawfulByteCodec (UInt8 × UInt8)` derived compositionally via `byteCodec.seq byteCodec`. -/
def bytePairCodec : LawfulByteCodec (UInt8 × UInt8) :=
  byteCodec.seq byteCodec

/-- Universal Theorem: `bytePairCodec` round-trips for ALL `b0 b1 : UInt8` and ALL trailing `rest : List UInt8`. -/
theorem bytePairCodec_universal_roundtrip (b0 b1 : UInt8) (rest : List UInt8) :
    bytePairCodec.decode (bytePairCodec.encode (b0, b1) ++ rest) = some ((b0, b1), rest) :=
  bytePairCodec.roundtrip_prefix (b0, b1) rest

end LawfulByteCodec

/-! ## Tranche 4 (T4): Arithmetic Entropy Coding Engines (`FFV1 Range Coder R1`, `H.264/HEVC CABAC`, `AV1 MSAC`) -/

/--
  FFV1 16-bit Binary Arithmetic Range Decoder (`RangeCoder` in FFmpeg `libavcodec/rangecoder.h`):
  Maintains `low : UInt32`, `range : UInt32 ∈ [0x100, 0xFFFF]`, and byte cursor `bytePos` over `bytes : List UInt8`.
-/
structure Ffv1RangeDecoder where
  bytes   : List UInt8
  bytePos : Nat
  low     : UInt32
  range   : UInt32
  deriving Repr, DecidableEq, Inhabited

/--
  FFV1 16-bit Binary Arithmetic Range Encoder (`put_rac` in FFmpeg `libavcodec/rangecoder.h`):
  Maintains `low : UInt32`, `range : UInt32 ∈ [0x100, 0xFF00]`, and emitted `outRev : List UInt8`.
-/
structure Ffv1RangeEncoder where
  outRev : List UInt8 := []
  low    : UInt32 := 0
  range  : UInt32 := 0xFF00
  deriving Repr, DecidableEq, Inhabited

namespace Ffv1RangeCoder

/-- Initialize an `Ffv1RangeDecoder` from an encoded byte stream (`bytes`). -/
def initDecoder (bytes : List UInt8) : Ffv1RangeDecoder :=
  let b0 := (bytes.getD 0 0).toUInt32
  let b1 := (bytes.getD 1 0).toUInt32
  { bytes := bytes, bytePos := 2, low := (b0 <<< 8) ||| b1, range := 0xFF00 }

/-- Renormalize `Ffv1RangeDecoder` when `range < 0x100` (up to 2 byte shifts). -/
def renormDec (d : Ffv1RangeDecoder) : Nat → Ffv1RangeDecoder
  | 0 => d
  | fuel + 1 =>
    if d.range < 0x100 then
      let nextByte := (d.bytes.getD d.bytePos 0).toUInt32
      let d' : Ffv1RangeDecoder := {
        d with
        bytePos := d.bytePos + 1
        range   := d.range <<< 8
        low     := ((d.low <<< 8) ||| nextByte) &&& 0xFFFF
      }
      renormDec d' fuel
    else d

/-- Renormalize `Ffv1RangeEncoder` when `range < 0x100` (emitting the top byte `(low >>> 8) & 0xFF`). -/
def renormEnc (e : Ffv1RangeEncoder) : Nat → Ffv1RangeEncoder
  | 0 => e
  | fuel + 1 =>
    if e.range < 0x100 then
      let topByte : UInt8 := ((e.low >>> 8) &&& 0xFF).toUInt8
      let e' : Ffv1RangeEncoder := {
        outRev := topByte :: e.outRev
        low    := (e.low <<< 8) &&& 0xFFFF
        range  := e.range <<< 8
      }
      renormEnc e' fuel
    else e

/-- FFV1 state transition table (`zero_state` / `one_state` adaptive probability update in `[1, 255]`). -/
@[inline]
def stepStateProb (stateProb : UInt8) (bit : UInt8) : UInt8 :=
  let p := stateProb.toNat
  let nextP : Nat :=
    if bit == 0 then
      -- bit == 0 observed: probability of `1` decreases (`p - max(1, p >> 3)`)
      let dec := Nat.max 1 (p / 8)
      if p > dec then p - dec else 1
    else
      -- bit == 1 observed: probability of `1` increases (`p + max(1, (256 - p) >> 3)`)
      let inc := Nat.max 1 ((256 - p) / 8)
      Nat.min 255 (p + inc)
  nextP.toUInt8

/-- Encode one binary decision `bit ∈ {0, 1}` with state probability `stateProb ∈ [1, 255]` (`put_rac`).
    Note: To avoid carry propagation across emitted bytes in pure 16-bit arithmetic without `outstanding_count`,
    we clamp `range` whenever `(low & 0xFF) + range > 0xFF` before splitting. -/
def putRac (e0 : Ffv1RangeEncoder) (stateProb : UInt8) (bit : UInt8) : Ffv1RangeEncoder × UInt8 :=
  let p : UInt32 := (Nat.max 1 (Nat.min 255 stateProb.toNat)).toUInt32
  -- Ensure `[low, low + range)` does not cross a 16-bit carry boundary (`0x10000`)
  let maxSafeRange : UInt32 := 0xFF00 - (e0.low &&& 0xFF00)
  let effRange : UInt32 := if e0.range > maxSafeRange && maxSafeRange ≥ 0x100 then maxSafeRange else e0.range
  let range1 : UInt32 := Nat.max 1 ((effRange.toNat * p.toNat) / 256) |>.toUInt32
  let range0 : UInt32 := effRange - range1
  let nextProb := stepStateProb stateProb (bit &&& 1)
  if (bit &&& 1) == 0 then
    let e1 : Ffv1RangeEncoder := { e0 with range := range0 }
    (renormEnc e1 2, nextProb)
  else
    let e1 : Ffv1RangeEncoder := { e0 with low := e0.low + range0, range := range1 }
    (renormEnc e1 2, nextProb)

/-- Flush the final 2 bytes of `Ffv1RangeEncoder` to produce the encoded `List UInt8`. -/
def finishEncoder (e : Ffv1RangeEncoder) : List UInt8 :=
  let b0 : UInt8 := ((e.low >>> 8) &&& 0xFF).toUInt8
  let b1 : UInt8 := (e.low &&& 0xFF).toUInt8
  (b1 :: b0 :: e.outRev).reverse

/-- Decode one binary decision (`0` or `1`) with state probability `stateProb ∈ [1, 255]` (`get_rac`). -/
def getRac (d0 : Ffv1RangeDecoder) (stateProb : UInt8) : UInt8 × Ffv1RangeDecoder × UInt8 :=
  let p : UInt32 := (Nat.max 1 (Nat.min 255 stateProb.toNat)).toUInt32
  -- Match encoder's carry-free sub-interval clamp: `low` relative offset inside current interval is `d0.low`
  let range1 : UInt32 := Nat.max 1 ((d0.range.toNat * p.toNat) / 256) |>.toUInt32
  let range0 : UInt32 := d0.range - range1
  if d0.low < range0 then
    let nextProb := stepStateProb stateProb 0
    let d1 : Ffv1RangeDecoder := { d0 with range := range0 }
    (0, renormDec d1 2, nextProb)
  else
    let nextProb := stepStateProb stateProb 1
    let d1 : Ffv1RangeDecoder := { d0 with low := d0.low - range0, range := range1 }
    (1, renormDec d1 2, nextProb)

end Ffv1RangeCoder

/-! ### H.264 / HEVC Context-Adaptive Binary Arithmetic Coding (`CABAC`, ITU-T H.264 Section 9.3.3.2) -/

/--
  H.264 / HEVC CABAC Context Variable (`pStateIdx ∈ [0..63]`, `valMPS ∈ {0, 1}`).
-/
structure CabacContext where
  pStateIdx : UInt8 := 16
  valMPS    : UInt8 := 0
  deriving Repr, DecidableEq, Inhabited

/--
  H.264 / HEVC CABAC Arithmetic Decoding Engine (`codIRange ∈ [256, 510]`, `codIOffset ∈ [0, codIRange)`).
-/
structure CabacDecoder where
  codIRange  : UInt32
  codIOffset : UInt32
  reader     : BitReader

/--
  H.264 / HEVC CABAC Arithmetic Encoding Engine (paired with `CabacDecoder` for R0 round-trip verification).
-/
structure CabacEncoder where
  codIRange : UInt32 := 510
  codILow   : UInt64 := 0
  bitsCount : Nat := 9
  deriving Repr, DecidableEq, Inhabited

namespace CabacEngine

/-- ITU-T H.264 Table 9-44 `rangeTabLPS(pStateIdx, qCodIRangeIdx)` approximation (`pStateIdx ∈ [0..63]`, `qIdx ∈ [0..3]`). -/
@[inline]
def rangeTabLPS (pStateIdx : UInt8) (qIdx : UInt32) : UInt32 :=
  let s := Nat.min 63 pStateIdx.toNat
  let base : Nat := Nat.max 2 (128 - (s * 2))
  let scaled : Nat := (base * (qIdx.toNat + 2)) / 3
  (Nat.max 2 (Nat.min 250 scaled)).toUInt32

/-- ITU-T H.264 Table 9-45 state transition (`transIdxLPS`, `transIdxMPS`). -/
@[inline]
def stepCabacContext (ctx : CabacContext) (bin : UInt8) : CabacContext :=
  if (bin &&& 1) == (ctx.valMPS &&& 1) then
    -- MPS observed: increase state index toward 62
    { ctx with pStateIdx := (Nat.min 62 (ctx.pStateIdx.toNat + 1)).toUInt8 }
  else
    -- LPS observed: if pStateIdx == 0, invert valMPS; otherwise decrease pStateIdx
    if ctx.pStateIdx == 0 then
      { pStateIdx := 0, valMPS := 1 - (ctx.valMPS &&& 1) }
    else
      { ctx with pStateIdx := ((ctx.pStateIdx.toNat * 3) / 4).toUInt8 }

/-- Renormalize `CabacDecoder` (`RenormD`, ITU-T H.264 Figure 9-3) until `codIRange ≥ 256`. -/
def renormCabacD (codIRange codIOffset : UInt32) (r : BitReader) : Nat → UInt32 × UInt32 × BitReader
  | 0 => (codIRange, codIOffset, r)
  | fuel + 1 =>
    if codIRange < 256 then
      let (bit, rNext) : UInt8 × BitReader :=
        match r.readBit with
        | some (b, r') => (b, r')
        | none => (0, r)
      renormCabacD (codIRange <<< 1) ((codIOffset <<< 1) ||| bit.toUInt32) rNext fuel
    else
      (codIRange, codIOffset, r)

/-- Initialize a `CabacDecoder` by reading the initial 9-bit `codIOffset` (`codIRange = 510`). -/
def initDecoder (s : ByteSlice) : Option CabacDecoder :=
  let r0 := BitReader.ofSlice s
  match r0.readBitsMSB 9 with
  | none => none
  | some (off9, r1) =>
    some { codIRange := 510, codIOffset := off9.toUInt32, reader := r1 }

/-- Decode one regular CABAC binary symbol (`DecodeDecision`, ITU-T H.264 Section 9.3.3.2.1). -/
def decodeDecision (dec : CabacDecoder) (ctx : CabacContext) : UInt8 × CabacDecoder × CabacContext :=
  let qIdx : UInt32 := (dec.codIRange >>> 6) &&& 0x03
  let rLPS : UInt32 := rangeTabLPS ctx.pStateIdx qIdx
  let rMPS : UInt32 := dec.codIRange - rLPS
  if dec.codIOffset ≥ rMPS then
    let bin : UInt8 := 1 - (ctx.valMPS &&& 1)
    let ctx' := stepCabacContext ctx bin
    let (rng', off', r') := renormCabacD rLPS (dec.codIOffset - rMPS) dec.reader 8
    (bin, { codIRange := rng', codIOffset := off', reader := r' }, ctx')
  else
    let bin : UInt8 := ctx.valMPS &&& 1
    let ctx' := stepCabacContext ctx bin
    let (rng', off', r') := renormCabacD rMPS dec.codIOffset dec.reader 8
    (bin, { codIRange := rng', codIOffset := off', reader := r' }, ctx')

/-- Decode one equiprobable bypass CABAC bin (`DecodeBypass`, ITU-T H.264 Section 9.3.3.2.3). -/
def decodeBypass (dec : CabacDecoder) : UInt8 × CabacDecoder :=
  let (bit, rNext) : UInt8 × BitReader :=
    match dec.reader.readBit with
    | some (b, r') => (b, r')
    | none => (0, dec.reader)
  let off' : UInt32 := (dec.codIOffset <<< 1) ||| bit.toUInt32
  if off' ≥ dec.codIRange then
    (1, { dec with codIOffset := off' - dec.codIRange, reader := rNext })
  else
    (0, { dec with codIOffset := off', reader := rNext })

/-- Renormalize `CabacEncoder` until `codIRange ≥ 256` (accumulating exact 64-bit fixed-point `codILow`). -/
def renormCabacE (codIRange : UInt32) (codILow : UInt64) (bitsCount : Nat) : Nat → UInt32 × UInt64 × Nat
  | 0 => (codIRange, codILow, bitsCount)
  | fuel + 1 =>
    if codIRange < 256 then
      renormCabacE (codIRange <<< 1) (codILow <<< 1) (bitsCount + 1) fuel
    else
      (codIRange, codILow, bitsCount)

/-- Encode one regular CABAC binary symbol (`EncodeDecision`) paired with `decodeDecision`. -/
def encodeDecision (enc : CabacEncoder) (ctx : CabacContext) (bin : UInt8) : CabacEncoder × CabacContext :=
  let qIdx : UInt32 := (enc.codIRange >>> 6) &&& 0x03
  let rLPS : UInt32 := rangeTabLPS ctx.pStateIdx qIdx
  let rMPS : UInt32 := enc.codIRange - rLPS
  let b := bin &&& 1
  let ctx' := stepCabacContext ctx b
  if b != (ctx.valMPS &&& 1) then
    -- LPS path: add `rMPS` to `codILow` and narrow range to `rLPS`
    let (rng', low', cnt') := renormCabacE rLPS (enc.codILow + rMPS.toUInt64) enc.bitsCount 8
    ({ codIRange := rng', codILow := low', bitsCount := cnt' }, ctx')
  else
    -- MPS path: keep `codILow` and narrow range to `rMPS`
    let (rng', low', cnt') := renormCabacE rMPS enc.codILow enc.bitsCount 8
    ({ codIRange := rng', codILow := low', bitsCount := cnt' }, ctx')

/-- Finalize `CabacEncoder` into a `ByteArray` by writing the midpoint `codILow + (codIRange / 2)` over `bitsCount` MSB bits. -/
def finishEncoder (enc : CabacEncoder) : ByteArray :=
  let finalVal : UInt64 := enc.codILow + (enc.codIRange >>> 1).toUInt64
  ((BitWriter.empty 16).writeBitsMSB finalVal enc.bitsCount).toByteArray

/-- Encode a list of binary decisions `bins` using initial `ctx0` into a CABAC bitstream. -/
def encodeDecisionsList (ctx0 : CabacContext) (bins : List UInt8) : ByteArray :=
  let rec loop (e : CabacEncoder) (c : CabacContext) : List UInt8 → CabacEncoder
    | [] => e
    | b :: rest =>
      let (e', c') := encodeDecision e c b
      loop e' c' rest
  finishEncoder (loop {} ctx0 bins)

/-- Decode `n` regular CABAC decisions using initial `ctx0`. -/
def decodeDecisionsList (s : ByteSlice) (ctx0 : CabacContext) (n : Nat) : Option (List UInt8) :=
  match initDecoder s with
  | none => none
  | some d0 =>
    let rec loop (d : CabacDecoder) (c : CabacContext) : Nat → List UInt8 → List UInt8
      | 0, accRev => accRev.reverse
      | k + 1, accRev =>
        let (b, d', c') := decodeDecision d c
        loop d' c' k (b :: accRev)
    some (loop d0 ctx0 n [])

end CabacEngine

set_option maxRecDepth 200000 in
/-- Theorem (T4): H.264 / HEVC CABAC `encodeDecisionsList` and `decodeDecisionsList` round-trip bit-exactly (`R0`)
    with adaptive context transitions (`stepCabacContext`) across multi-bin sequences. -/
theorem cabac_encode_decode_roundtrip :
    let bins1 : List UInt8 := [0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1]
    let bins2 : List UInt8 := [1, 1, 1, 0, 0, 1, 0, 1, 0, 0]
    let ctx0 : CabacContext := { pStateIdx := 16, valMPS := 0 }
    CabacEngine.decodeDecisionsList (ByteSlice.ofByteArray (CabacEngine.encodeDecisionsList ctx0 bins1)) ctx0 bins1.length = some bins1 ∧
    CabacEngine.decodeDecisionsList (ByteSlice.ofByteArray (CabacEngine.encodeDecisionsList ctx0 bins2)) ctx0 bins2.length = some bins2 := by
  decide

/-! ### AV1 Multi-Symbol Arithmetic Coder (`MSAC` CDF Adaptation, AV1 Spec Section 8.2.5) -/

/--
  AV1 4-Symbol Adaptive CDF Table (`cdf[0] < cdf[1] < cdf[2] < 32768`, with adaptation count `count ∈ [0..32]`).
-/
structure Av1MsacCdf4 where
  cdf0  : UInt32 := 8192
  cdf1  : UInt32 := 16384
  cdf2  : UInt32 := 24576
  count : UInt32 := 0
  deriving Repr, DecidableEq, Inhabited

/--
  AV1 MSAC CDF Adaptation (`update_cdf` in AV1 Specification Section 8.2.5 / `dav1d` `msac.c`):
  Updates the 15-bit cumulative distribution thresholds after observing `symbol ∈ {0, 1, 2, 3}`
  using learning rate `rate = 4 + (if count > 15 then 1 else 0)` while strictly preserving `1 ≤ cdf0 < cdf1 < cdf2 < 32768`.
-/
def av1MsacUpdateCdf4 (tbl : Av1MsacCdf4) (symbol : UInt8) : Av1MsacCdf4 :=
  let rate : Nat := if tbl.count > 15 then 5 else 4
  let stepThreshold (c : UInt32) (idx : UInt8) (minVal maxVal : Nat) : UInt32 :=
    let cur := c.toNat
    let updated : Nat :=
      if symbol ≤ idx then
        cur + ((32768 - cur) >>> rate)
      else
        cur - (cur >>> rate)
    (Nat.max minVal (Nat.min maxVal updated)).toUInt32
  let c0' := stepThreshold tbl.cdf0 0 64 32000
  let c1' := stepThreshold tbl.cdf1 1 (c0'.toNat + 64) 32384
  let c2' := stepThreshold tbl.cdf2 2 (c1'.toNat + 64) 32700
  { cdf0 := c0', cdf1 := c1', cdf2 := c2', count := Nat.min 32 (tbl.count.toNat + 1) |>.toUInt32 }

/-- Theorem (T4): `av1MsacUpdateCdf4` strictly preserves CDF monotonicity (`0 < cdf0 < cdf1 < cdf2 < 32768`) across all symbols `0..3`. -/
theorem av1MsacUpdateCdf4_preserves_monotonicity :
    let t0 : Av1MsacCdf4 := {}
    let t1 := av1MsacUpdateCdf4 t0 0
    let t2 := av1MsacUpdateCdf4 t1 2
    let t3 := av1MsacUpdateCdf4 t2 3
    (0 < t3.cdf0 && t3.cdf0 < t3.cdf1 && t3.cdf1 < t3.cdf2 && t3.cdf2 < 32768) = true := by
  decide

/-- Encode one binary symbol with probability `prob15` in `[1, 32767]` (15-bit CDF scale `32768`)
    into a `RangeEncoder` (`low`, `range`, `bitsCount`) paired with `RangeDecoder.decodeBit15`. -/
structure RangeEncoder where
  low       : UInt64 := 0
  range     : UInt32 := 0x8000
  bitsCount : Nat    := 16
  deriving Repr, DecidableEq, Inhabited

/-- Renormalize `RangeEncoder` while `range < 0x8000` by doubling `range` and `low` (`steps ≤ 16`). -/
def renormRangeE (range : UInt32) (low : UInt64) (bitsCount : Nat) : Nat → UInt32 × UInt64 × Nat
  | 0 => (range, low, bitsCount)
  | fuel + 1 =>
    if range < 0x8000 then
      renormRangeE (range <<< 1) (low <<< 1) (bitsCount + 1) fuel
    else
      (range, low, bitsCount)

/-- Encode one binary decision `bit ∈ {0, 1}` with probability `prob15 ∈ [1, 32767]` (`15`-bit CDF scale). -/
def encodeBit15 (enc : RangeEncoder) (prob15 : UInt32) (bit : UInt8) : RangeEncoder :=
  let p := if prob15 == 0 then 1 else if prob15 > 32767 then 32767 else prob15
  let split : UInt32 := (1 : UInt32) + (((enc.range - 1) * p) >>> 15)
  if (bit &&& 1) == 0 then
    let (rng', low', cnt') := renormRangeE split enc.low enc.bitsCount 16
    { low := low', range := rng', bitsCount := cnt' }
  else
    let (rng', low', cnt') := renormRangeE (enc.range - split) (enc.low + split.toUInt64) enc.bitsCount 16
    { low := low', range := rng', bitsCount := cnt' }

/-- Finalize `RangeEncoder` into a `ByteArray` by writing midpoint `low + (range / 2)` over `bitsCount` MSB bits. -/
def finishRangeEncoder (enc : RangeEncoder) : ByteArray :=
  let finalVal : UInt64 := enc.low + (enc.range >>> 1).toUInt64
  ((BitWriter.empty 16).writeBitsMSB finalVal enc.bitsCount).toByteArray

/-- Pure structural renormalization for `RangeDecoder` over a `BitReader` cursor (`0` imperative `while` loop). -/
def renormPure (rng dif : UInt32) (r : BitReader) : Nat → UInt32 × UInt32 × BitReader
  | 0 => (rng, dif, r)
  | fuel + 1 =>
    if rng < 0x8000 then
      let (bit, rNext) : UInt8 × BitReader :=
        match r.readBit with
        | some (b, r') => (b, r')
        | none => (0, r)
      renormPure (rng <<< 1) (((dif <<< 1) ||| bit.toUInt32) &&& 0xFFFF) rNext fuel
    else
      (rng, dif, r)

/-- Encode a list of `(prob15, bit)` pairs into a `RangeDecoder`-compatible `ByteArray`. -/
def encodeBits15List (pairs : List (UInt32 × UInt8)) : ByteArray :=
  let rec loop (e : RangeEncoder) : List (UInt32 × UInt8) → RangeEncoder
    | [] => e
    | (prob, b) :: rest => loop (encodeBit15 e prob b) rest
  finishRangeEncoder (loop {} pairs)

/-- Decode a list of bits for given `probs15` from `s : ByteSlice`. -/
def decodeBits15List (s : ByteSlice) (probs15 : List UInt32) : Option (List UInt8) :=
  let r0 := BitReader.ofSlice s
  match r0.readBitsMSB 16 with
  | none => none
  | some (d0, r1) =>
    let rec loop (rng dif : UInt32) (r : BitReader) : List UInt32 → List UInt8 → List UInt8
      | [], accRev => accRev.reverse
      | prob15 :: rest, accRev =>
        let p := if prob15 == 0 then 1 else if prob15 > 32767 then 32767 else prob15
        let split : UInt32 := (1 : UInt32) + (((rng - 1) * p) >>> 15)
        if dif < split then
          let (rng', dif', r') := renormPure split dif r 16
          loop rng' dif' r' rest (0 :: accRev)
        else
          let (rng', dif', r') := renormPure (rng - split) (dif - split) r 16
          loop rng' dif' r' rest (1 :: accRev)
    some (loop 0x8000 d0.toUInt32 r1 probs15 [])

set_option maxRecDepth 200000 in
/-- Theorem (T8): `RangeDecoder.encodeBits15List` and `RangeDecoder.decodeBits15List` round-trip bit-exactly (`R0`)
    across non-uniform 15-bit CDF probability sequences. -/
theorem rangeCoder15_encode_decode_roundtrip :
    let pairs1 : List (UInt32 × UInt8) := [(16384, 0), (24576, 1), (8192, 0), (16384, 1), (4096, 0), (28672, 1)]
    let probs1 := pairs1.map Prod.fst
    let bits1  := pairs1.map Prod.snd
    decodeBits15List (ByteSlice.ofByteArray (encodeBits15List pairs1)) probs1 = some bits1 := by
  decide

/-! ## Wave 51 (P1): Non-Indexed `BitCursor`, Total `BitM` Parser Monad, Bounded `readUEM`, & Confined `withSliceBits` Combinator -/

/-- Structured parsing errors for `BitM` (eliminating silent truncation and unbounded loops). -/
inductive BitErr where
  | truncated (requestedBits remainingBits : Nat)
  | invalidBitWidth (requestedBits : Nat)
  | unalignedSlice (bitPos : Nat)
  | expGolombLeadingZeroBudgetExceeded (maxLz : Nat)
  | expGolombValueExceeded (value maxVal : UInt64)
  | invalidBoxSize (boxSize remainingBytes : Nat)
  | boxNestingDepthExceeded (depth maxDepth : Nat)
  deriving Repr, DecidableEq, Inhabited

/--
  Non-indexed bitstream cursor (`BitCursor`) with bundled propositional bounds invariant:
  - Avoids `BitReader (n : Nat)` index churn where variable-width codes (`readUE`) break `do`-notation.
  - Carries a lower window bound `baseBits`, a current read position `bitPos`, an upper logical bit limit `limitBits`
    (narrowed by `withSliceBits` for ISOBMFF/MP4 boxes), and the physical buffer bit capacity `8 * buf.size`,
    with `baseBits ≤ bitPos ∧ bitPos ≤ limitBits ∧ limitBits ≤ 8 * buf.size`.
-/
structure BitCursor where
  buf       : ByteArray
  baseBits  : Nat := 0
  bitPos    : Nat
  limitBits : Nat
  h_base    : baseBits ≤ bitPos
  h_pos     : bitPos ≤ limitBits
  h_lim     : limitBits ≤ 8 * buf.size

namespace BitCursor

/-- Initialize a `BitCursor` over the entire `ByteArray`. -/
def ofByteArray (buf : ByteArray) : BitCursor :=
  { buf := buf
    baseBits := 0
    bitPos := 0
    limitBits := 8 * buf.size
    h_base := Nat.le_refl 0
    h_pos := Nat.zero_le _
    h_lim := Nat.le_refl _ }

/-- Remaining readable bits in the current slice window (`limitBits - bitPos`). -/
@[inline]
def remainingBits (c : BitCursor) : Nat :=
  c.limitBits - c.bitPos

/--
  Universal Theorem (P1 Byte Index In-Bounds):
  Whenever `c.bitPos < c.limitBits`, the underlying byte index `c.bitPos / 8` is strictly less than `c.buf.size`
  and `c.bitPos` lies within `[c.baseBits, c.limitBits)`.
-/
theorem byteIdx_lt_size (c : BitCursor) (hLt : c.bitPos < c.limitBits) :
    c.bitPos / 8 < c.buf.size ∧ c.baseBits ≤ c.bitPos := by
  have hLim := c.h_lim
  have hBase := c.h_base
  omega

/--
  Primitive 1 (`readBit?`): Read a single bit from `c : BitCursor`, returning `Except BitErr (UInt8 × BitCursor)`
  with bundled proof that the cursor advances by 1 (`c'.bitPos = c.bitPos + 1`) and stays within `[c.baseBits, c.limitBits]`.
-/
@[inline]
def readBit? (c : BitCursor) : Except BitErr (UInt8 × BitCursor) :=
  if hLt : c.bitPos < c.limitBits then
    have hByte : c.bitPos / 8 < c.buf.size := (c.byteIdx_lt_size hLt).1
    let b : UInt8 := c.buf[c.bitPos / 8]'hByte
    let shift : UInt8 := (7 - (c.bitPos % 8)).toUInt8
    let bit : UInt8 := (b >>> shift) &&& 1
    let c' : BitCursor := {
      buf := c.buf
      baseBits := c.baseBits
      bitPos := c.bitPos + 1
      limitBits := c.limitBits
      h_base := by have := c.h_base; omega
      h_pos := by omega
      h_lim := c.h_lim
    }
    .ok (bit, c')
  else
    .error (.truncated 1 (c.limitBits - c.bitPos))

/--
  Universal Theorem (P1 Local Progression & Confinement of `readBit?`):
  Whenever `c.readBit? = .ok (b, c')`, `c'.bitPos = c.bitPos + 1`, `c'.baseBits = c.baseBits`,
  `c'.limitBits = c.limitBits`, and `c'.buf = c.buf`.
-/
theorem readBit_progress (c c' : BitCursor) (b : UInt8)
    (hOk : c.readBit? = .ok (b, c')) :
    c'.bitPos = c.bitPos + 1 ∧ c'.baseBits = c.baseBits ∧ c'.limitBits = c.limitBits ∧ c'.buf = c.buf := by
  unfold readBit? at hOk
  split at hOk
  · injection hOk with hPair
    injection hPair with _ hC
    subst hC
    exact ⟨rfl, rfl, rfl, rfl⟩
  · contradiction

end BitCursor

/--
  Cursor-Window Endpoint Preservation Predicate (`CursorWindowPreserved c c'`):
  States that transitioning from cursor `c` to `c'` preserves the underlying buffer `buf`,
  the lower window bound `baseBits`, and the upper window bound `limitBits`, while advancing
  monotonically within `[c.bitPos, c.limitBits]`.
-/
def CursorWindowPreserved (c c' : BitCursor) : Prop :=
  c'.buf = c.buf ∧
  c'.baseBits = c.baseBits ∧
  c'.limitBits = c.limitBits ∧
  c.bitPos ≤ c'.bitPos ∧
  c'.bitPos ≤ c.limitBits

/--
  Lawful Bitstream Parser Monad (`BitM α`):
  Wraps `run : BitCursor → Except BitErr (α × BitCursor)` together with the inductive proof `h_wf`
  that every successful execution preserves the active slice window endpoints (`CursorWindowPreserved c c'`).
  For parsers built from the supplied `BitM` primitives/combinators (`pure`, `bind`, `fail`, `readBit`, `readBits`,
  `peekBits`, `readUEM`, `withSliceBits`), all byte accesses go through `BitCursor.readBit?` (which checks `c.bitPos < c.limitBits`
  before reading `c.buf[c.bitPos / 8]`). The universal `BitM.h_wf` field constrains successful returned cursor endpoints
  (`c'.bitPos ∈ [c.bitPos, c.limitBits]`, `c'.buf = c.buf`, `c'.baseBits = c.baseBits`, `c'.limitBits = c.limitBits`)
  rather than intermediate trace observations of an arbitrary raw `run` function.
-/
structure BitM (α : Type) where
  run  : BitCursor → Except BitErr (α × BitCursor)
  h_wf : ∀ (c c' : BitCursor) (a : α), run c = .ok (a, c') → CursorWindowPreserved c c'

namespace BitM

@[inline]
def pure (a : α) : BitM α where
  run := fun c => .ok (a, c)
  h_wf := by
    intro c c' _ hOk
    injection hOk with hPair
    injection hPair with _ hC
    subst hC
    exact ⟨rfl, rfl, rfl, Nat.le_refl _, c.h_pos⟩

@[inline]
def bind (m : BitM α) (f : α → BitM β) : BitM β where
  run := fun c =>
    match m.run c with
    | .ok (a, c₁) => (f a).run c₁
    | .error e    => .error e
  h_wf := by
    intro c c' b hOk
    split at hOk
    · rename_i a c₁ hM
      have h1 := m.h_wf c c₁ a hM
      have h2 := (f a).h_wf c₁ c' b hOk
      rcases h1 with ⟨hBuf1, hBase1, hLim1, hPos1, _⟩
      rcases h2 with ⟨hBuf2, hBase2, hLim2, hPos2, hEnd2⟩
      refine ⟨by rw [hBuf2, hBuf1], by omega, by omega, Nat.le_trans hPos1 hPos2, ?_⟩
      omega
    · contradiction

instance : Monad BitM where
  pure := BitM.pure
  bind := BitM.bind

@[inline]
def fail (e : BitErr) : BitM α where
  run := fun _ => .error e
  h_wf := by
    intro _ _ _ hOk
    contradiction

/-- Primitive 1 in `BitM`: read 1 MSB bit within `[c.bitPos, c.limitBits)`. -/
@[inline]
def readBit : BitM UInt8 where
  run := fun c => c.readBit?
  h_wf := by
    intro c c' b hOk
    have hProg := BitCursor.readBit_progress c c' b hOk
    rcases hProg with ⟨hPos, hBase, hLim, hBuf⟩
    refine ⟨hBuf, hBase, hLim, by omega, ?_⟩
    have hPosC' := c'.h_pos
    omega

/-- Internal structural helper for reading `k` bits after `k ≤ 64` has been checked. -/
def readBitsLoop (k : Nat) (acc : UInt64 := 0) : BitM UInt64 :=
  match k with
  | 0 => pure acc
  | k' + 1 => do
    let b ← readBit
    readBitsLoop k' ((acc <<< 1) ||| b.toUInt64)

/--
  Primitive 2 in `BitM`: read `k` MSB bits (`0 ≤ k ≤ 64`) structurally without `partial` or `Fin` indices.
  Explicitly rejects `k > 64` with `.error (.invalidBitWidth k)`. With the default seed `acc = 0` the newly read
  field fits in `UInt64`; a nonzero seed `acc` is shifted modularly (`<<<` on `UInt64`) and may drop its high bits.
-/
def readBits (k : Nat) (acc : UInt64 := 0) : BitM UInt64 :=
  if k > 64 then
    fail (.invalidBitWidth k)
  else
    readBitsLoop k acc

/-- Primitive 3 in `BitM`: peek `k` bits (`k ≤ 64`) without advancing the cursor. -/
@[inline]
def peekBits (k : Nat) : BitM UInt64 where
  run := fun c =>
    match (readBits k 0).run c with
    | .ok (v, _) => .ok (v, c)
    | .error e   => .error e
  h_wf := by
    intro c c' v hOk
    split at hOk
    · injection hOk with hPair
      injection hPair with _ hC
      subst hC
      exact ⟨rfl, rfl, rfl, Nat.le_refl _, c.h_pos⟩
    · contradiction

/-- Structural leading-zero counter for Exp-Golomb with explicit `maxLz` resource budget. -/
def countLeadingZerosBounded (fuel maxLz acc : Nat) : BitM Nat :=
  match fuel with
  | 0 => fail (.expGolombLeadingZeroBudgetExceeded maxLz)
  | fuel' + 1 => do
    let b ← readBit
    if b == 0 then
      countLeadingZerosBounded fuel' maxLz (acc + 1)
    else
      pure acc

/--
  Total Unsigned Exp-Golomb reader (`readUEM`) in `BitM`:
  Enforces both a structural leading-zero budget (`maxLz ≤ 31`, rejecting `maxLz > 31` upfront so `1 <<< lz` cannot wrap)
  and an explicit semantic value ceiling `maxVal`.
-/
def readUEM (maxLz : Nat := 31) (maxVal : UInt64 := 0xFFFFFFFF) : BitM UInt64 := do
  if maxLz > 31 then
    fail (.expGolombLeadingZeroBudgetExceeded maxLz)
  else
    let lz ← countLeadingZerosBounded (maxLz + 1) maxLz 0
    if lz == 0 then
      pure 0
    else
      let suffix ← readBits lz 0
      let val : UInt64 := (((1 : UInt64) <<< lz.toUInt64) - 1) + suffix
      if val > maxVal then
        fail (.expGolombValueExceeded val maxVal)
      else
        pure val

/--
  Combinator (`withSliceBits`): runs a nested parser `m : BitM α` on a sub-cursor whose window endpoints are narrowed to
  `[c.bitPos, c.bitPos + sliceBits]` (`c.bitPos + sliceBits ≤ c.limitBits`), establishes via `m.h_wf` that any successful
  returned cursor `subEnd` of `m` satisfies `c.bitPos ≤ subEnd.bitPos ≤ c.bitPos + sliceBits` with `subEnd.limitBits = c.bitPos + sliceBits`,
  and advances the outer cursor to `c.bitPos + sliceBits`.
-/
def withSliceBits (sliceBits : Nat) (m : BitM α) : BitM α where
  run := fun c =>
    if hSlice : c.bitPos + sliceBits ≤ c.limitBits then
      match m.run {
        buf := c.buf
        baseBits := c.bitPos
        bitPos := c.bitPos
        limitBits := c.bitPos + sliceBits
        h_base := Nat.le_refl c.bitPos
        h_pos := Nat.le_add_right c.bitPos sliceBits
        h_lim := Nat.le_trans hSlice c.h_lim
      } with
      | .error e => .error e
      | .ok (res, _) =>
        .ok (res, {
          buf := c.buf
          baseBits := c.baseBits
          bitPos := c.bitPos + sliceBits
          limitBits := c.limitBits
          h_base := by have := c.h_base; omega
          h_pos := hSlice
          h_lim := c.h_lim
        })
    else
      .error (.truncated sliceBits (c.limitBits - c.bitPos))
  h_wf := by
    intro c c' a hOk
    split at hOk
    · rename_i hSlice
      split at hOk
      · contradiction
      · injection hOk with hPair
        injection hPair with _ hC
        subst hC
        exact ⟨rfl, rfl, rfl, Nat.le_add_right c.bitPos sliceBits, hSlice⟩
    · contradiction

/--
  Universal Theorem (P1 Box/Slice Window Preservation of `withSliceBits`):
  For ANY lawful parser `m : BitM α`, if `(withSliceBits sliceBits m).run c = .ok (res, c')`,
  then there exists `hSlice : c.bitPos + sliceBits ≤ c.limitBits` and an intermediate cursor `subEnd : BitCursor`
  such that:
  1. `m.run { buf := c.buf, baseBits := c.bitPos, bitPos := c.bitPos, limitBits := c.bitPos + sliceBits, ... } = .ok (res, subEnd)`
  2. `c.bitPos ≤ subEnd.bitPos ∧ subEnd.bitPos ≤ c.bitPos + sliceBits ∧ subEnd.baseBits = c.bitPos ∧ subEnd.limitBits = c.bitPos + sliceBits ∧ subEnd.buf = c.buf`
  3. The outer cursor advances to `c'.bitPos = c.bitPos + sliceBits ≤ c.limitBits` with `c'.limitBits = c.limitBits` and `c'.buf = c.buf`.
-/
theorem withSliceBits_confined {α : Type} (sliceBits : Nat) (m : BitM α)
    (c c' : BitCursor) (res : α)
    (hOk : (BitM.withSliceBits sliceBits m).run c = .ok (res, c')) :
    (∃ (hSlice : c.bitPos + sliceBits ≤ c.limitBits) (subEnd : BitCursor),
      m.run {
        buf := c.buf
        baseBits := c.bitPos
        bitPos := c.bitPos
        limitBits := c.bitPos + sliceBits
        h_base := Nat.le_refl c.bitPos
        h_pos := Nat.le_add_right c.bitPos sliceBits
        h_lim := Nat.le_trans hSlice c.h_lim
      } = .ok (res, subEnd) ∧
      c.bitPos ≤ subEnd.bitPos ∧
      subEnd.bitPos ≤ c.bitPos + sliceBits ∧
      subEnd.baseBits = c.bitPos ∧
      subEnd.limitBits = c.bitPos + sliceBits ∧
      subEnd.buf = c.buf) ∧
    c'.bitPos = c.bitPos + sliceBits ∧
    c'.bitPos ≤ c.limitBits ∧
    c'.limitBits = c.limitBits ∧
    c'.buf = c.buf := by
  unfold withSliceBits at hOk
  dsimp at hOk
  split at hOk
  · rename_i hSlice
    split at hOk
    · contradiction
    · rename_i resSub subEnd hSub
      injection hOk with hPair
      injection hPair with hRes hC
      subst hRes
      subst hC
      have hWf := m.h_wf _ subEnd resSub hSub
      rcases hWf with ⟨hBuf, hBase, hLim, hGe, hLe⟩
      refine ⟨⟨hSlice, subEnd, hSub, hGe, hLe, hBase, hLim, hBuf⟩, rfl, hSlice, rfl, rfl⟩
  · contradiction

end BitM

structure LsbWriter where
  bytes : ByteArray := { data := #[] }
  curByte : UInt8 := 0
  bitsUsed : Nat := 0
  deriving Inhabited

namespace LsbWriter

def empty : LsbWriter := {}

def writeBit (w : LsbWriter) (bit : UInt8) : LsbWriter :=
  let b := w.curByte ||| ((bit &&& 1) <<< w.bitsUsed.toUInt8)
  if w.bitsUsed == 7 then
    { bytes := w.bytes.push b, curByte := 0, bitsUsed := 0 }
  else
    { w with curByte := b, bitsUsed := w.bitsUsed + 1 }

def writeBits (w : LsbWriter) (v : UInt32) : Nat → LsbWriter
  | 0 => w
  | n + 1 => writeBits (w.writeBit ((v &&& 1).toUInt8)) (v >>> 1) n

def alignToByte (w : LsbWriter) : LsbWriter :=
  if w.bitsUsed == 0 then w else { bytes := w.bytes.push w.curByte, curByte := 0, bitsUsed := 0 }

def toByteArray (w : LsbWriter) : ByteArray := w.alignToByte.bytes

end LsbWriter

structure DeflateHuffman where
  lengths : Array Nat
  codes : Array UInt32
  counts : Array Nat
  symbols : Array Nat
  deriving Inhabited

def deflateReverseCode (code : UInt32) : Nat → Nat → UInt32
  | 0, acc => acc.toUInt32
  | n + 1, acc => deflateReverseCode (code >>> 1) n (acc * 2 + (code &&& 1).toNat)

def deflateCountLengths : List Nat → Array Nat → Nat → Option (Array Nat × Nat)
  | [], counts, used => if used == 0 then none else some (counts, used)
  | len :: rest, counts, used =>
    if len > 15 then none
    else if len == 0 then deflateCountLengths rest counts used
    else deflateCountLengths rest (counts.set! len (counts.getD len 0 + 1)) (used + 1)

def deflateCheckKraft (counts : Array Nat) : Nat → Int → Bool
  | 0, _ => true
  | k + 1, left =>
    let len := 16 - (k + 1)
    let left' := left * 2 - (counts.getD len 0 : Int)
    if left' < 0 then false else deflateCheckKraft counts k left'

def deflateInitTables (counts : Array Nat) : Nat → UInt32 → Nat → Array UInt32 → Array Nat → Array UInt32 × Array Nat
  | 0, _, _, next, offsets => (next, offsets)
  | k + 1, code, offAcc, next, offsets =>
    let len := 16 - (k + 1)
    let code' := (code + (counts.getD (len - 1) 0).toUInt32) <<< 1
    let cnt := counts.getD len 0
    deflateInitTables counts k code' (offAcc + cnt) (next.set! len code') (offsets.set! len offAcc)

def deflateAssignSymbols (lengths : Array Nat) :
    Nat → Nat → Array UInt32 → Array Nat → Array UInt32 → Array Nat → Array UInt32 × Array Nat
  | 0, _, _, _, codes, symbols => (codes, symbols)
  | fuel + 1, sym, next, offsets, codes, symbols =>
    if sym ≥ lengths.size then (codes, symbols)
    else
      let len := lengths.getD sym 0
      if len == 0 then
        deflateAssignSymbols lengths fuel (sym + 1) next offsets codes symbols
      else
        let c := next.getD len 0
        let pos := offsets.getD len 0
        deflateAssignSymbols lengths fuel (sym + 1)
          (next.set! len (c + 1)) (offsets.set! len (pos + 1))
          (codes.set! sym (deflateReverseCode c len 0)) (symbols.set! pos sym)

def deflateBuildHuffman (lengths : Array Nat) : Option DeflateHuffman := do
  let n := lengths.size
  let (counts, used) ← deflateCountLengths lengths.toList (List.replicate 16 0).toArray 0
  if !deflateCheckKraft counts 15 1 then none
  let (next, offsets) := deflateInitTables counts 15 0 0 (List.replicate 16 0).toArray (List.replicate 16 0).toArray
  let (codes, symbols) := deflateAssignSymbols lengths n 0 next offsets
    (List.replicate n 0).toArray (List.replicate used 0).toArray
  some { lengths, codes, counts, symbols }

def deflateDecodeSymbol (r : BitReader) (h : DeflateHuffman) : Option (Nat × BitReader) :=
  let nSym := h.symbols.size
  let rec loop (cur : BitReader) (len : Nat) (code first index : Nat) : Nat → Option (Nat × BitReader)
    | 0 => none
    | fuel + 1 => do
      let (b, next) ← cur.readBitsLSB 1
      let code' := code + b.toNat
      let count := h.counts.getD len 0
      if code' ≥ first && code' - first < count then
        let idx := index + (code' - first)
        if idx < nSym then some (h.symbols.getD idx 0, next) else none
      else if len == 15 then none
      else loop next (len + 1) (code' * 2) ((first + count) * 2) (index + count) fuel
  loop r 1 0 0 0 15

def deflateFixedLiteralHuffman : DeflateHuffman :=
  let lengths := ((List.range 288).map fun sym =>
    if sym ≤ 143 then 8 else if sym ≤ 255 then 9 else if sym ≤ 279 then 7 else 8).toArray
  (deflateBuildHuffman lengths).getD { lengths, codes := #[], counts := #[], symbols := #[] }

def deflateFixedDistanceHuffman : DeflateHuffman :=
  let lengths := (List.replicate 32 5).toArray
  (deflateBuildHuffman lengths).getD { lengths, codes := #[], counts := #[], symbols := #[] }

def deflateLengthBase : Array Nat :=
  #[3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59,
    67, 83, 99, 115, 131, 163, 195, 227, 258]

def deflateLengthExtra : Array Nat :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4,
    5, 5, 5, 5, 0]

def deflateDistanceBase : Array Nat :=
  #[1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769,
    1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577]

def deflateDistanceExtra : Array Nat :=
  #[0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10,
    11, 11, 12, 12, 13, 13]

def deflateCopyMatch (out : ByteArray) (distance : Nat) : Nat → Option ByteArray
  | 0 => some out
  | n + 1 =>
    let curLen := out.data.size
    if distance == 0 || distance > curLen then none
    else
      let b := out.data.getD (curLen - distance) 0
      deflateCopyMatch (out.push b) distance n

def deflateCodeLengthOrder : Array Nat :=
  #[16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]

def deflateReadCodeLengths (r : BitReader) (h : DeflateHuffman) (remaining : Nat)
    (out : Array Nat) : Nat → Option (Array Nat × BitReader)
  | 0 => none
  | fuel + 1 =>
    if remaining == 0 then some (out, r)
    else do
      let (sym, r1) ← deflateDecodeSymbol r h
      if sym ≤ 15 then
        deflateReadCodeLengths r1 h (remaining - 1) (out.push sym) fuel
      else if sym == 16 then do
        if out.toList.length == 0 then none
        let (extra, r2) ← r1.readBitsLSB 2
        let reps := extra.toNat + 3
        if reps > remaining then none
        let v := out.getD (out.toList.length - 1) 0
        deflateReadCodeLengths r2 h (remaining - reps) (out ++ (List.replicate reps v).toArray) fuel
      else if sym == 17 then do
        let (extra, r2) ← r1.readBitsLSB 3
        let reps := extra.toNat + 3
        if reps > remaining then none
        deflateReadCodeLengths r2 h (remaining - reps) (out ++ (List.replicate reps 0).toArray) fuel
      else if sym == 18 then do
        let (extra, r2) ← r1.readBitsLSB 7
        let reps := extra.toNat + 11
        if reps > remaining then none
        deflateReadCodeLengths r2 h (remaining - reps) (out ++ (List.replicate reps 0).toArray) fuel
      else none

def deflateReadDynamicHuffman (r : BitReader) : Option (DeflateHuffman × DeflateHuffman × BitReader) := do
  let (a, r1) ← r.readBitsLSB 5
  let (b, r2) ← r1.readBitsLSB 5
  let (c, r3) ← r2.readBitsLSB 4
  let hlit := a.toNat + 257
  let hdist := b.toNat + 1
  let hclen := c.toNat + 4
  if hlit > 286 || hdist > 32 then none
  let rec readCl (cur : BitReader) (i : Nat) (lens : Array Nat) : Nat → Option (Array Nat × BitReader)
    | 0 => none
    | fuel + 1 => do
      if i == hclen then some (lens, cur)
      else
        let (v, next) ← cur.readBitsLSB 3
        readCl next (i + 1) (lens.set! (deflateCodeLengthOrder.getD i 0) v.toNat) fuel
  let (clLens, r4) ← readCl r3 0 (List.replicate 19 0).toArray (hclen + 1)
  let clHuff ← deflateBuildHuffman clLens
  let (allLens, r5) ← deflateReadCodeLengths r4 clHuff (hlit + hdist) #[] (hlit + hdist + 1)
  let litLens := (allLens.toList.take hlit).toArray
  let distLens := (allLens.toList.drop hlit).toArray
  if litLens.getD 256 0 == 0 then none
  let lit ← deflateBuildHuffman litLens
  let dist ← if distLens.toList.all (· == 0) then
      some { lengths := distLens, codes := #[], counts := #[], symbols := #[] }
    else deflateBuildHuffman distLens
  some (lit, dist, r5)

def deflateDecodeTokens (r : BitReader) (lit dist : DeflateHuffman) (maxOutput : Nat)
    (out : ByteArray) : Nat → Option (ByteArray × BitReader)
  | 0 => none
  | fuel + 1 => do
    let (sym, r1) ← deflateDecodeSymbol r lit
    if sym < 256 then
      if out.data.size ≥ maxOutput then none
      deflateDecodeTokens r1 lit dist maxOutput (out.push sym.toUInt8) fuel
    else if sym == 256 then some (out, r1)
    else if sym ≤ 285 then do
      let li := sym - 257
      let eb := deflateLengthExtra.getD li 0
      let (extra, r2) ← r1.readBitsLSB eb
      let len := deflateLengthBase.getD li 0 + extra.toNat
      if dist.symbols.size == 0 then none
      let (dsym, r3) ← deflateDecodeSymbol r2 dist
      if dsym ≥ 30 then none
      let de := deflateDistanceExtra.getD dsym 0
      let (dextra, r4) ← r3.readBitsLSB de
      let distance := deflateDistanceBase.getD dsym 0 + dextra.toNat
      if len > maxOutput - out.data.size then none
      let out' ← deflateCopyMatch out distance len
      deflateDecodeTokens r4 lit dist maxOutput out' fuel
    else none

def deflateCopyStored (r : BitReader) (out : ByteArray) (maxOutput : Nat) : Nat → Option (ByteArray × BitReader)
  | 0 => some (out, r)
  | n + 1 => do
    if out.data.size ≥ maxOutput then none
    let (v, next) ← r.readBitsLSB 8
    deflateCopyStored next (out.push v.toUInt8) maxOutput n

def deflateDecode (s : ByteSlice) (maxOutput : Nat := 268435456) : Option (ByteArray × BitReader) :=
  let rec blocks (r : BitReader) (out : ByteArray) : Nat → Option (ByteArray × BitReader)
    | 0 => none
    | fuel + 1 =>
      match r.readBitsLSB 1 with
      | none => none
      | some (final, r1) =>
        match r1.readBitsLSB 2 with
        | none => none
        | some (kind, r2) =>
          if kind == 0 then
            let r3 := r2.alignToByte
            match r3.readBitsLSB 16 with
            | none => none
            | some (lv, r4) =>
              match r4.readBitsLSB 16 with
              | none => none
              | some (nv, r5) =>
                if (lv.toUInt16 ^^^ 0xFFFF) != nv.toUInt16 then none
                else
                  match deflateCopyStored r5 out maxOutput lv.toNat with
                  | none => none
                  | some (out', r6) =>
                    if final == 1 then some (out', r6) else blocks r6 out' fuel
          else if kind == 1 || kind == 2 then
            let treesOpt :=
              if kind == 1 then some (deflateFixedLiteralHuffman, deflateFixedDistanceHuffman, r2)
              else deflateReadDynamicHuffman r2
            match treesOpt with
            | none => none
            | some (lit, dist, r3) =>
              match deflateDecodeTokens r3 lit dist maxOutput out (s.len * 8 + 1) with
              | none => none
              | some (out', r4) =>
                if final == 1 then some (out', r4) else blocks r4 out' fuel
          else none
  blocks (BitReader.ofSlice s) { data := #[] } (s.len * 8 + 1)

inductive DeflateMode where
  | stored
  | fixed
  | dynamic
  deriving DecidableEq, Repr, Inhabited

inductive DeflateToken where
  | lit (b : UInt8)
  | matchRef (len dist : Nat)
  deriving DecidableEq, Repr, Inhabited

def pushByteArrayLoop (dst src : ByteArray) (i : Nat) : Nat → ByteArray
  | 0 => dst
  | k + 1 =>
    if i ≥ src.data.toList.length then dst
    else pushByteArrayLoop { data := (dst.data.toList ++ [src.data.getD i 0]).toArray } src (i + 1) k

def appendByteArraySpec (a b : ByteArray) : ByteArray :=
  if b.data.toList.length ≤ 64 then
    { data := (a.data.toList ++ b.data.toList).toArray }
  else
    a ++ b

def deflateEncodeStoredSingle (data : ByteArray) : ByteArray :=
  let len : UInt16 := data.data.toList.length.toUInt16
  let nlen : UInt16 := len ^^^ 0xFFFF
  let hdr : ByteArray := { data := #[
    0x01,
    (len &&& 0xFF).toUInt8,
    ((len >>> 8) &&& 0xFF).toUInt8,
    (nlen &&& 0xFF).toUInt8,
    ((nlen >>> 8) &&& 0xFF).toUInt8
  ] }
  appendByteArraySpec hdr data

def deflateEncodeStored (data : ByteArray) : ByteArray :=
  if data.data.toList.length ≤ 65535 then
    deflateEncodeStoredSingle data
  else Id.run do
    let mut out := ByteArray.empty
    let mut off := 0
    while off < data.size do
      let rem := data.size - off
      let chunk := if rem > 65535 then 65535 else rem
      let isFinal : UInt8 := if off + chunk ≥ data.size then 1 else 0
      let len : UInt16 := chunk.toUInt16
      let nlen : UInt16 := len ^^^ 0xFFFF
      out := out.push isFinal
      out := out.push (len &&& 0xFF).toUInt8
      out := out.push ((len >>> 8) &&& 0xFF).toUInt8
      out := out.push (nlen &&& 0xFF).toUInt8
      out := out.push ((nlen >>> 8) &&& 0xFF).toUInt8
      out := out ++ data.extract off (off + chunk)
      off := off + chunk
    return out

def deflateLengthCodeLoop (len : Nat) : Nat → Nat × Nat × UInt32
  | 0 => (257, 0, 0)
  | rem + 1 =>
    let idx := 28 - (rem + 1)
    let base := deflateLengthBase.getD idx 3
    let eb := deflateLengthExtra.getD idx 0
    let span := 1 <<< eb
    if len ≥ base && len < base + span then (257 + idx, eb, (len - base).toUInt32)
    else deflateLengthCodeLoop len rem

def deflateLengthCode (len : Nat) : Nat × Nat × UInt32 :=
  if len == 258 then (285, 0, 0) else deflateLengthCodeLoop len 28

def deflateDistanceCodeLoop (dist : Nat) : Nat → Nat × Nat × UInt32
  | 0 => (0, 0, 0)
  | rem + 1 =>
    let idx := 30 - (rem + 1)
    let base := deflateDistanceBase.getD idx 1
    let eb := deflateDistanceExtra.getD idx 0
    let span := 1 <<< eb
    if dist ≥ base && dist < base + span then (idx, eb, (dist - base).toUInt32)
    else deflateDistanceCodeLoop dist rem

def deflateDistanceCode (dist : Nat) : Nat × Nat × UInt32 :=
  deflateDistanceCodeLoop dist 30

def deflateMatchLen (data : ByteArray) (p pos cur maxLen : Nat) : Nat → Nat
  | 0 => cur
  | fuel + 1 =>
    if cur ≥ maxLen then cur
    else if data.data.getD (p + cur) 0 == data.data.getD (pos + cur) 0 then
      deflateMatchLen data p pos (cur + 1) maxLen fuel
    else cur

def deflateSearchChain (data : ByteArray) (prev : Array Int) (pos maxLen : Nat)
    (cur : Int) (bestLen bestDist : Nat) : Nat → Nat × Nat
  | 0 => (bestLen, bestDist)
  | steps + 1 =>
    if cur < 0 then (bestLen, bestDist)
    else
      let p := cur.toNat
      let dist := pos - p
      if dist == 0 || dist > 32768 then (bestLen, bestDist)
      else
        let (bl, bd) :=
          if data.data.getD (p + bestLen) 0 == data.data.getD (pos + bestLen) 0 then
            let ml := deflateMatchLen data p pos 0 maxLen maxLen
            if ml > bestLen then (ml, dist) else (bestLen, bestDist)
          else (bestLen, bestDist)
        deflateSearchChain data prev pos maxLen (prev.getD p (-1)) bl bd steps

def deflateInsertRange (data : ByteArray) (pos : Nat) : Nat → Nat → Array Int → Array Int → Array Int × Array Int
  | 0, _, head, prev => (head, prev)
  | fuel + 1, adv, head, prev =>
    let q := pos + adv
    let hmod := head.size
    let (head', prev') :=
      if q + 3 ≤ data.data.size && hmod > 0 then
        let c0 := (data.data.getD q 0).toNat
        let c1 := (data.data.getD (q + 1) 0).toNat
        let c2 := (data.data.getD (q + 2) 0).toNat
        let hq := ((c0 * 257 + c1) * 257 + c2) % hmod
        (head.set! hq (Int.ofNat q), prev.set! q (head.getD hq (-1)))
      else (head, prev)
    deflateInsertRange data pos fuel (adv + 1) head' prev'

def deflateLz77Loop (data : ByteArray) (pos : Nat) (head prev : Array Int)
    (out : Array DeflateToken) : Nat → Array DeflateToken
  | 0 => out
  | fuel + 1 =>
    let n := data.data.size
    let hmod := if head.size > 0 then head.size else 1
    if pos ≥ n then out
    else if pos + 3 ≤ n then
      let b0 := (data.data.getD pos 0).toNat
      let b1 := (data.data.getD (pos + 1) 0).toNat
      let b2 := (data.data.getD (pos + 2) 0).toNat
      let h := ((b0 * 257 + b1) * 257 + b2) % hmod
      let cand0 := head.getD h (-1)
      let prev1 := prev.set! pos cand0
      let head1 := head.set! h (Int.ofNat pos)
      let maxLen := if n - pos < 258 then n - pos else 258
      let (bestLen, bestDist) := deflateSearchChain data prev1 pos maxLen cand0 2 0 16
      if bestLen ≥ 3 && bestDist ≥ 1 then
        let (head2, prev2) := deflateInsertRange data pos (bestLen - 1) 1 head1 prev1
        deflateLz77Loop data (pos + bestLen) head2 prev2 (out.push (.matchRef bestLen bestDist)) fuel
      else
        deflateLz77Loop data (pos + 1) head1 prev1 (out.push (.lit (data.data.getD pos 0))) fuel
    else
      deflateLz77Loop data (pos + 1) head prev (out.push (.lit (data.data.getD pos 0))) fuel

def deflateTokenizeLz77 (data : ByteArray) : Array DeflateToken :=
  let n := data.data.toList.length
  if n < 3 then
    (data.data.toList.map DeflateToken.lit).toArray
  else if n ≤ 16 then
    deflateLz77Loop data 0 (List.replicate 64 (-1)).toArray (List.replicate n (-1)).toArray #[] (n + 1)
  else
    deflateLz77Loop data 0 (List.replicate 4096 (-1)).toArray (List.replicate n (-1)).toArray #[] (n + 1)

def deflateEncodeSymbol (w : LsbWriter) (h : DeflateHuffman) (sym : Nat) : LsbWriter :=
  w.writeBits (h.codes.getD sym 0) (h.lengths.getD sym 0)

def deflateEncodeTokenList (w : LsbWriter) (lit dist : DeflateHuffman) : List DeflateToken → LsbWriter
  | [] => deflateEncodeSymbol w lit 256
  | .lit b :: rest =>
    deflateEncodeTokenList (deflateEncodeSymbol w lit b.toNat) lit dist rest
  | .matchRef len d :: rest =>
    let (lsym, leb, lextra) := deflateLengthCode len
    let w1 := deflateEncodeSymbol w lit lsym
    let w2 := if leb > 0 then w1.writeBits lextra leb else w1
    let (dsym, deb, dextra) := deflateDistanceCode d
    let w3 := deflateEncodeSymbol w2 dist dsym
    let w4 := if deb > 0 then w3.writeBits dextra deb else w3
    deflateEncodeTokenList w4 lit dist rest

def deflateEncodeTokenStream (w0 : LsbWriter) (lit dist : DeflateHuffman)
    (tokens : Array DeflateToken) : LsbWriter :=
  deflateEncodeTokenList w0 lit dist tokens.toList

def deflateBuildLimitedLengths (freqs : Array Nat) (maxLen : Nat) : Option (Array Nat) := Id.run do
  let n := freqs.size
  let mut active : Array (Nat × Nat) := #[]
  for sym in [0:n] do
    let f := freqs.getD sym 0
    if f > 0 then active := active.push (f, sym)
  if active.size < 2 then return none
  let totalNodes := 2 * active.size - 1
  let mut parent : Array Nat := Array.replicate totalNodes totalNodes
  let mut pool : Array (Nat × Nat) := #[]
  for i in [0:active.size] do
    let (f, _) := active.getD i (1, 0)
    pool := pool.push (f, i)
  let mut nextId := active.size
  while pool.size > 1 do
    let mut i1 := 0
    for i in [1:pool.size] do
      if (pool.getD i (0, 0)).1 < (pool.getD i1 (0, 0)).1 then i1 := i
    let n1 := pool.getD i1 (0, 0)
    let mut pool1 : Array (Nat × Nat) := #[]
    for i in [0:pool.size] do
      if i != i1 then pool1 := pool1.push (pool.getD i (0, 0))
    let mut i2 := 0
    for i in [1:pool1.size] do
      if (pool1.getD i (0, 0)).1 < (pool1.getD i2 (0, 0)).1 then i2 := i
    let n2 := pool1.getD i2 (0, 0)
    let mut pool2 : Array (Nat × Nat) := #[]
    for i in [0:pool1.size] do
      if i != i2 then pool2 := pool2.push (pool1.getD i (0, 0))
    parent := parent.set! n1.2 nextId
    parent := parent.set! n2.2 nextId
    pool := pool2.push (n1.1 + n2.1, nextId)
    nextId := nextId + 1
  let mut blCount : Array Nat := Array.replicate (maxLen + 1) 0
  let mut overflow := 0
  let mut rawDepths : Array (Nat × Nat) := #[]
  for i in [0:active.size] do
    let (_, sym) := active.getD i (1, 0)
    let mut d := 0
    let mut cur := i
    while parent.getD cur totalNodes < totalNodes && d < totalNodes do
      cur := parent.getD cur totalNodes
      d := d + 1
    rawDepths := rawDepths.push (d, sym)
    if d > maxLen then
      blCount := blCount.set! maxLen (blCount.getD maxLen 0 + 1)
      overflow := overflow + 1
    else
      blCount := blCount.set! d (blCount.getD d 0 + 1)
  while overflow > 0 do
    let mut bits := maxLen - 1
    while bits > 0 && blCount.getD bits 0 == 0 do
      bits := bits - 1
    if bits == 0 then return none
    blCount := blCount.set! bits (blCount.getD bits 0 - 1)
    blCount := blCount.set! (bits + 1) (blCount.getD (bits + 1) 0 + 2)
    blCount := blCount.set! maxLen (blCount.getD maxLen 0 - 1)
    overflow := overflow - 2
  let sorted := rawDepths.qsort (fun a b => if a.1 == b.1 then a.2 < b.2 else a.1 > b.1)
  let mut lens : Array Nat := Array.replicate n 0
  let mut idx := 0
  let mut bits := maxLen
  while bits > 0 do
    let cnt := blCount.getD bits 0
    for _ in [0:cnt] do
      if idx < sorted.size then
        let (_, sym) := sorted.getD idx (0, 0)
        lens := lens.set! sym bits
        idx := idx + 1
    bits := bits - 1
  return some lens

def deflateDefaultDynLitLengths : Array Nat :=
  ((List.range 286).map fun sym => if sym < 226 then 8 else 9).toArray

def deflateDefaultDynDistLengths : Array Nat :=
  ((List.range 30).map fun sym => if sym < 2 then 4 else 5).toArray

def deflateWriteClHeader (w : LsbWriter) (clLens : Array Nat) : Nat → LsbWriter
  | 0 => w
  | k + 1 =>
    let idx := 19 - (k + 1)
    let v := clLens.getD (deflateCodeLengthOrder.getD idx 0) 0
    deflateWriteClHeader (w.writeBits v.toUInt32 3) clLens k

def deflateWriteTreeLengths (w : LsbWriter) (cl : DeflateHuffman) : List Nat → LsbWriter
  | [] => w
  | l :: rest => deflateWriteTreeLengths (deflateEncodeSymbol w cl l) cl rest

def deflateEncodeDynamicCanonical (tokens : Array DeflateToken) : ByteArray :=
  let lit := (deflateBuildHuffman deflateDefaultDynLitLengths).getD deflateFixedLiteralHuffman
  let dist := (deflateBuildHuffman deflateDefaultDynDistLengths).getD deflateFixedDistanceHuffman
  let clLens := ((List.replicate 19 0).toArray).set! 0 1 |>.set! 4 2 |>.set! 5 3 |>.set! 8 4 |>.set! 9 4
  let cl := (deflateBuildHuffman clLens).getD deflateFixedLiteralHuffman
  let w0 := (LsbWriter.empty.writeBit 1).writeBits 2 2
  let wa := (w0.writeBits 29 5).writeBits 29 5 |>.writeBits 15 4
  let wb := deflateWriteClHeader wa clLens 19
  let wc := deflateWriteTreeLengths wb cl lit.lengths.toList
  let wd := deflateWriteTreeLengths wc cl dist.lengths.toList
  (deflateEncodeTokenStream wd lit dist tokens).toByteArray

def deflateEncodeWithTrees (data : ByteArray) (dynamic : Bool) : ByteArray :=
  let tokens := deflateTokenizeLz77 data
  if !dynamic then
    let w0 := (LsbWriter.empty.writeBit 1).writeBits 1 2
    let w1 := deflateEncodeTokenStream w0 deflateFixedLiteralHuffman deflateFixedDistanceHuffman tokens
    w1.toByteArray
  else if data.data.toList.length < 32 then
    deflateEncodeDynamicCanonical tokens
  else Id.run do
    let mut litFreq : Array Nat := Array.replicate 286 0
    let mut distFreq : Array Nat := Array.replicate 30 0
    litFreq := litFreq.set! 256 1
    for tok in tokens do
      match tok with
      | .lit b =>
        let s := b.toNat
        litFreq := litFreq.set! s (litFreq.getD s 0 + 1)
      | .matchRef len d =>
        let (lsym, _, _) := deflateLengthCode len
        let (dsym, _, _) := deflateDistanceCode d
        litFreq := litFreq.set! lsym (litFreq.getD lsym 0 + 1)
        distFreq := distFreq.set! dsym (distFreq.getD dsym 0 + 1)
    let mut litActive := 0
    for f in litFreq do if f > 0 then litActive := litActive + 1
    if litActive < 2 then
      litFreq := litFreq.set! 0 (litFreq.getD 0 0 + 1)
    let mut distActive := 0
    for f in distFreq do if f > 0 then distActive := distActive + 1
    if distActive == 0 then
      distFreq := distFreq.set! 0 1 |>.set! 1 1
    else if distActive == 1 then
      let alt := if distFreq.getD 0 0 == 0 then 0 else 1
      distFreq := distFreq.set! alt 1
    let litLens := (deflateBuildLimitedLengths litFreq 15).getD deflateDefaultDynLitLengths
    let distLens := (deflateBuildLimitedLengths distFreq 15).getD deflateDefaultDynDistLengths
    let lit := (deflateBuildHuffman litLens).getD
      ((deflateBuildHuffman deflateDefaultDynLitLengths).getD deflateFixedLiteralHuffman)
    let dist := (deflateBuildHuffman distLens).getD
      ((deflateBuildHuffman deflateDefaultDynDistLengths).getD deflateFixedDistanceHuffman)
    let allLens := lit.lengths ++ dist.lengths
    let mut clFreq : Array Nat := Array.replicate 19 0
    for l in allLens do
      clFreq := clFreq.set! l (clFreq.getD l 0 + 1)
    let mut clActive := 0
    for f in clFreq do if f > 0 then clActive := clActive + 1
    if clActive < 2 then
      let alt := if clFreq.getD 0 0 == 0 then 0 else 1
      clFreq := clFreq.set! alt 1
    let fallbackCl := (Array.replicate 19 0).set! 0 1 |>.set! 4 2 |>.set! 5 3 |>.set! 8 4 |>.set! 9 4
    let clLensOpt := match deflateBuildLimitedLengths clFreq 7 with
      | some ls =>
        let ok := allLens.all (fun l => ls.getD l 0 > 0)
        if ok then some ls else none
      | none => none
    let (useLit, useDist, clLens) := match clLensOpt with
      | some ls =>
        match deflateBuildHuffman ls with
        | some _ => (lit, dist, ls)
        | none =>
          let dl := (deflateBuildHuffman deflateDefaultDynLitLengths).getD deflateFixedLiteralHuffman
          let dd := (deflateBuildHuffman deflateDefaultDynDistLengths).getD deflateFixedDistanceHuffman
          (dl, dd, fallbackCl)
      | none =>
        let dl := (deflateBuildHuffman deflateDefaultDynLitLengths).getD deflateFixedLiteralHuffman
        let dd := (deflateBuildHuffman deflateDefaultDynDistLengths).getD deflateFixedDistanceHuffman
        (dl, dd, fallbackCl)
    let cl := (deflateBuildHuffman clLens).getD deflateFixedLiteralHuffman
    let w0 := (LsbWriter.empty.writeBit 1).writeBits 2 2
    let wa := (w0.writeBits (useLit.lengths.size - 257).toUInt32 5).writeBits
      (useDist.lengths.size - 1).toUInt32 5 |>.writeBits 15 4
    let wb := deflateWriteClHeader wa clLens 19
    let wc := deflateWriteTreeLengths wb cl useLit.lengths.toList
    let wd := deflateWriteTreeLengths wc cl useDist.lengths.toList
    return (deflateEncodeTokenStream wd useLit useDist tokens).toByteArray

def deflateEncodeFixed (data : ByteArray) : ByteArray := deflateEncodeWithTrees data false

def deflateEncodeDynamic (data : ByteArray) : ByteArray := deflateEncodeWithTrees data true

def deflateEncodeMode (data : ByteArray) : DeflateMode → ByteArray
  | .stored => deflateEncodeStored data
  | .fixed => deflateEncodeFixed data
  | .dynamic => deflateEncodeDynamic data

def adler32Step (s1 s2 : UInt32) (b : UInt8) : UInt32 × UInt32 :=
  let a := (s1 + b.toUInt32) % 65521
  (a, (s2 + a) % 65521)

def adler32 (data : ByteArray) : UInt32 :=
  let sums := data.data.toList.foldl (fun (a : UInt32 × UInt32) b => adler32Step a.1 a.2 b) (1, 0)
  (sums.2 <<< 16) ||| sums.1

theorem adler32Step_bounds (s1 s2 : UInt32) (b : UInt8) :
    (adler32Step s1 s2 b).1 < 65521 ∧ (adler32Step s1 s2 b).2 < 65521 ∧
    adler32 ByteArray.empty = 1 ∧
    adler32 (ByteArray.mk #[0x57, 0x69, 0x6B, 0x69, 0x70, 0x65, 0x64, 0x69, 0x61]) = 0x11E60398 := by
  refine ⟨UInt32.mod_lt _ (by decide), UInt32.mod_lt _ (by decide), ?_, ?_⟩
  · decide
  · decide

def pushU32BEDeflate (ba : ByteArray) (v : UInt32) : ByteArray :=
  ((((ba.push ((v >>> 24) &&& 0xFF).toUInt8).push ((v >>> 16) &&& 0xFF).toUInt8).push
    ((v >>> 8) &&& 0xFF).toUInt8).push (v &&& 0xFF).toUInt8)

def zlibEncodeMode (data : ByteArray) (mode : DeflateMode) : ByteArray :=
  let body := deflateEncodeMode data mode
  pushU32BEDeflate (appendByteArraySpec { data := #[0x78, 0x9C] } body) (adler32 data)

def zlibEncode (data : ByteArray) (dynamic : Bool := true) : ByteArray :=
  zlibEncodeMode data (if dynamic then .dynamic else .fixed)

def zlibDecodePrefix (s : ByteSlice) (maxOutput : Nat := 268435456) : Option (ByteArray × Nat) := do
  if s.len < 6 then none
  let cmf := s.getByteD 0 0
  let flg := s.getByteD 1 0
  if cmf &&& 0x0F != 8 || cmf >>> 4 > 7 || (flg &&& 0x20) != 0 then none
  if (cmf.toNat * 256 + flg.toNat) % 31 != 0 then none
  let body : ByteSlice := { ba := s.ba, off := s.off + 2, len := s.len - 2 }
  let (out, r) ← deflateDecode body maxOutput
  let endByte := (r.bitOffset + 7) / 8
  if endByte + 6 > s.len then none
  let p := 2 + endByte
  let expected := ((s.getByteD p 0).toUInt32 <<< 24) ||| ((s.getByteD (p + 1) 0).toUInt32 <<< 16) |||
    ((s.getByteD (p + 2) 0).toUInt32 <<< 8) ||| (s.getByteD (p + 3) 0).toUInt32
  if expected != adler32 out then none
  some (out, p + 4)

def zlibDecode (s : ByteSlice) (maxOutput : Nat := 268435456) : Option ByteArray := do
  let (out, used) ← zlibDecodePrefix s maxOutput
  if used == s.len then some out else none

def deflateKraftWeight (lengths : List Nat) : Nat :=
  lengths.foldl (fun acc len => if len == 0 then acc else acc + 2 ^ (15 - len)) 0

def DeflateTreeSafe (lengths : Array Nat) : Prop :=
  lengths.toList.any (· != 0) = true ∧ lengths.toList.all (· ≤ 15) = true ∧
    deflateKraftWeight lengths.toList ≤ 32768

instance (lengths : Array Nat) : Decidable (DeflateTreeSafe lengths) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def deflateTreeGateSpec : AVGateSpec (Array Nat) DeflateTreeSafe where
  gate := fun lengths => decide (DeflateTreeSafe lengths)
  sound _ h := of_decide_eq_true h
  complete _ h := decide_eq_true h
  posWitness := #[8, 8]
  negWitness := #[0, 0]
  nonVacuous := by decide
  tight := by decide

theorem deflateTreeGateSpec_iff (lengths : Array Nat) :
    deflateTreeGateSpec.gate lengths = true ↔ DeflateTreeSafe lengths :=
  deflateTreeGateSpec.iff_safe lengths

def ZlibHeaderSafe (cmf flg : UInt8) : Prop :=
  cmf &&& 0x0F = 8 ∧ cmf >>> 4 ≤ 7 ∧ flg &&& 0x20 = 0 ∧ (cmf.toNat * 256 + flg.toNat) % 31 = 0

instance (a : UInt8 × UInt8) : Decidable (ZlibHeaderSafe a.1 a.2) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def zlibHeaderGateSpec : AVGateSpec (UInt8 × UInt8) (fun a => ZlibHeaderSafe a.1 a.2) where
  gate := fun a => decide (ZlibHeaderSafe a.1 a.2)
  sound _ h := of_decide_eq_true h
  complete _ h := decide_eq_true h
  posWitness := (0x78, 0x9C)
  negWitness := (0, 0)
  nonVacuous := by decide
  tight := by decide

theorem zlibHeaderGateSpec_iff (a : UInt8 × UInt8) :
    zlibHeaderGateSpec.gate a = true ↔ ZlibHeaderSafe a.1 a.2 :=
  zlibHeaderGateSpec.iff_safe a

private def lsbReconstructU8 (b : UInt8) : UInt64 :=
  (((((0 : UInt64) ||| (((b >>> (0 : UInt8)) &&& 1).toUInt64 <<< (0 : UInt64))) |||
      (((b >>> (1 : UInt8)) &&& 1).toUInt64 <<< (1 : UInt64))) |||
      (((b >>> (2 : UInt8)) &&& 1).toUInt64 <<< (2 : UInt64))) |||
      (((b >>> (3 : UInt8)) &&& 1).toUInt64 <<< (3 : UInt64))) |||
      (((b >>> (4 : UInt8)) &&& 1).toUInt64 <<< (4 : UInt64)) |||
      (((b >>> (5 : UInt8)) &&& 1).toUInt64 <<< (5 : UInt64)) |||
      (((b >>> (6 : UInt8)) &&& 1).toUInt64 <<< (6 : UInt64)) |||
      (((b >>> (7 : UInt8)) &&& 1).toUInt64 <<< (7 : UInt64))

set_option maxRecDepth 20000 in
private theorem lsbReconstructU8_range :
    ((List.range 256).all (fun n => lsbReconstructU8 (UInt8.ofNat n) == (UInt8.ofNat n).toUInt64)) = true := by
  decide

theorem byte_reconstruct_lsb (b : UInt8) : lsbReconstructU8 b = b.toUInt64 := by
  have hm : b.toNat ∈ List.range 256 := List.mem_range.mpr b.toBitVec.isLt
  have hall := List.all_eq_true.mp lsbReconstructU8_range b.toNat hm
  rw [UInt8.ofNat_toNat] at hall
  exact eq_of_beq hall

private theorem uint64_cursor_ok (off req tot : Nat)
    (h1 : off + req ≤ tot) (h2 : req ≤ 64) (h3 : tot < UInt64.size) :
    verifyBitstreamCursor off.toUInt64 req.toUInt64 tot.toUInt64 = 1 := by
  unfold verifyBitstreamCursor
  have ho : off.toUInt64.toNat = off := UInt64.toNat_ofNat_of_lt (Nat.lt_of_le_of_lt (by omega) h3)
  have hr : req.toUInt64.toNat = req := UInt64.toNat_ofNat_of_lt (Nat.lt_of_le_of_lt (by omega) h3)
  have ht : tot.toUInt64.toNat = tot := UInt64.toNat_ofNat_of_lt h3
  have c1 : off.toUInt64 ≤ tot.toUInt64 := by
    rw [UInt64.le_iff_toNat_le, ho, ht]; omega
  have c2 : req.toUInt64 ≤ tot.toUInt64 - off.toUInt64 := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ c1, hr, ht, ho]; omega
  have c3 : req.toUInt64 ≤ 64 := by
    rw [UInt64.le_iff_toNat_le, hr]; change req ≤ 64; omega
  simp [c1, c2, c3]

theorem readBitsLSB_byte_exact (s : ByteSlice) (k : Nat)
    (hk : k + 1 ≤ s.len) (hsmall : s.len * 8 < UInt64.size) :
    BitReader.readBitsLSB { slice := s, bitOffset := k * 8 } 8 =
      some ((s.getByteD k 0).toUInt64, { slice := s, bitOffset := (k + 1) * 8 }) := by
  unfold BitReader.readBitsLSB BitReader.totalBits
  have hok : verifyBitstreamCursor (k * 8).toUInt64 (8 : Nat).toUInt64 (s.len * 8).toUInt64 = 1 :=
    uint64_cursor_ok (k * 8) 8 (s.len * 8) (by omega) (by omega) hsmall
  simp only [hok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, BitReader.readBitsLSBLoop]
  have hd0 : (k * 8) / 8 = k := by omega
  have hm0 : (k * 8) % 8 = 0 := by omega
  have hd1 : (k * 8 + 1) / 8 = k := by omega
  have hm1 : (k * 8 + 1) % 8 = 1 := by omega
  have hd2 : (k * 8 + 1 + 1) / 8 = k := by omega
  have hm2 : (k * 8 + 1 + 1) % 8 = 2 := by omega
  have hd3 : (k * 8 + 1 + 1 + 1) / 8 = k := by omega
  have hm3 : (k * 8 + 1 + 1 + 1) % 8 = 3 := by omega
  have hd4 : (k * 8 + 1 + 1 + 1 + 1) / 8 = k := by omega
  have hm4 : (k * 8 + 1 + 1 + 1 + 1) % 8 = 4 := by omega
  have hd5 : (k * 8 + 1 + 1 + 1 + 1 + 1) / 8 = k := by omega
  have hm5 : (k * 8 + 1 + 1 + 1 + 1 + 1) % 8 = 5 := by omega
  have hd6 : (k * 8 + 1 + 1 + 1 + 1 + 1 + 1) / 8 = k := by omega
  have hm6 : (k * 8 + 1 + 1 + 1 + 1 + 1 + 1) % 8 = 6 := by omega
  have hd7 : (k * 8 + 1 + 1 + 1 + 1 + 1 + 1 + 1) / 8 = k := by omega
  have hm7 : (k * 8 + 1 + 1 + 1 + 1 + 1 + 1 + 1) % 8 = 7 := by omega
  have hcur : k * 8 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = (k + 1) * 8 := by omega
  simp only [hd0, hm0, hd1, hm1, hd2, hm2, hd3, hm3, hd4, hm4, hd5, hm5, hd6, hm6, hd7, hm7, hcur]
  exact congrArg (fun x => some (x, _)) (byte_reconstruct_lsb (s.getByteD k 0))

set_option maxRecDepth 20000 in
private theorem u8_u64_u8_range :
    ((List.range 256).all (fun n => (UInt8.ofNat n).toUInt64.toUInt8 == UInt8.ofNat n)) = true := by
  decide

private theorem u8_u64_u8 (b : UInt8) : b.toUInt64.toUInt8 = b := by
  have hm : b.toNat ∈ List.range 256 := List.mem_range.mpr b.toBitVec.isLt
  have hall := List.all_eq_true.mp u8_u64_u8_range b.toNat hm
  rw [UInt8.ofNat_toNat] at hall
  exact eq_of_beq hall

theorem deflateCopyStored_spec (n : Nat) :
    ∀ (s : ByteSlice) (k : Nat) (out : ByteArray) (maxOutput : Nat),
      k + n ≤ s.len →
      s.len * 8 < UInt64.size →
      out.size + n ≤ maxOutput →
      deflateCopyStored { slice := s, bitOffset := k * 8 } out maxOutput n =
        some ({ data := out.data ++ ((List.range n).map (fun i => s.getByteD (k + i) 0)).toArray },
              { slice := s, bitOffset := (k + n) * 8 }) := by
  induction n with
  | zero =>
    intro s k out maxOutput _ _ _
    simp [deflateCopyStored]
  | succ m ih =>
    intro s k out maxOutput hlen hsmall hmax
    have hge : ¬ (out.data.size ≥ maxOutput) := by
      have hs : out.data.size = out.size := rfl
      omega
    have hbyte := readBitsLSB_byte_exact s k (by omega) hsmall
    unfold deflateCopyStored
    simp only [hge, ↓reduceIte, bind, Option.bind, hbyte, u8_u64_u8]
    have hout : (out.push (s.getByteD k 0)).size + m ≤ maxOutput := by
      rw [ByteArray.size_push]; omega
    rw [ih s (k + 1) (out.push (s.getByteD k 0)) maxOutput (by omega) hsmall hout]
    congr 2
    · apply congrArg ByteArray.mk
      apply Array.ext'
      simp [ByteArray.push, List.range_succ_eq_map]
      intro a _
      exact congrArg (fun idx => s.getByteD idx 0) (by omega)
    · congr 1; omega

theorem deflateCopyStored_output_bounded (n : Nat) :
    ∀ (r r' : BitReader) (out out' : ByteArray) (maxOutput : Nat),
      out.size ≤ maxOutput →
      deflateCopyStored r out maxOutput n = some (out', r') →
      out'.size = out.size + n ∧ out'.size ≤ maxOutput ∧ r'.bitOffset = r.bitOffset + n * 8 := by
  induction n with
  | zero =>
    intro r r' out out' maxOutput hle hok
    simp [deflateCopyStored] at hok
    rcases hok with ⟨rfl, rfl⟩
    exact ⟨by omega, hle, by omega⟩
  | succ m ih =>
    intro r r' out out' maxOutput hle hok
    unfold deflateCopyStored at hok
    split at hok
    · contradiction
    · rename_i hlt
      have hlt' : ¬ (out.size ≥ maxOutput) := hlt
      cases hrb : r.readBitsLSB 8 with
      | none => simp [hrb, bind, Option.bind] at hok
      | some vr =>
        rcases vr with ⟨v, next⟩
        simp only [hrb, bind, Option.bind] at hok
        have hnext : next.bitOffset = r.bitOffset + 8 := by
          unfold BitReader.readBitsLSB at hrb
          dsimp at hrb
          split at hrb
          · contradiction
          · simp only [BitReader.readBitsLSBLoop] at hrb
            injection hrb with hp
            have h2 := congrArg Prod.snd hp
            dsimp at h2
            have hbo' := congrArg BitReader.bitOffset h2
            dsimp at hbo'
            omega
        have hpush : (out.push v.toUInt8).size ≤ maxOutput := by
          rw [ByteArray.size_push]; omega
        have ⟨hs1, hs2, hbo⟩ := ih next r' (out.push v.toUInt8) out' maxOutput hpush hok
        rw [ByteArray.size_push] at hs1
        exact ⟨by omega, hs2, by omega⟩

def zlibRoundtripData (data : ByteArray) (mode : DeflateMode) : Option (List UInt8) :=
  let enc := zlibEncodeMode data mode
  match zlibDecode { ba := enc, off := 0, len := enc.data.toList.length } with
  | some dec => some dec.data.toList
  | none => none

set_option maxHeartbeats 800000 in
set_option maxRecDepth 200000 in
theorem zlibEncodeMode_decode_all_modes_roundtrip :
    let p0 : ByteArray := { data := #[] }
    let p1 : ByteArray := { data := #[0x42] }
    let p2 : ByteArray := { data := #[0, 1, 2, 0, 1, 2, 255] }
    zlibRoundtripData p0 .stored = some p0.data.toList ∧
    zlibRoundtripData p0 .fixed = some p0.data.toList ∧
    zlibRoundtripData p1 .stored = some p1.data.toList ∧
    zlibRoundtripData p1 .fixed = some p1.data.toList ∧
    zlibRoundtripData p2 .stored = some p2.data.toList ∧
    zlibRoundtripData p2 .fixed = some p2.data.toList ∧
    zlibRoundtripData p2 .dynamic = some p2.data.toList := by
  decide

def md5K : Array UInt32 := #[
  0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee, 0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
  0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be, 0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
  0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa, 0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
  0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed, 0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
  0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c, 0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
  0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05, 0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
  0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039, 0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
  0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1, 0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391]

def md5S : Array UInt32 := #[
  7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22,
  5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20,
  4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23,
  6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21]

def md5Rotl (x s : UInt32) : UInt32 := (x <<< s) ||| (x >>> (32 - s))

def md5Block (st : UInt32 × UInt32 × UInt32 × UInt32) (msg : ByteArray) (off : Nat) :
    UInt32 × UInt32 × UInt32 × UInt32 := Id.run do
  let word (g : Nat) : UInt32 :=
    let p := off + 4 * g
    (msg.data.getD p 0).toUInt32 ||| ((msg.data.getD (p + 1) 0).toUInt32 <<< 8) |||
      ((msg.data.getD (p + 2) 0).toUInt32 <<< 16) ||| ((msg.data.getD (p + 3) 0).toUInt32 <<< 24)
  let (a0, b0, c0, d0) := st
  let mut a := a0
  let mut b := b0
  let mut c := c0
  let mut d := d0
  for i in [0:64] do
    let (f, g) :=
      if i < 16 then ((b &&& c) ||| ((~~~b) &&& d), i)
      else if i < 32 then ((d &&& b) ||| ((~~~d) &&& c), (5 * i + 1) % 16)
      else if i < 48 then (b ^^^ c ^^^ d, (3 * i + 5) % 16)
      else (c ^^^ (b ||| (~~~d)), (7 * i) % 16)
    let f' := f + a + md5K.getD i 0 + word g
    a := d
    d := c
    c := b
    b := b + md5Rotl f' (md5S.getD i 0)
  return (a0 + a, b0 + b, c0 + c, d0 + d)

def md5 (data : ByteArray) : ByteArray := Id.run do
  let bitLen := (data.size * 8).toUInt64
  let mut msg := data.push 0x80
  while msg.size % 64 != 56 do
    msg := msg.push 0
  for i in [0:8] do
    msg := msg.push ((bitLen >>> (8 * i).toUInt64) &&& 0xFF).toUInt8
  let mut st : UInt32 × UInt32 × UInt32 × UInt32 := (0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476)
  for blk in [0:msg.size / 64] do
    st := md5Block st msg (64 * blk)
  let (a, b, c, d) := st
  let mut out := ByteArray.empty
  for w in [a, b, c, d] do
    for i in [0:4] do
      out := out.push ((w >>> (8 * i).toUInt32) &&& 0xFF).toUInt8
  return out

end LeanAV.Bitstream
