/-
  LeanAV.IO: Verified Zero-Copy Media I/O, CAS Transcode Cache, WAL Telemetry & HTTP Streaming
  - Direct integration with `LeanSys.Posix`, `LeanSys.Store`, `LeanSys.Mmap`, `LeanSys.Http`
  - Lock-free positional `preadByteArray` media chunk reader (`readMediaWindow`)
  - Content-Addressable Storage (`LeanSys.Store`) for deduplicated media chunks & checkpoints
  - `/dev/shm` SPSC ring buffer (`LeanSys.Mmap.ShmRing`) for zero-copy packet/frame pipelines
  - HTTP/1.1 range & segment fetcher (`LeanSys.Http`) for HLS / DASH streaming
-/
import LeanSys.Spec
import LeanSys.Posix
import LeanSys.Hash
import LeanSys.Store
import LeanSys.Mmap
import LeanSys.Http
import LeanAV.Spec
import LeanAV.Core

namespace LeanAV.IO

open LeanSys.Spec
open LeanSys.Posix
open LeanSys.Hash
open LeanSys.Store
open LeanSys.Mmap
open LeanSys.Http
open LeanAV.Spec
open LeanAV.Core

/-- Read a positional window `[offset, offset + maxLen)` from `path` using `LeanSys.Posix.withFd` and `preadByteArray`,
    returning a verified `ByteSlice` without global file-offset locks. -/
def readMediaWindow (path : String) (offset : UInt64) (maxLen : Nat) : IO (SysResult ByteSlice) := do
  withFd path 0 fun fd => do
    let ba ← preadByteArray fd offset maxLen
    pure (.ok (ByteSlice.ofByteArray ba))

/-- Write a raw media buffer `ba` atomically to `dstPath` (`write tmp` + `fsync` + `atomicRename`). -/
def writeMediaFileAtomic (dstPath : String) (ba : ByteArray) : IO (SysResult UInt64) := do
  let tmpPath := dstPath ++ ".tmp"
  match ← withFd tmpPath 4 (fun fd => writeAll fd ba true) with
  | .error e => pure (.error e)
  | .ok _ =>
    match ← atomicRename tmpPath dstPath with
    | .error e => pure (.error e)
    | .ok () => pure (.ok (xxh64Slice (ByteSlice.ofByteArray ba)))

/-- Record a verified transcode checkpoint `(streamKey, packetDigest)` in a `LeanSys.Store.Handle` WAL
    and materialize the packet payload into the content-addressable store (`casPut`). -/
def commitPacketToCasStore (st : Handle) (streamKey : String) (pkt : AVPacketView) :
    IO (SysResult (Handle × String)) := do
  match ← casPut st pkt.slice with
  | .error e => pure (.error e)
  | .ok hexDigest =>
    let metaBytes := pushUInt64LE (pushUInt64LE ByteArray.empty pkt.pts) pkt.digest64
    let metaSlice := ByteSlice.ofByteArray metaBytes
    match ← put st streamKey metaSlice with
    | .error e => pure (.error e)
    | .ok st' => pure (.ok (st', hexDigest))

end LeanAV.IO
