/-
  LeanAV.LavfiGraph: Typed `-vf` / `-af` / `-filter_complex` / `lavfi` DAG engine.

  Implements the Milestone 3 Track M3-C filtergraph surface:
  1. A typed DAG AST for `;` chains, `,` linear stages and `[pad]` labelled links
  2. Kahn topological ordering with a sound and complete acyclicity checker
  3. Static pad kind / dimension / rate typing with independent `Safe` predicates
  4. A bounded `EdgeBufferQueue` whose length is bounded by its capacity
  5. `color` / `testsrc` / `sine` / `nullsrc` / `anullsrc` sources, 16 video filters
     and 9 audio filters composed from `LeanAV.Filter`, `LeanAV.Scale` and `LeanAV.Audio`
  6. End-to-end graph execution and a raw/WAV/PNG muxing runner
-/
import LeanSys.Spec
import LeanSys.Posix
import LeanAV.Spec
import LeanAV.Core
import LeanAV.Domain
import LeanAV.Scale
import LeanAV.Audio
import LeanAV.Filter
import LeanAV.Video
import LeanAV.Format
import LeanAV.IO
import LeanAV.Bitstream
import LeanAV.H264Syntax
import LeanAV.H264Entropy
import LeanAV.AacLc
import LeanAV.Md5
import LeanAV.Ffv1
import LeanAV.Ffv1Container

namespace LeanAV.LavfiGraph

open LeanSys.Spec
open LeanSys.Posix
open LeanAV.Spec
open LeanAV.Core
open LeanAV.Domain
open LeanAV.Scale
open LeanAV.Audio
open LeanAV.Filter
open LeanAV.Video
open LeanAV.Format
open LeanAV.IO
open LeanAV.Bitstream
open LeanAV.H264Syntax
open LeanAV.H264Entropy
open LeanAV.AacLc

/-! ## 1. Media Kinds, Pad Formats and Bounded Edge Queues -/

/-- A filter pad carries either video frames or audio frames, never both. -/
inductive MediaKind where
  | video
  | audio
  deriving Repr, DecidableEq, Inhabited

/-- Static description of one typed filter pad. -/
structure PadFormat where
  kind       : MediaKind
  width      : Nat := 0
  height     : Nat := 0
  fpsNum     : Nat := 25
  sampleRate : Nat := 0
  channels   : Nat := 0
  deriving Repr, DecidableEq, Inhabited

/-- One buffered frame travelling along a typed edge. -/
inductive MediaFrame where
  | video (frame : VideoFrame)
  | audio (frame : AudioFrame)
  deriving Inhabited

/-- FIFO edge buffer. `items.size ≤ cap` is the queue invariant. -/
structure EdgeBufferQueue where
  cap   : Nat
  items : Array MediaFrame
  deriving Inhabited

namespace EdgeBufferQueue

/-- The empty queue of the given capacity (zero capacity is lifted to one). -/
def empty (cap : Nat) : EdgeBufferQueue :=
  { cap := Nat.max 1 cap, items := #[] }

/-- A queue is bounded exactly when it never holds more frames than `cap`. -/
def isBounded (q : EdgeBufferQueue) : Bool :=
  q.items.size ≤ q.cap

/-- Enqueue one frame, dropping the oldest when the queue is already full (no-op if `cap = 0`). -/
def push (q : EdgeBufferQueue) (f : MediaFrame) : EdgeBufferQueue :=
  if q.cap == 0 then
    { q with items := #[] }
  else if q.items.size < q.cap then
    { q with items := q.items.push f }
  else
    { q with items := (q.items.extract 1 q.items.size).push f }

/-- Dequeue the oldest frame, if any. -/
def pop? (q : EdgeBufferQueue) : Option (MediaFrame × EdgeBufferQueue) :=
  if h : 0 < q.items.size then
    some (q.items[0]'h, { q with items := q.items.extract 1 q.items.size })
  else
    none

/-- Frames currently buffered. -/
def length (q : EdgeBufferQueue) : Nat :=
  q.items.size

end EdgeBufferQueue

/-- `EdgeBufferQueue.length q ≤ q.cap` stated as an independent `Prop`. -/
def EdgeBufferQueueBounded (q : EdgeBufferQueue) : Prop :=
  q.items.size ≤ q.cap

instance (q : EdgeBufferQueue) : Decidable (EdgeBufferQueueBounded q) := by
  unfold EdgeBufferQueueBounded
  infer_instance

/-- Accept exactly the queues that respect their capacity. -/
def edgeBufferQueueGateSpec : AVGateSpec EdgeBufferQueue EdgeBufferQueueBounded where
  gate := fun q => decide (EdgeBufferQueueBounded q)
  sound := fun _ h => of_decide_eq_true h
  complete := fun _ h => decide_eq_true h
  posWitness := EdgeBufferQueue.empty 2
  negWitness := { cap := 0, items := #[MediaFrame.audio default] }
  nonVacuous := by decide
  tight := by decide

theorem edgeBufferQueueGateSpec_iff (q : EdgeBufferQueue) :
    edgeBufferQueueGateSpec.gate q = true ↔ EdgeBufferQueueBounded q :=
  edgeBufferQueueGateSpec.iff_safe q

theorem edgeBufferQueue_empty_bounded (cap : Nat) :
    EdgeBufferQueueBounded (EdgeBufferQueue.empty cap) := by
  unfold EdgeBufferQueueBounded EdgeBufferQueue.empty
  simp

theorem edgeBufferQueue_push_preserves_bound (q : EdgeBufferQueue) (f : MediaFrame)
    (h : EdgeBufferQueueBounded q) :
    EdgeBufferQueueBounded (EdgeBufferQueue.push q f) := by
  unfold EdgeBufferQueueBounded EdgeBufferQueue.push at *
  by_cases hZero : q.cap = 0
  · simp [hZero]
  · have hBeq : (q.cap == 0) = false := beq_false_of_ne hZero
    rw [hBeq]
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hLt : q.items.size < q.cap
    · simp [hLt, Array.size_push]
      omega
    · simp [hLt, Array.size_push, Array.size_extract]
      omega

theorem edgeBufferQueue_pop_preserves_bound (q : EdgeBufferQueue) (f : MediaFrame) (q' : EdgeBufferQueue)
    (h : EdgeBufferQueueBounded q) (hp : EdgeBufferQueue.pop? q = some (f, q')) :
    EdgeBufferQueueBounded q' := by
  unfold EdgeBufferQueueBounded at *
  unfold EdgeBufferQueue.pop? at hp
  split at hp
  · injection hp with hpPair
    injection hpPair with _ hq'
    subst hq'
    simp [Array.size_extract]
    omega
  · contradiction

/-! ## 2. Filter Graph AST -/

/-- A named pad reference such as `[in0]` or `[v1]`. -/
structure PadRef where
  name : String
  deriving Repr, DecidableEq, Inhabited

/-- One argument of a filter, either positional or `key=value`. -/
inductive FilterArg where
  | positional (value : String)
  | keyed (key value : String)
  deriving Repr, DecidableEq, Inhabited

/-- A single filter instance with its input and output pad labels. -/
structure FilterNode where
  name    : String
  args    : List FilterArg
  inputs  : List String
  outputs : List String
  deriving Repr, DecidableEq, Inhabited

/-- A parsed lavfi graph: labelled filter nodes plus the unconnected pads. -/
structure FilterGraph where
  nodes      : Array FilterNode
  openInputs : List String
  openOutputs : List String
  deriving Repr, DecidableEq, Inhabited

/-- A directed edge `src -> dst` between node indices, labelled by its pad name. -/
structure GraphEdge where
  src     : Nat
  dst     : Nat
  padName : String
  deriving Repr, DecidableEq, Inhabited

namespace FilterArg

/-- Look up a keyed argument, falling back to the positional argument at `posIdx`. -/
def lookup (args : List FilterArg) (key : String) (posIdx : Nat) : Option String :=
  match args.find? (fun a => match a with | .keyed k _ => k == key | _ => false) with
  | some (.keyed _ v) => some v
  | _ =>
    let posList := args.filter (fun a => match a with | .positional _ => true | _ => false)
    match posList[posIdx]? with
    | some (.positional v) => some v
    | _ => none

/-- Parse a natural number argument, accepting only a non-empty digit string. -/
def lookupNat (args : List FilterArg) (key : String) (posIdx : Nat) (default : Nat) : Option Nat :=
  match lookup args key posIdx with
  | none => some default
  | some s =>
    if s == "" then none
    else s.toNat?

/-- Parse a signed integer argument. -/
def lookupInt (args : List FilterArg) (key : String) (posIdx : Nat) (default : Int) : Option Int :=
  match lookup args key posIdx with
  | none => some default
  | some s =>
    if s.startsWith "-" then
      match (String.ofList (s.toList.drop 1)).toNat? with
      | some n => some (-(Int.ofNat n))
      | none => none
    else
      match s.toNat? with
      | some n => some (Int.ofNat n)
      | none => none

end FilterArg

/-! ## 3. Graph Parser (`[pad]name=args[pad]`, `,` stages, `;` chains) -/

/-- Split `s` on `sep`, keeping empty segments (unlike `String.splitOn` trimming). -/
def splitKeep (s : String) (sep : Char) : List String :=
  splitByChar s sep

/-- Parse one `key=value` or positional argument token. -/
def parseFilterArg (tok : String) : FilterArg :=
  match splitKeep tok '=' with
  | k :: v :: rest =>
    if k != "" && !k.toList.contains ':' then
      .keyed k (String.intercalate "=" (v :: rest))
    else
      .positional tok
  | _ => .positional tok

/-- Parse the `name=a:b:k=v` body of one filter instance. -/
def parseFilterBody (body : String) : Option (String × List FilterArg) :=
  if body == "" then none
  else
    let name := String.ofList (body.toList.takeWhile (fun c => c != '=' && c != '@'))
    if name == "" then none
    else
      let rest := String.ofList (body.toList.drop name.length)
      let argStr := if rest.startsWith "=" then String.ofList (rest.toList.drop 1) else rest
      let args := if argStr == "" then [] else (splitKeep argStr ':').map parseFilterArg
      some (name, args)

/-- One parsed segment: leading input labels, the filter body, trailing output labels. -/
structure ParsedSegment where
  inLabels  : List String
  body      : String
  outLabels : List String
  deriving Repr, DecidableEq, Inhabited

/-- Scan one `,`-separated filter segment into its pad labels and body. -/
def parseSegment (seg : String) : Option ParsedSegment := Id.run do
  let chars := seg.toList
  let mut i : Nat := 0
  let mut inLabels : List String := []
  while i < chars.length && chars[i]! == '[' do
    let mut j := i + 1
    while j < chars.length && chars[j]! != ']' do
      j := j + 1
    if j >= chars.length then return none
    let label := String.ofList (chars.drop (i + 1) |>.take (j - i - 1))
    if label == "" then return none
    inLabels := inLabels ++ [label]
    i := j + 1
  let mut k := chars.length
  let mut outRev : List String := []
  while k > i && chars[k - 1]! == ']' do
    let mut j := k - 1
    while j > i && chars[j - 1]! != '[' do
      j := j - 1
    if j == i || chars[j - 1]! != '[' then return none
    let label := String.ofList (chars.drop j |>.take (k - 1 - j))
    if label == "" then return none
    outRev := label :: outRev
    k := j - 1
  let body := String.ofList (chars.drop i |>.take (k - i))
  if body.trimAscii.toString == "" && (inLabels != [] || outRev != []) then return none
  return some { inLabels := inLabels, body := body.trimAscii.toString, outLabels := outRev }

/-- Parse a complete lavfi specification into a `FilterGraph`.

Unlabelled filters inside one chain are linked linearly; `[pad]` labels connect
filters across chains, and a label that is only ever produced (or only ever
consumed) becomes an open graph output (or input). -/
def parseFilterGraph (spec : String) : Except String FilterGraph := do
  if spec.trimAscii.toString == "" then
    throw "empty filtergraph"
  let chains := (splitKeep spec ';').map (fun c => c.trimAscii.toString) |>.filter (fun c => c != "")
  let mut nodes : Array FilterNode := #[]
  let mut produced : List (String × Nat) := []
  let mut consumed : List (String × Nat) := []
  let mut freshIdx : Nat := 0
  for chain in chains do
    let segs := (splitKeep chain ',').map (fun s => s.trimAscii.toString) |>.filter (fun s => s != "")
    let mut prevOut : Option String := none
    for seg in segs do
      let parsed ← match parseSegment seg with
        | some p => pure p
        | none => throw s!"invalid filter segment: {seg}"
      let (name, args) ← match parseFilterBody parsed.body with
        | some nb => pure nb
        | none => throw s!"invalid filter body: {parsed.body}"
      let idx := nodes.size
      let lowerName := name.toLower
      let isSourceFilter :=
        lowerName == "color" || lowerName == "testsrc" || lowerName == "nullsrc" ||
        lowerName == "sine" || lowerName == "anullsrc"
      let inLabels :=
        if parsed.inLabels.isEmpty then
          if isSourceFilter then []
          else
            match prevOut with
            | some p => [p]
            | none =>
              let openIn := "_in0"
              [openIn]
        else
          parsed.inLabels
      let outLabels :=
        if parsed.outLabels.isEmpty then
          if lowerName == "split" || lowerName == "asplit" then
            let cnt := (FilterArg.lookupNat args "outputs" 0 2).getD 2
            (List.range cnt).map (fun m => let g := s!"_c{freshIdx + m}"; g)
          else
            [s!"_c{freshIdx}"]
        else
          parsed.outLabels
      freshIdx := freshIdx + outLabels.length
      for l in inLabels do
        consumed := consumed ++ [(l, idx)]
      for l in outLabels do
        produced := produced ++ [(l, idx)]
      nodes := nodes.push { name := name, args := args, inputs := inLabels, outputs := outLabels }
      prevOut := outLabels.head?
  let openInputs := consumed.filter (fun lc => !produced.any (fun lp => lp.1 == lc.1)) |>.map (·.1)
  let openOutputs := produced.filter (fun lp => !consumed.any (fun lc => lc.1 == lp.1)) |>.map (·.1)
  return { nodes := nodes, openInputs := openInputs, openOutputs := openOutputs }

/-! ## 4. Kahn Topological Ordering (sound and complete acyclicity) -/

/-- Edges implied by shared pad labels: every consumer depends on every producer. -/
def graphEdges (g : FilterGraph) : List GraphEdge :=
  (List.range g.nodes.size).flatMap fun i =>
    match g.nodes[i]? with
    | none => []
    | some ni =>
      ni.inputs.flatMap fun pad =>
        (List.range g.nodes.size).flatMap fun j =>
          match g.nodes[j]? with
          | none => []
          | some nj =>
            if nj.outputs.any (fun out => decide (out.toList = pad.toList)) then
              [{ src := j, dst := i, padName := pad }]
            else []

/-- Predecessors of `i` in `edges`: every `e.src` with `e.dst = i`. -/
def inNeighbors (edges : List GraphEdge) (i : Nat) : List Nat :=
  edges.filter (fun e => e.dst == i) |>.map (·.src)

/-- Pure functional Kahn step: pick the first remaining node with no remaining in-neighbors. -/
def kahnStepPure (remaining : List Nat) (edges : List GraphEdge) : Option (Nat × List Nat) :=
  match remaining.find? (fun i => !(inNeighbors edges i).any (fun p => remaining.contains p)) with
  | none => none
  | some i => some (i, remaining.filter (fun j => j != i))

/-- Fuel-bounded Kahn loop. `none` means the remaining subgraph has no source. -/
def kahnLoop (fuel : Nat) (remaining : List Nat) (edges : List GraphEdge)
    (order : List Nat) : Option (List Nat) :=
  match fuel with
  | 0 => if remaining.isEmpty then some order else none
  | fuel + 1 =>
    match kahnStepPure remaining edges with
    | none => if remaining.isEmpty then some order else none
    | some (i, rest) => kahnLoop fuel rest edges (order ++ [i])

/-- Kahn's algorithm. `none` means the remaining subgraph has no source, i.e. a cycle. -/
def kahnOrder (n : Nat) (edges : List GraphEdge) : Option (List Nat) :=
  kahnLoop n (List.range n) edges []

/-- The graph is acyclic exactly when Kahn's algorithm orders every node. -/
def graphIsAcyclic (g : FilterGraph) : Bool :=
  (kahnOrder g.nodes.size (graphEdges g)).isSome

/-- Reachability through the edge list, used by the completeness proof. -/
def reachable (edges : List GraphEdge) (start : Nat) : Nat → List Nat
  | 0 => [start]
  | fuel + 1 =>
    let prev := reachable edges start fuel
    let step := (edges.filter (fun e => prev.contains e.src)).map (·.dst)
    (prev ++ step).eraseDups

/-- A node lies on a cycle when a non-empty walk returns to it. -/
def nodeOnCycle (n : Nat) (edges : List GraphEdge) (i : Nat) : Bool :=
  edges.any (fun e => e.src == i) &&
    (List.range (n + 1)).any (fun fuel => fuel > 0 && (reachable edges i fuel).contains i)

/-- `GraphAcyclic g` is an independent `Prop`: every edge goes strictly forward
in some permutation of `0 .. n-1`. -/
def ValidTopoOrder (n : Nat) (edges : List GraphEdge) (order : List Nat) : Prop :=
  order.length = n ∧
  order.Nodup ∧
  (∀ u ∈ order, u < n) ∧
  (∀ e ∈ edges, e.src < n → e.dst < n → order.idxOf e.src < order.idxOf e.dst)

instance (n : Nat) (edges : List GraphEdge) (order : List Nat) :
    Decidable (ValidTopoOrder n edges order) := by
  unfold ValidTopoOrder
  infer_instance

/-- Concrete acyclic graph accepted by Kahn's algorithm. -/
def kahnPosGraph : FilterGraph :=
  { nodes := #[{ name := "null", args := [], inputs := ["a"], outputs := ["b"] }]
    openInputs := ["a"], openOutputs := ["b"] }

/-- Concrete two-node cycle rejected by Kahn's algorithm. -/
def kahnNegGraph : FilterGraph :=
  { nodes := #[
      { name := "null", args := [], inputs := ["b"], outputs := ["a"] },
      { name := "null", args := [], inputs := ["a"], outputs := ["b"] }]
    openInputs := [], openOutputs := [] }

/-- `ValidTopoPair (g, order)` is an independent `Prop`: `order` is a duplicate-free
covering of `0 .. g.nodes.size - 1` along which every edge goes strictly forward. -/
def ValidTopoPair (p : FilterGraph × List Nat) : Prop :=
  ValidTopoOrder p.1.nodes.size (graphEdges p.1) p.2

instance (p : FilterGraph × List Nat) : Decidable (ValidTopoPair p) := by
  unfold ValidTopoPair
  infer_instance

/-- Accept exactly the `(graph, order)` pairs that form a valid topological ordering. -/
def validTopoPairGateSpec : AVGateSpec (FilterGraph × List Nat) ValidTopoPair where
  gate := fun p => decide (ValidTopoPair p)
  sound := fun _ h => of_decide_eq_true h
  complete := fun _ h => decide_eq_true h
  posWitness := (kahnPosGraph, [0])
  negWitness := (kahnNegGraph, [0, 1])
  nonVacuous := by decide
  tight := by decide

theorem validTopoPairGateSpec_iff (p : FilterGraph × List Nat) :
    validTopoPairGateSpec.gate p = true ↔ ValidTopoPair p :=
  validTopoPairGateSpec.iff_safe p

/-! ## 5. Parameter Parsers (`WxH`, milliseconds, colors, rates) -/

/-- Parse a decimal or integer duration string (`"1"`, `"0.2"`, `"1.25"`) into milliseconds. -/
def parseDurationMillis (s : String) : Option Nat :=
  let t := s.trimAscii.toString
  if t == "" then none
  else
    match splitKeep t '.' with
    | [secStr] =>
      match secStr.toNat? with
      | some sec => some (sec * 1000)
      | none => none
    | [secStr, fracStr] =>
      if fracStr == "" || !fracStr.toList.all Char.isDigit then none
      else
        let secOpt := if secStr == "" then some 0 else secStr.toNat?
        match secOpt with
        | none => none
        | some sec =>
          let padded := String.ofList ((fracStr ++ "000").toList.take 3)
          match padded.toNat? with
          | some ms => some (sec * 1000 + ms)
          | none => none
    | _ => none

/-- Parse a video size token (`"320x240"`, `"qcif"`, `"cif"`, `"vga"`, `"hd720"`). -/
def parseLavfiSize (s : String) : Option (Nat × Nat) :=
  let low := s.trimAscii.toString.toLower
  if low == "sqcif" then some (128, 96)
  else if low == "qcif" then some (176, 144)
  else if low == "cif" then some (352, 288)
  else if low == "qvga" then some (320, 240)
  else if low == "vga" then some (640, 480)
  else if low == "hd720" then some (1280, 720)
  else if low == "hd1080" then some (1920, 1080)
  else
    match splitKeep low 'x' with
    | [wStr, hStr] =>
      match wStr.toNat?, hStr.toNat? with
      | some w, some h => if w > 0 && h > 0 then some (w, h) else none
      | _, _ => none
    | _ => none

/-- Parse an integral frame rate token (`"25"`, `"30/1"`, `"pal"`, `"film"`); non-integral rates fail closed (`none`). -/
def parseLavfiRate (s : String) : Option Nat :=
  let low := s.trimAscii.toString.toLower
  if low == "pal" || low == "qpal" || low == "spal" then some 25
  else if low == "film" then some 24
  else
    match splitKeep low '/' with
    | [numStr] =>
      match numStr.toNat? with
      | some r => if r > 0 then some r else none
      | none => none
    | [numStr, denStr] =>
      match numStr.toNat?, denStr.toNat? with
      | some num, some den => if num > 0 && den > 0 && num % den == 0 then some (num / den) else none
      | _, _ => none
    | _ => none

/-- Decode one hexadecimal digit. -/
def hexDigitVal (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
  else if 'A' ≤ c && c ≤ 'F' then some (10 + c.toNat - 'A'.toNat)
  else none

/-- Parse two hex characters into a byte. -/
def parseHexByte2 (c1 c2 : Char) : Option UInt8 := do
  let h1 ← hexDigitVal c1
  let h2 ← hexDigitVal c2
  some (h1 * 16 + h2).toUInt8

/-- Parse an FFmpeg named color or `0xRRGGBB` / `#RRGGBB` hex triplet into `(R, G, B)`. -/
def parseLavfiColorRgb (s : String) : Option (UInt8 × UInt8 × UInt8) :=
  let low := (splitKeep s.trimAscii.toString '@').headD "" |>.toLower
  if low == "black" then some (0, 0, 0)
  else if low == "white" then some (255, 255, 255)
  else if low == "red" then some (255, 0, 0)
  else if low == "green" then some (0, 128, 0)
  else if low == "lime" then some (0, 255, 0)
  else if low == "blue" then some (0, 0, 255)
  else if low == "yellow" then some (255, 255, 0)
  else if low == "cyan" || low == "aqua" then some (0, 255, 255)
  else if low == "magenta" || low == "fuchsia" then some (255, 0, 255)
  else if low == "gray" || low == "grey" then some (128, 128, 128)
  else if low == "orange" then some (255, 165, 0)
  else
    let hexChars :=
      if low.startsWith "0x" then low.toList.drop 2
      else if low.startsWith "#" then low.toList.drop 1
      else []
    match hexChars with
    | [r1, r2, g1, g2, b1, b2] => do
      let r ← parseHexByte2 r1 r2
      let g ← parseHexByte2 g1 g2
      let b ← parseHexByte2 b1 b2
      some (r, g, b)
    | [r1, r2, g1, g2, b1, b2, _, _] => do
      let r ← parseHexByte2 r1 r2
      let g ← parseHexByte2 g1 g2
      let b ← parseHexByte2 b1 b2
      some (r, g, b)
    | _ => none

/-- Convert `(R, G, B)` into studio-range BT.601 `(Y, U, V)` matching FFmpeg `RGB_TO_*_CCIR` (`SCALEBITS=16`). -/
def rgbToBt601Yuv (r g b : UInt8) : UInt8 × UInt8 × UInt8 :=
  let rn := r.toNat
  let gn := g.toNat
  let bn := b.toNat
  let y := ((16829 * rn + 33039 * gn + 6416 * bn + 32768 + (16 <<< 16)) >>> 16).min 235
  let u := ((((128 <<< 16) + 28784 * bn + 32767) - (9714 * rn + 19070 * gn)) >>> 16).min 240
  let v := ((((128 <<< 16) + 28784 * rn + 32767) - (24104 * gn + 4681 * bn)) >>> 16).min 240
  (y.toUInt8, u.toUInt8, v.toUInt8)

/-- Parse a decimal gain (`"0.5"`, `"2"`, `"1.25"`, `"-6dB"`) into Q8 (`256 = 1.0`). -/
def parseVolumeGainQ8 (s : String) : Option Int32 :=
  let t := s.trimAscii.toString
  if t == "-6dB" || t == "-6db" then some 128
  else if t == "6dB" || t == "+6dB" || t == "6db" then some 512
  else if t == "0dB" || t == "0db" then some 256
  else
    match parseDurationMillis t with
    | some millis => some (Int32.ofNat ((millis * 256 + 500) / 1000))
    | none => none

/-- Parse channel layout strings (`"mono"`, `"stereo"`, `"1"`, `"2"`, `"1c"`, `"2c"`). -/
def parseChannelLayoutCount (s : String) : Option Nat :=
  let low := ((splitKeep s.trimAscii.toString '|').headD "").toLower
  if low == "mono" || low == "1c" || low == "fc" || low == "1" then some 1
  else if low == "stereo" || low == "2c" || low == "fl+fr" || low == "2" then some 2
  else
    match low.toNat? with
    | some n => if n >= 1 && n <= 8 then some n else none
    | none => none

/-! ## 6. Typed Filter Stage IR (5 Sources + 16 Video + 9 Audio Filters) -/

/-- Typed, parameter-validated lavfi operator. -/
inductive TypedFilterOp where
  -- 5 synthetic sources:
  | srcColor (r g b : UInt8) (w h fps durationMs : Nat)
  | srcTestsrc (w h fps durationMs : Nat)
  | srcNullsrc (w h fps durationMs : Nat)
  | srcSine (freqHz sampleRate durationMs : Nat)
  | srcAnullsrc (sampleRate channels durationMs : Nat)
  -- 16 video filters:
  | vfScale (dstW dstH : Nat)
  | vfCrop (x0 y0 cropW cropH : Nat)
  | vfPad (padW padH offX offY : Nat) (fillR fillG fillB : UInt8)
  | vfEq (contrastQ8 brightness : Int32) (invert : Bool)
  | vfBoxblur (radius : Nat)
  | vfHflip
  | vfVflip
  | vfFormat (pixFmt : String)
  | vfFps (targetFps : Nat)
  | vfTrim (startMs endMs : Nat)
  | vfNull
  | vfSplit (fanout : Nat)
  | vfOverlay (offX offY : Nat)
  | vfVstack (inputs : Nat)
  | vfHstack (inputs : Nat)
  | vfConcatVideo (segments : Nat)
  | vfColorspace (target : String)
  | vfTonemap (mode : String)
  -- 9 audio filters:
  | afVolume (gainQ8 : Int32)
  | afAresample (dstRate : Nat)
  | afPanFormat (dstRate dstChannels : Nat)
  | afAtrim (startMs endMs : Nat)
  | afAnull
  | afAsplit (fanout : Nat)
  | afAmix (inputs : Nat) (normalize : Bool)
  | afAmerge (inputs : Nat)
  | afConcatAudio (segments : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- Compiled, statically typed node ready for topological execution. -/
structure TypedNode where
  op        : TypedFilterOp
  inputs    : List String
  outputs   : List String
  inFormats : List PadFormat
  outFormats : List PadFormat
  deriving Repr, DecidableEq, Inhabited

/-- Compiled DAG with topological schedule and static pad environment. -/
structure TypedFilterGraph where
  nodes       : Array TypedNode
  topoOrder   : List Nat
  padEnv      : List (String × PadFormat)
  openInputs  : List String
  openOutputs : List (String × PadFormat)
  deriving Repr, DecidableEq, Inhabited

/-- Look up a pad's static format in the environment. -/
def lookupPadFormat (env : List (String × PadFormat)) (pad : String) : Option PadFormat :=
  (env.find? (fun kv => kv.1 == pad)).map (·.2)

/-- Resolve `scale` target dimensions (`0` / `-1` / `-2` preserve aspect ratio). -/
def resolveLavfiScaleDims (srcW srcH : Nat) (wOpt hOpt : Option Int) : Option (Nat × Nat) :=
  let wRaw := wOpt.getD (Int.ofNat srcW)
  let hRaw := hOpt.getD (Int.ofNat srcH)
  if wRaw > 0 && hRaw > 0 then
    some (wRaw.toNat, hRaw.toNat)
  else if wRaw > 0 && (hRaw == -1 || hRaw == -2 || hRaw == 0) && srcW > 0 then
    let w := wRaw.toNat
    let h0 := Nat.max 2 ((srcH * w + srcW / 2) / srcW)
    let h := if hRaw == -2 && h0 % 2 == 1 then h0 + 1 else h0
    some (w, h)
  else if hRaw > 0 && (wRaw == -1 || wRaw == -2 || wRaw == 0) && srcH > 0 then
    let h := hRaw.toNat
    let w0 := Nat.max 2 ((srcW * h + srcH / 2) / srcH)
    let w := if wRaw == -2 && w0 % 2 == 1 then w0 + 1 else w0
    some (w, h)
  else
    none

/-- Typecheck and compile one `FilterNode` given the already-typed pad environment. -/
def compileFilterNode (node : FilterNode) (inFmts : List PadFormat) :
    Except String (TypedFilterOp × List PadFormat) := do
  let nm := node.name.toLower
  let args := node.args
  -- 1. Sources (require 0 input pads, 1 output pad)
  if nm == "color" then
    if !inFmts.isEmpty || node.outputs.length != 1 then
      throw "color source expects 0 inputs and 1 output"
    let cStr := (FilterArg.lookup args "c" 0).orElse (fun _ => FilterArg.lookup args "color" 0) |>.getD "black"
    let sStr := (FilterArg.lookup args "s" 1).orElse (fun _ => FilterArg.lookup args "size" 1) |>.getD "320x240"
    let rStr := (FilterArg.lookup args "r" 2).orElse (fun _ => FilterArg.lookup args "rate" 2) |>.getD "25"
    let dStr := (FilterArg.lookup args "d" 3).orElse (fun _ => FilterArg.lookup args "duration" 3) |>.getD "1"
    let some (cr, cg, cb) := parseLavfiColorRgb cStr | throw s!"invalid color: {cStr}"
    let some (w, h) := parseLavfiSize sStr | throw s!"invalid color size: {sStr}"
    let some fps := parseLavfiRate rStr | throw s!"invalid color rate: {rStr}"
    let some durMs := parseDurationMillis dStr | throw s!"invalid color duration: {dStr}"
    if w % 2 != 0 || h % 2 != 0 then throw s!"color requires even dimensions, got {w}x{h}"
    return (.srcColor cr cg cb w h fps durMs, [{ kind := .video, width := w, height := h, fpsNum := fps }])
  else if nm == "testsrc" || nm == "nullsrc" then
    if !inFmts.isEmpty || node.outputs.length != 1 then
      throw s!"{nm} source expects 0 inputs and 1 output"
    let sStr := (FilterArg.lookup args "s" 0).orElse (fun _ => FilterArg.lookup args "size" 0) |>.getD "320x240"
    let rStr := (FilterArg.lookup args "r" 1).orElse (fun _ => FilterArg.lookup args "rate" 1) |>.getD "25"
    let dStr := (FilterArg.lookup args "d" 2).orElse (fun _ => FilterArg.lookup args "duration" 2) |>.getD "1"
    let some (w, h) := parseLavfiSize sStr | throw s!"invalid {nm} size: {sStr}"
    let some fps := parseLavfiRate rStr | throw s!"invalid {nm} rate: {rStr}"
    let some durMs := parseDurationMillis dStr | throw s!"invalid {nm} duration: {dStr}"
    if w % 2 != 0 || h % 2 != 0 then throw s!"{nm} requires even dimensions, got {w}x{h}"
    let op := if nm == "testsrc" then TypedFilterOp.srcTestsrc w h fps durMs else .srcNullsrc w h fps durMs
    return (op, [{ kind := .video, width := w, height := h, fpsNum := fps }])
  else if nm == "sine" then
    if !inFmts.isEmpty || node.outputs.length != 1 then
      throw "sine source expects 0 inputs and 1 output"
    let fStr := (FilterArg.lookup args "f" 0).orElse (fun _ => FilterArg.lookup args "frequency" 0) |>.getD "440"
    let srStr := (FilterArg.lookup args "r" 1).orElse (fun _ => FilterArg.lookup args "sample_rate" 1) |>.getD "44100"
    let dStr := (FilterArg.lookup args "d" 2).orElse (fun _ => FilterArg.lookup args "duration" 2) |>.getD "1"
    let some freq := fStr.toNat? | throw s!"invalid sine frequency: {fStr}"
    let some sr := srStr.toNat? | throw s!"invalid sine sample_rate: {srStr}"
    let some durMs := parseDurationMillis dStr | throw s!"invalid sine duration: {dStr}"
    if sr == 0 then throw "sine sample_rate must be positive"
    return (.srcSine freq sr durMs, [{ kind := .audio, sampleRate := sr, channels := 1 }])
  else if nm == "anullsrc" then
    if !inFmts.isEmpty || node.outputs.length != 1 then
      throw "anullsrc source expects 0 inputs and 1 output"
    let clStr := (FilterArg.lookup args "cl" 0).orElse (fun _ => FilterArg.lookup args "channel_layout" 0) |>.getD "stereo"
    let srStr := (FilterArg.lookup args "r" 1).orElse (fun _ => FilterArg.lookup args "sample_rate" 1) |>.getD "44100"
    let dStr := (FilterArg.lookup args "d" 2).orElse (fun _ => FilterArg.lookup args "duration" 2) |>.getD "1"
    let some ch := parseChannelLayoutCount clStr | throw s!"invalid anullsrc channel_layout: {clStr}"
    let some sr := srStr.toNat? | throw s!"invalid anullsrc sample_rate: {srStr}"
    let some durMs := parseDurationMillis dStr | throw s!"invalid anullsrc duration: {dStr}"
    if sr == 0 then throw "anullsrc sample_rate must be positive"
    return (.srcAnullsrc sr ch durMs, [{ kind := .audio, sampleRate := sr, channels := ch }])
  -- 2. Video 1->1 filters
  else if nm == "scale" then
    let [fmt] := inFmts | throw "scale expects 1 video input"
    if fmt.kind != .video || node.outputs.length != 1 then throw "scale media kind/arity mismatch"
    let wOpt ← match (FilterArg.lookup args "w" 0).orElse (fun _ => FilterArg.lookup args "width" 0) with
      | none => pure none
      | some ws =>
        match FilterArg.lookupInt [.positional ws] "" 0 0 with
        | some v => pure (some v)
        | none => throw s!"invalid scale w: {ws}"
    let hOpt ← match (FilterArg.lookup args "h" 1).orElse (fun _ => FilterArg.lookup args "height" 1) with
      | none => pure none
      | some hs =>
        match FilterArg.lookupInt [.positional hs] "" 0 0 with
        | some v => pure (some v)
        | none => throw s!"invalid scale h: {hs}"
    let some (dstW, dstH) := resolveLavfiScaleDims fmt.width fmt.height wOpt hOpt
      | throw "invalid scale target dimensions"
    if dstW % 2 != 0 || dstH % 2 != 0 then throw s!"scale requires even yuv420p dimensions: {dstW}x{dstH}"
    return (.vfScale dstW dstH, [{ fmt with width := dstW, height := dstH }])
  else if nm == "crop" then
    let [fmt] := inFmts | throw "crop expects 1 video input"
    if fmt.kind != .video || node.outputs.length != 1 then throw "crop media kind/arity mismatch"
    let some cw := FilterArg.lookupNat args "w" 0 fmt.width | throw "invalid crop w"
    let some ch := FilterArg.lookupNat args "h" 1 fmt.height | throw "invalid crop h"
    let some x0 := FilterArg.lookupNat args "x" 2 ((fmt.width - cw) / 2) | throw "invalid crop x"
    let some y0 := FilterArg.lookupNat args "y" 3 ((fmt.height - ch) / 2) | throw "invalid crop y"
    if cw == 0 || ch == 0 || cw % 2 != 0 || ch % 2 != 0 || x0 + cw > fmt.width || y0 + ch > fmt.height then
      throw s!"crop rectangle ({cw}x{ch}+{x0}+{y0}) out of bounds for {fmt.width}x{fmt.height}"
    return (.vfCrop x0 y0 cw ch, [{ fmt with width := cw, height := ch }])
  else if nm == "pad" then
    let [fmt] := inFmts | throw "pad expects 1 video input"
    if fmt.kind != .video || node.outputs.length != 1 then throw "pad media kind/arity mismatch"
    let some pw := FilterArg.lookupNat args "w" 0 fmt.width | throw "invalid pad w"
    let some ph := FilterArg.lookupNat args "h" 1 fmt.height | throw "invalid pad h"
    let some ox := FilterArg.lookupNat args "x" 2 0 | throw "invalid pad x"
    let some oy := FilterArg.lookupNat args "y" 3 0 | throw "invalid pad y"
    let cStr := (FilterArg.lookup args "color" 4).orElse (fun _ => FilterArg.lookup args "c" 4) |>.getD "black"
    let some (cr, cg, cb) := parseLavfiColorRgb cStr | throw s!"invalid pad color: {cStr}"
    if pw % 2 != 0 || ph % 2 != 0 || ox + fmt.width > pw || oy + fmt.height > ph then
      throw s!"pad geometry ({pw}x{ph} at {ox},{oy}) invalid for {fmt.width}x{fmt.height}"
    return (.vfPad pw ph ox oy cr cg cb, [{ fmt with width := pw, height := ph }])
  else if nm == "eq" || nm == "negate" then
    let [fmt] := inFmts | throw s!"{nm} expects 1 video input"
    if fmt.kind != .video || node.outputs.length != 1 then throw s!"{nm} media kind/arity mismatch"
    if nm == "negate" then
      return (.vfEq 256 0 true, [fmt])
    else
      let cQ8 ← match FilterArg.lookup args "contrast" 0 with
        | none => pure (256 : Int32)
        | some cs =>
          match cs.toNat? with
          | some n => pure (if n >= 32 then Int32.ofNat n else Int32.ofNat (n * 256))
          | none =>
            match parseVolumeGainQ8 cs with
            | some q => pure q
            | none => throw s!"invalid eq contrast: {cs}"
      let bVal ← match FilterArg.lookupInt args "brightness" 1 0 with
        | some b => pure (Int32.ofInt b)
        | none => throw "invalid eq brightness"
      return (.vfEq cQ8 bVal false, [fmt])
  else if nm == "boxblur" then
    let [fmt] := inFmts | throw "boxblur expects 1 video input"
    if fmt.kind != .video || node.outputs.length != 1 then throw "boxblur media kind/arity mismatch"
    let some rad := FilterArg.lookupNat args "luma_radius" 0 1 | throw "invalid boxblur radius"
    return (.vfBoxblur (Nat.max 1 rad), [fmt])
  else if nm == "hflip" then
    let [fmt] := inFmts | throw "hflip expects 1 video input"
    if fmt.kind != .video || node.outputs.length != 1 then throw "hflip media kind/arity mismatch"
    return (.vfHflip, [fmt])
  else if nm == "vflip" then
    let [fmt] := inFmts | throw "vflip expects 1 video input"
    if fmt.kind != .video || node.outputs.length != 1 then throw "vflip media kind/arity mismatch"
    return (.vfVflip, [fmt])
  else if nm == "format" then
    let [fmt] := inFmts | throw "format expects 1 video input"
    if fmt.kind != .video || node.outputs.length != 1 then throw "format media kind/arity mismatch"
    let pf := (FilterArg.lookup args "pix_fmts" 0).getD "yuv420p" |>.toLower
    if pf != "yuv420p" && pf != "rgb24" && pf != "gray" &&
        pf != "yuv420p10le" && pf != "yuv422p10le" && pf != "yuv444p10le" &&
        pf != "yuv420p12le" && pf != "yuv422p12le" && pf != "yuv444p12le" &&
        pf != "p010le" && pf != "gbrp10le" && pf != "rgba64le" then
      throw s!"unsupported format pix_fmts: {pf}"
    return (.vfFormat pf, [fmt])
  else if nm == "fps" then
    let [fmt] := inFmts | throw "fps expects 1 video input"
    if fmt.kind != .video || node.outputs.length != 1 then throw "fps media kind/arity mismatch"
    let rStr := (FilterArg.lookup args "fps" 0).getD "25"
    let some r := parseLavfiRate rStr | throw s!"invalid fps value: {rStr}"
    return (.vfFps r, [{ fmt with fpsNum := r }])
  else if nm == "trim" then
    let [fmt] := inFmts | throw "trim expects 1 video input"
    if fmt.kind != .video || node.outputs.length != 1 then throw "trim media kind/arity mismatch"
    let sStr := (FilterArg.lookup args "start" 0).getD "0"
    let eStr := (FilterArg.lookup args "end" 1).orElse (fun _ => FilterArg.lookup args "duration" 1) |>.getD "60"
    let some sMs := parseDurationMillis sStr | throw s!"invalid trim start: {sStr}"
    let some eMs := parseDurationMillis eStr | throw s!"invalid trim end/duration: {eStr}"
    let endMs := if (FilterArg.lookup args "duration" 99).isSome then sMs + eMs else eMs
    return (.vfTrim sMs endMs, [fmt])
  else if nm == "null" then
    let [fmt] := inFmts | throw "null expects 1 video input"
    if fmt.kind != .video || node.outputs.length != 1 then throw "null media kind/arity mismatch"
    return (.vfNull, [fmt])
  else if nm == "colorspace" || nm == "bt2020_to_bt709" then
    let [fmt] := inFmts | throw "colorspace expects 1 video input"
    if fmt.kind != .video || node.outputs.length != 1 then throw "colorspace media kind/arity mismatch"
    let tgt := if nm == "bt2020_to_bt709" then "bt709"
      else (FilterArg.lookup args "all" 0).orElse (fun _ => FilterArg.lookup args "space" 0) |>.getD "bt709" |>.toLower
    if tgt != "bt709" && tgt != "bt601" && tgt != "bt2020" then
      throw s!"unsupported colorspace target: {tgt}"
    return (.vfColorspace tgt, [fmt])
  else if nm == "tonemap" then
    let [fmt] := inFmts | throw "tonemap expects 1 video input"
    if fmt.kind != .video || node.outputs.length != 1 then throw "tonemap media kind/arity mismatch"
    let md := (FilterArg.lookup args "tonemap" 0).getD "reinhard" |>.toLower
    if md != "reinhard" && md != "hable" && md != "mobius" && md != "clip" && md != "linear" then
      throw s!"unsupported tonemap mode: {md}"
    return (.vfTonemap md, [fmt])
  else if nm == "split" then
    let [fmt] := inFmts | throw "split expects 1 video input"
    if fmt.kind != .video then throw "split expects video input"
    let defOut := Nat.max 2 node.outputs.length
    let some k := FilterArg.lookupNat args "outputs" 0 defOut | throw "invalid split count"
    if k < 1 || node.outputs.length != k then
      throw s!"split count {k} does not match {node.outputs.length} output pads"
    return (.vfSplit k, List.replicate k fmt)
  else if nm == "overlay" then
    let [bg, fg] := inFmts | throw "overlay expects 2 video inputs"
    if bg.kind != .video || fg.kind != .video || node.outputs.length != 1 then
      throw "overlay requires 2 video inputs and 1 video output"
    let some ox := FilterArg.lookupNat args "x" 0 0 | throw "invalid overlay x"
    let some oy := FilterArg.lookupNat args "y" 1 0 | throw "invalid overlay y"
    return (.vfOverlay ox oy, [bg])
  else if nm == "vstack" then
    let some k := FilterArg.lookupNat args "inputs" 0 (Nat.max 2 inFmts.length) | throw "invalid vstack inputs"
    if k < 2 || inFmts.length != k || node.outputs.length != 1 then
      throw "vstack input/output arity mismatch"
    let some f0 := inFmts.head? | throw "vstack empty"
    if inFmts.any (fun f => f.kind != .video || f.width != f0.width) then
      throw "vstack requires video inputs of equal width"
    let totalH := inFmts.foldl (fun acc f => acc + f.height) 0
    return (.vfVstack k, [{ f0 with height := totalH }])
  else if nm == "hstack" then
    let some k := FilterArg.lookupNat args "inputs" 0 (Nat.max 2 inFmts.length) | throw "invalid hstack inputs"
    if k < 2 || inFmts.length != k || node.outputs.length != 1 then
      throw "hstack input/output arity mismatch"
    let some f0 := inFmts.head? | throw "hstack empty"
    if inFmts.any (fun f => f.kind != .video || f.height != f0.height) then
      throw "hstack requires video inputs of equal height"
    let totalW := inFmts.foldl (fun acc f => acc + f.width) 0
    return (.vfHstack k, [{ f0 with width := totalW }])
  -- 3. Audio filters
  else if nm == "volume" then
    let [fmt] := inFmts | throw "volume expects 1 audio input"
    if fmt.kind != .audio || node.outputs.length != 1 then throw "volume media kind/arity mismatch"
    let vStr := (FilterArg.lookup args "volume" 0).getD "1.0"
    let some gQ8 := parseVolumeGainQ8 vStr | throw s!"invalid volume gain: {vStr}"
    return (.afVolume gQ8, [fmt])
  else if nm == "aresample" then
    let [fmt] := inFmts | throw "aresample expects 1 audio input"
    if fmt.kind != .audio || node.outputs.length != 1 then throw "aresample media kind/arity mismatch"
    let some dstSr := FilterArg.lookupNat args "sample_rate" 0 fmt.sampleRate | throw "invalid aresample rate"
    if dstSr == 0 then throw "aresample rate must be positive"
    return (.afAresample dstSr, [{ fmt with sampleRate := dstSr }])
  else if nm == "pan" || nm == "aformat" then
    let [fmt] := inFmts | throw s!"{nm} expects 1 audio input"
    if fmt.kind != .audio || node.outputs.length != 1 then throw s!"{nm} media kind/arity mismatch"
    let clOpt := (FilterArg.lookup args "channel_layouts" 0).orElse (fun _ => FilterArg.lookup args "cl" 0)
    let dstCh ← match clOpt with
      | none => pure fmt.channels
      | some cs =>
        match parseChannelLayoutCount cs with
        | some c => pure c
        | none => throw s!"invalid {nm} channel layout: {cs}"
    let srStrOpt := (FilterArg.lookup args "sample_rates" 1).orElse (fun _ => FilterArg.lookup args "r" 1)
    let dstSr ← match srStrOpt with
      | none => pure fmt.sampleRate
      | some rs =>
        let first := (splitKeep rs '|').headD rs
        match first.toNat? with
        | some r => if r > 0 then pure r else throw s!"invalid {nm} sample rate: {rs}"
        | none => throw s!"invalid {nm} sample rate: {rs}"
    return (.afPanFormat dstSr dstCh, [{ fmt with sampleRate := dstSr, channels := dstCh }])
  else if nm == "atrim" then
    let [fmt] := inFmts | throw "atrim expects 1 audio input"
    if fmt.kind != .audio || node.outputs.length != 1 then throw "atrim media kind/arity mismatch"
    let sStr := (FilterArg.lookup args "start" 0).getD "0"
    let eStr := (FilterArg.lookup args "end" 1).orElse (fun _ => FilterArg.lookup args "duration" 1) |>.getD "60"
    let some sMs := parseDurationMillis sStr | throw s!"invalid atrim start: {sStr}"
    let some eMs := parseDurationMillis eStr | throw s!"invalid atrim end/duration: {eStr}"
    let endMs := if (FilterArg.lookup args "duration" 99).isSome then sMs + eMs else eMs
    return (.afAtrim sMs endMs, [fmt])
  else if nm == "anull" then
    let [fmt] := inFmts | throw "anull expects 1 audio input"
    if fmt.kind != .audio || node.outputs.length != 1 then throw "anull media kind/arity mismatch"
    return (.afAnull, [fmt])
  else if nm == "asplit" then
    let [fmt] := inFmts | throw "asplit expects 1 audio input"
    if fmt.kind != .audio then throw "asplit expects audio input"
    let defOut := Nat.max 2 node.outputs.length
    let some k := FilterArg.lookupNat args "outputs" 0 defOut | throw "invalid asplit count"
    if k < 1 || node.outputs.length != k then
      throw s!"asplit count {k} does not match {node.outputs.length} output pads"
    return (.afAsplit k, List.replicate k fmt)
  else if nm == "amix" then
    let some k := FilterArg.lookupNat args "inputs" 0 (Nat.max 2 inFmts.length) | throw "invalid amix inputs"
    let normNat := (FilterArg.lookupNat args "normalize" 99 1).getD 1
    if k < 2 || inFmts.length != k || node.outputs.length != 1 then
      throw "amix input/output arity mismatch"
    let some f0 := inFmts.head? | throw "amix empty"
    if inFmts.any (fun f => f.kind != .audio || f.sampleRate != f0.sampleRate) then
      throw "amix requires audio inputs with matching sample_rate"
    let outCh := inFmts.foldl (fun acc f => Nat.max acc f.channels) f0.channels
    return (.afAmix k (normNat != 0), [{ f0 with channels := outCh }])
  else if nm == "amerge" then
    let some k := FilterArg.lookupNat args "inputs" 0 (Nat.max 2 inFmts.length) | throw "invalid amerge inputs"
    if k < 2 || inFmts.length != k || node.outputs.length != 1 then
      throw "amerge input/output arity mismatch"
    let some f0 := inFmts.head? | throw "amerge empty"
    if inFmts.any (fun f => f.kind != .audio || f.sampleRate != f0.sampleRate) then
      throw "amerge requires audio inputs with matching sample_rate"
    let totalCh := inFmts.foldl (fun acc f => acc + f.channels) 0
    if totalCh > 8 then throw s!"amerge output channel count {totalCh} exceeds limit 8"
    return (.afAmerge k, [{ f0 with channels := totalCh }])
  else if nm == "concat" then
    let some nSeg := FilterArg.lookupNat args "n" 0 (Nat.max 2 inFmts.length) | throw "invalid concat n"
    let some vOut := FilterArg.lookupNat args "v" 1 1 | throw "invalid concat v"
    let some aOut := FilterArg.lookupNat args "a" 2 0 | throw "invalid concat a"
    if nSeg < 1 || node.outputs.length != vOut + aOut then
      throw "concat output pad count mismatch"
    if vOut == 1 && aOut == 0 then
      if inFmts.length != nSeg then throw "concat video input count mismatch"
      let some f0 := inFmts.head? | throw "concat empty"
      if inFmts.any (fun f => f.kind != .video || f.width != f0.width || f.height != f0.height) then
        throw "concat video inputs must all be video with matching dimensions"
      return (.vfConcatVideo nSeg, [f0])
    else if vOut == 0 && aOut == 1 then
      if inFmts.length != nSeg then throw "concat audio input count mismatch"
      let some f0 := inFmts.head? | throw "concat empty"
      if inFmts.any (fun f => f.kind != .audio || f.sampleRate != f0.sampleRate || f.channels != f0.channels) then
        throw "concat audio inputs must all be audio with matching sample_rate and channels"
      return (.afConcatAudio nSeg, [f0])
    else
      throw "concat supports either (v=1,a=0) or (v=0,a=1)"
  else
    throw s!"unsupported filter: {node.name}"

/-- Verify single-producer / single-consumer discipline on internal pad labels
and compile a `FilterGraph` into a `TypedFilterGraph` along its Kahn order. -/
def typecheckFilterGraph (g : FilterGraph) (externalInputs : List (String × PadFormat)) :
    Except String TypedFilterGraph := do
  if g.nodes.isEmpty then
    throw "filtergraph contains no filter nodes"
  -- Check duplicate output pad producers or duplicate input pad consumers
  let allOutputs := g.nodes.toList.flatMap (·.outputs) ++ externalInputs.map (·.1)
  if allOutputs.eraseDups.length != allOutputs.length then
    throw "duplicate output pad label in filtergraph"
  let allInputs := g.nodes.toList.flatMap (·.inputs)
  if allInputs.eraseDups.length != allInputs.length then
    throw "pad label consumed multiple times without split/asplit"
  let edges := graphEdges g
  let some order := kahnOrder g.nodes.size edges
    | throw "cyclic filtergraph rejected by Kahn topological checker"
  let mut env : List (String × PadFormat) := externalInputs
  let mut compiled : Array (Option TypedNode) := Array.replicate g.nodes.size none
  for idx in order do
    if hIdx : idx < g.nodes.size then
      let node := g.nodes[idx]
      let mut inFmts : List PadFormat := []
      for p in node.inputs do
        match lookupPadFormat env p with
        | some fmt => inFmts := inFmts ++ [fmt]
        | none => throw s!"unbound input pad [{p}] at filter {node.name}"
      let (op, outFmts) ← compileFilterNode node inFmts
      if outFmts.length != node.outputs.length then
        throw s!"output pad count mismatch at filter {node.name}"
      for (p, fmt) in List.zip node.outputs outFmts do
        env := env ++ [(p, fmt)]
      compiled := compiled.set! idx (some {
        op := op
        inputs := node.inputs
        outputs := node.outputs
        inFormats := inFmts
        outFormats := outFmts
      })
    else
      throw "internal Kahn index out of bounds"
  let mut typedNodes : Array TypedNode := #[]
  for optN in compiled do
    match optN with
    | some tn => typedNodes := typedNodes.push tn
    | none => throw "uncompiled node in filtergraph"
  let mut openOuts : List (String × PadFormat) := []
  for p in g.openOutputs do
    match lookupPadFormat env p with
    | some fmt => openOuts := openOuts ++ [(p, fmt)]
    | none => throw s!"missing format for open output [{p}]"
  if openOuts.isEmpty then
    throw "filtergraph has no open output pads"
  return {
    nodes := typedNodes
    topoOrder := order
    padEnv := env
    openInputs := g.openInputs
    openOutputs := openOuts
  }

/-! ## 7. Synthetic Source Generators (`color`, `testsrc`, `sine`, `nullsrc`, `anullsrc`) -/

/-- Maximum number of video frames materialized per lavfi run (bounded memory). -/
def maxLavfiVideoFrames : Nat := 300

/-- Maximum number of audio samples materialized per lavfi run (bounded memory). -/
def maxLavfiAudioSamples : Nat := 480000

/-- Frame count for `(fps, durationMs)`, clamped to `[1, maxLavfiVideoFrames]`. -/
def lavfiVideoFrameCount (fps durationMs : Nat) : Nat :=
  let raw := (fps * durationMs) / 1000
  Nat.min maxLavfiVideoFrames (Nat.max 1 raw)

/-- Sample count for `(sampleRate, durationMs)`, clamped to `[1, maxLavfiAudioSamples]`. -/
def lavfiAudioSampleCount (sampleRate durationMs : Nat) : Nat :=
  let raw := (sampleRate * durationMs) / 1000
  Nat.min maxLavfiAudioSamples (Nat.max 1 raw)

/-- Generate one studio-range BT.601 `yuv420p` frame for `color`. -/
def genColorVideoFrame (r g b : UInt8) (w h fps frameIdx : Nat) : VideoFrame :=
  let (y, u, v) := rgbToBt601Yuv r g b
  let tb := AVRational.mkSafe 1 (Nat.max 1 fps).toUInt64
  let cw := (w + 1) / 2
  let ch := (h + 1) / 2
  {
    width := w
    height := h
    pixFmt := .yuv420p
    colorMatrix := .bt601
    pts := frameIdx.toUInt64
    duration := 1
    timeBase := tb
    planes := #[Plane2D.alloc w h w y, Plane2D.alloc cw ch cw u, Plane2D.alloc cw ch cw v]
  }

/-- Generate one neutral `yuv420p` frame (`Y=16, U=128, V=128`) for `nullsrc`. -/
def genNullsrcVideoFrame (w h fps frameIdx : Nat) : VideoFrame :=
  VideoFrame.allocYuv420p w h frameIdx.toUInt64 (AVRational.mkSafe 1 (Nat.max 1 fps).toUInt64) .bt601

/-- Fill a solid grayscale `(val, val, val)` rectangle into a packed RGB24 `Plane2D`. -/
def fillRgbRect (rgb : Plane2D) (w h : Nat) (val : UInt8) (bx by0 bw bh : Nat) : Plane2D := Id.run do
  let mut out := rgb
  let yEnd := Nat.min h (by0 + bh)
  let xEnd := Nat.min w (bx + bw)
  for yy in [by0:yEnd] do
    for xx in [bx:xEnd] do
      out := out.setPixel yy (xx * 3) val
      out := out.setPixel yy (xx * 3 + 1) val
      out := out.setPixel yy (xx * 3 + 2) val
  return out

/-- 7-segment bitmask table (`0..9`) matching FFmpeg `vf_testsrc.c`. -/
def testsrcDigitMask (d : Nat) : Nat :=
  match d % 10 with
  | 0 => 1 ||| 2 ||| 8 ||| 16 ||| 32 ||| 64
  | 1 => 32 ||| 64
  | 2 => 1 ||| 4 ||| 2 ||| 32 ||| 16
  | 3 => 1 ||| 4 ||| 2 ||| 32 ||| 64
  | 4 => 4 ||| 8 ||| 32 ||| 64
  | 5 => 1 ||| 2 ||| 4 ||| 8 ||| 64
  | 6 => 1 ||| 2 ||| 4 ||| 8 ||| 16 ||| 64
  | 7 => 1 ||| 32 ||| 64
  | 8 => 1 ||| 2 ||| 4 ||| 8 ||| 16 ||| 32 ||| 64
  | _ => 1 ||| 2 ||| 4 ||| 8 ||| 32 ||| 64

/-- Render one 7-segment digit in `testsrc` at `(dx, dy)` when `w >= 80 && h >= 60`. -/
def drawTestsrcDigit (rgb : Plane2D) (w h digit dx dy dv dh : Nat) : Plane2D := Id.run do
  let mut out := fillRgbRect rgb w h 0 dx dy (7 * dv) (13 * dh)
  let m := testsrcDigitMask digit
  let segs : List (Nat × Nat × Nat × Nat × Nat) := [
    (dv, 0, 5 * dv, dh, 1),
    (dv, 12 * dh, 5 * dv, dh, 2),
    (dv, 6 * dh, 5 * dv, dh, 4),
    (0, dh, dv, 5 * dh, 8),
    (0, 7 * dh, dv, 5 * dh, 16),
    (6 * dv, dh, dv, 5 * dh, 32),
    (6 * dv, 7 * dh, dv, 5 * dh, 64)
  ]
  for (rx, ry, rw, rh, bit) in segs do
    if m &&& bit != 0 then
      out := fillRgbRect out w h 255 (dx + rx) (dy + ry) rw rh
  return out

/-- Convert packed `RGB24` `Plane2D` to studio-range BT.601 `yuv420p` with 2x2 chroma averaging. -/
def rgb24ToStudioYuv420p (rgb : Plane2D) (w h fps frameIdx : Nat) : VideoFrame := Id.run do
  let tb := AVRational.mkSafe 1 (Nat.max 1 fps).toUInt64
  let cw := (w + 1) / 2
  let ch := (h + 1) / 2
  let mut pY := Plane2D.alloc w h w 16
  let mut pU := Plane2D.alloc cw ch cw 128
  let mut pV := Plane2D.alloc cw ch cw 128
  for r in [:h] do
    for c in [:w] do
      let rv := rgb.getPixel r (c * 3)
      let gv := rgb.getPixel r (c * 3 + 1)
      let bv := rgb.getPixel r (c * 3 + 2)
      let (yv, _, _) := rgbToBt601Yuv rv gv bv
      pY := pY.setPixel r c yv
  for ur in [:ch] do
    for uc in [:cw] do
      let r0 := ur * 2
      let r1 := Nat.min (h - 1) (r0 + 1)
      let c0 := uc * 2
      let c1 := Nat.min (w - 1) (c0 + 1)
      let (_, u00, v00) := rgbToBt601Yuv (rgb.getPixel r0 (c0 * 3)) (rgb.getPixel r0 (c0 * 3 + 1)) (rgb.getPixel r0 (c0 * 3 + 2))
      let (_, u01, v01) := rgbToBt601Yuv (rgb.getPixel r0 (c1 * 3)) (rgb.getPixel r0 (c1 * 3 + 1)) (rgb.getPixel r0 (c1 * 3 + 2))
      let (_, u10, v10) := rgbToBt601Yuv (rgb.getPixel r1 (c0 * 3)) (rgb.getPixel r1 (c0 * 3 + 1)) (rgb.getPixel r1 (c0 * 3 + 2))
      let (_, u11, v11) := rgbToBt601Yuv (rgb.getPixel r1 (c1 * 3)) (rgb.getPixel r1 (c1 * 3 + 1)) (rgb.getPixel r1 (c1 * 3 + 2))
      let uAvg := ((u00.toNat + u01.toNat + u10.toNat + u11.toNat + 2) / 4).toUInt8
      let vAvg := ((v00.toNat + v01.toNat + v10.toNat + v11.toNat + 2) / 4).toUInt8
      pU := pU.setPixel ur uc uAvg
      pV := pV.setPixel ur uc vAvg
  return {
    width := w
    height := h
    pixFmt := .yuv420p
    colorMatrix := .bt601
    pts := frameIdx.toUInt64
    duration := 1
    timeBase := tb
    planes := #[pY, pU, pV]
  }

/-- Generate one `RGB24` plane for FFmpeg `testsrc` (exact 8 bars, inner circle, HSV band, 7-seg digits). -/
def genTestsrcRgbPlane (w h fps frameIdx : Nat) : Plane2D := Id.run do
  let mut rgb := Plane2D.alloc (w * 3) h (w * 3) 0
  let barW := Nat.max 1 (w / 8)
  let cx := w / 2
  let cy := h / 2
  let rad := (w + h) / 4
  let rad2 := rad * rad
  let ymin := (h * 3) / 4
  let ymax := (h * 7) / 8
  let grad0 := (256 * frameIdx) / 10
  let step := (6 * 256) / Nat.max 1 w
  let rem := (6 * 256) % Nat.max 1 w
  for y in [:h] do
    let mut grad := grad0
    let mut err : Nat := 0
    for x in [:w] do
      let i0 := Nat.min 7 (x / barW)
      let dx := if x >= cx then x - cx else cx - x
      let dy := if y >= cy then y - cy else cy - y
      let i := if w >= 16 && h >= 16 && dx * dx + dy * dy < rad2 then 7 - i0 else i0
      let mut r : UInt8 := if i &&& 1 != 0 then 255 else 0
      let mut g : UInt8 := if i &&& 2 != 0 then 255 else 0
      let mut b : UInt8 := if i &&& 4 != 0 then 255 else 0
      if y >= ymin && y <= ymax then
        let gm := grad % (6 * 256)
        let seg := gm / 256
        let r256 := gm % 256
        let rv := r256.toUInt8
        let iv := (255 - r256).toUInt8
        match seg with
        | 0 => r := 255; g := rv; b := 0
        | 1 => r := iv; g := 255; b := 0
        | 2 => r := 0; g := 255; b := rv
        | 3 => r := 0; g := iv; b := 255
        | 4 => r := rv; g := 0; b := 255
        | _ => r := 255; g := 0; b := iv
        grad := grad + step
        err := err + rem
        if err >= 6 * 256 then
          err := err - 6 * 256
          grad := grad + 1
      rgb := rgb.setPixel y (x * 3) r
      rgb := rgb.setPixel y (x * 3 + 1) g
      rgb := rgb.setPixel y (x * 3 + 2) b
  if w >= 80 && h >= 60 then
    let dv := w / 80
    let dh := h / 60
    let sec := frameIdx / Nat.max 1 fps
    let digits := (toString sec).toList.reverse
    let mut dx := w - 16 * dv
    let dy := (h - 13 * dh) / 2
    for ch in digits do
      let d := ch.toNat - '0'.toNat
      if dx < w then
        rgb := drawTestsrcDigit rgb w h d dx dy dv dh
      dx := if dx >= 9 * dv then dx - 9 * dv else w
  return rgb

/-- Generate one `testsrc` `VideoFrame` (`yuv420p`). -/
def genTestsrcVideoFrame (w h fps frameIdx : Nat) : VideoFrame :=
  rgb24ToStudioYuv420p (genTestsrcRgbPlane w h fps frameIdx) w h fps frameIdx

/-- Fixed-point 7th-order Taylor `sin(2π·f·n/sr) * 4095` (`1/8` full-scale `s16le`, ≤2 LSB vs FFmpeg). -/
def evalSineSample4095 (freqHz sampleRate sampleIdx : Nat) : Int32 :=
  if sampleRate == 0 || freqHz == 0 then 0
  else
    let x0 := ((freqHz * sampleIdx) % sampleRate) * 4194304 / sampleRate
    let half := 2097152
    let neg := x0 >= half
    let x1 := if neg then x0 - half else x0
    let q := 1048576
    let x := if x1 > q then half - x1 else x1
    let xi : Int := Int.ofNat x
    let t2 : Int := (xi * xi) / 1048576
    let p5 : Int := 1337020 - (78547 * t2) / 1048576
    let p3 : Int := -10837479 + (p5 * t2) / 1048576
    let p1 : Int := 26353589 + (p3 * t2) / 1048576
    let sinQ24 : Int := Nat.min 16777216 ((xi * p1) / 1048576).toNat
    let mag : Int := (sinQ24 * 4095) / 16777216
    clipInt16 (Int32.ofInt (if neg then -mag else mag))

/-- Generate a mono `AudioFrame` for `sine`. -/
def genSineAudioFrame (freqHz sampleRate durationMs : Nat) : AudioFrame :=
  let n := lavfiAudioSampleCount sampleRate durationMs
  let samples := (List.range n).toArray.map (fun i => evalSineSample4095 freqHz sampleRate i)
  {
    sampleFmt := .s16p
    sampleRate := sampleRate.toUInt32
    channels := 1
    numSamples := n
    pts := 0
    duration := n.toUInt64
    timeBase := AVRational.mkSafe 1 (Nat.max 1 sampleRate).toUInt64
    samples := samples
  }

/-- Generate a silent `AudioFrame` for `anullsrc`. -/
def genAnullsrcAudioFrame (sampleRate channels durationMs : Nat) : AudioFrame :=
  let n := lavfiAudioSampleCount sampleRate durationMs
  AudioFrame.alloc .s16p sampleRate.toUInt32 (Nat.max 1 channels).toUInt32 n 0

/-! ## 8. Video & Audio Stage Executors (16 Video + 9 Audio Filters) -/

/-- Crop all three planes of a `yuv420p` `VideoFrame` via `LeanAV.Filter.filterPlaneCrop`. -/
def execVideoCrop (vf : VideoFrame) (x0 y0 cw ch : Nat) : VideoFrame :=
  if vf.planes.size < 3 then vf
  else
    let pY := filterPlaneCrop vf.planes[0]! x0 y0 cw ch
    let pU := filterPlaneCrop vf.planes[1]! (x0 / 2) (y0 / 2) (cw / 2) (ch / 2)
    let pV := filterPlaneCrop vf.planes[2]! (x0 / 2) (y0 / 2) (cw / 2) (ch / 2)
    { vf with width := cw, height := ch, planes := #[pY, pU, pV] }

/-- Pad all three planes of a `yuv420p` `VideoFrame` via `LeanAV.Filter.filterPlanePad`. -/
def execVideoPad (vf : VideoFrame) (pw ph ox oy : Nat) (fr fg fb : UInt8) : VideoFrame :=
  if vf.planes.size < 3 then vf
  else
    let (fy, fu, fv) := rgbToBt601Yuv fr fg fb
    let pY := filterPlanePad vf.planes[0]! pw ph ox oy fy
    let pU := filterPlanePad vf.planes[1]! (pw / 2) (ph / 2) (ox / 2) (oy / 2) fu
    let pV := filterPlanePad vf.planes[2]! (pw / 2) (ph / 2) (ox / 2) (oy / 2) fv
    { vf with width := pw, height := ph, planes := #[pY, pU, pV] }

/-- Apply `eq` / `negate` via `LeanAV.Filter.filterPlanePointFused`. -/
def execVideoEq (vf : VideoFrame) (cQ8 bVal : Int32) (inv : Bool) : VideoFrame :=
  if vf.planes.size < 3 then vf
  else
    let pY := filterPlanePointFused vf.planes[0]! cQ8 bVal inv
    let pU := if inv then filterPlanePointFused vf.planes[1]! 256 0 true else vf.planes[1]!
    let pV := if inv then filterPlanePointFused vf.planes[2]! 256 0 true else vf.planes[2]!
    { vf with planes := #[pY, pU, pV] }

/-- Apply `boxblur` (`radius` passes of `filterPlaneBoxBlur3x3`). -/
def execVideoBoxblur (vf : VideoFrame) (radius : Nat) : VideoFrame := Id.run do
  if vf.planes.size < 3 then return vf
  let passes := Nat.min 4 (Nat.max 1 radius)
  let mut pY := vf.planes[0]!
  let mut pU := vf.planes[1]!
  let mut pV := vf.planes[2]!
  for _ in [:passes] do
    pY := filterPlaneBoxBlur3x3 pY
    pU := filterPlaneBoxBlur3x3 pU
    pV := filterPlaneBoxBlur3x3 pV
  return { vf with planes := #[pY, pU, pV] }

/-- Apply `hflip` across luma and chroma via `LeanAV.Filter.filterPlaneHFlip`. -/
def execVideoHflip (vf : VideoFrame) : VideoFrame :=
  if vf.planes.size < 3 then vf
  else
    { vf with planes := #[
        filterPlaneHFlip vf.planes[0]!,
        filterPlaneHFlip vf.planes[1]!,
        filterPlaneHFlip vf.planes[2]!] }

/-- Apply `vflip` across luma and chroma via `LeanAV.Filter.filterPlaneVFlip`. -/
def execVideoVflip (vf : VideoFrame) : VideoFrame :=
  if vf.planes.size < 3 then vf
  else
    { vf with planes := #[
        filterPlaneVFlip vf.planes[0]!,
        filterPlaneVFlip vf.planes[1]!,
        filterPlaneVFlip vf.planes[2]!] }

/-- Apply `format` (`gray` neutralizes chroma to `128`; named high-bit formats select their matrix). -/
def execVideoFormat (vf : VideoFrame) (pf : String) : VideoFrame :=
  if vf.planes.size < 3 then vf
  else if pf == "gray" then
    let cw := (vf.width + 1) / 2
    let ch := (vf.height + 1) / 2
    { vf with planes := #[vf.planes[0]!, Plane2D.alloc cw ch cw 128, Plane2D.alloc cw ch cw 128] }
  else
    match PixelFormat.parse pf with
    | some parsed =>
      let cm :=
        if parsed.bitDepth ≥ 10 &&
            (parsed == .yuv420p10le || parsed == .yuv422p10le || parsed == .yuv444p10le ||
             parsed == .yuv420p12le || parsed == .yuv422p12le || parsed == .yuv444p12le ||
             parsed == .p010le || parsed == .gbrp10le) then
          .bt2020ncl
        else vf.colorMatrix
      { vf with colorMatrix := cm }
    | none => vf

/-- Composite opaque foreground `fg` onto background `bg` at `(ox, oy)` via `filterPlaneOverlay` (`alphaQ8=256`). -/
def execVideoOverlay (bg fg : VideoFrame) (ox oy : Nat) : VideoFrame :=
  if bg.planes.size < 3 || fg.planes.size < 3 then bg
  else
    let pY := filterPlaneOverlay bg.planes[0]! fg.planes[0]! ox oy 256
    let pU := filterPlaneOverlay bg.planes[1]! fg.planes[1]! (ox / 2) (oy / 2) 256
    let pV := filterPlaneOverlay bg.planes[2]! fg.planes[2]! (ox / 2) (oy / 2) 256
    { bg with planes := #[pY, pU, pV] }

/-- Stack equal-width `Plane2D`s vertically. -/
def stackPlanesVertical (ps : List Plane2D) : Plane2D := Id.run do
  let w := (ps.head?.map (·.width)).getD 0
  let totalH := ps.foldl (fun acc p => acc + p.height) 0
  let mut out := Plane2D.alloc w totalH w 16
  let mut yOff : Nat := 0
  for p in ps do
    for r in [:p.height] do
      for c in [:w] do
        out := out.setPixel (yOff + r) c (p.getPixel r c)
    yOff := yOff + p.height
  return out

/-- Stack equal-height `Plane2D`s horizontally. -/
def stackPlanesHorizontal (ps : List Plane2D) : Plane2D := Id.run do
  let h := (ps.head?.map (·.height)).getD 0
  let totalW := ps.foldl (fun acc p => acc + p.width) 0
  let mut out := Plane2D.alloc totalW h totalW 16
  let mut xOff : Nat := 0
  for p in ps do
    for r in [:h] do
      for c in [:p.width] do
        out := out.setPixel r (xOff + c) (p.getPixel r c)
    xOff := xOff + p.width
  return out

/-- Stack video frames vertically (`vstack`). -/
def execVideoVstack (frames : List VideoFrame) : VideoFrame :=
  match frames.head? with
  | none => default
  | some f0 =>
    let totalH := frames.foldl (fun acc f => acc + f.height) 0
    let pY := stackPlanesVertical (frames.map (fun f => f.planes.getD 0 (Plane2D.alloc 0 0 0 16)))
    let pU := stackPlanesVertical (frames.map (fun f => f.planes.getD 1 (Plane2D.alloc 0 0 0 128)))
    let pV := stackPlanesVertical (frames.map (fun f => f.planes.getD 2 (Plane2D.alloc 0 0 0 128)))
    { f0 with height := totalH, planes := #[pY, pU, pV] }

/-- Stack video frames horizontally (`hstack`). -/
def execVideoHstack (frames : List VideoFrame) : VideoFrame :=
  match frames.head? with
  | none => default
  | some f0 =>
    let totalW := frames.foldl (fun acc f => acc + f.width) 0
    let pY := stackPlanesHorizontal (frames.map (fun f => f.planes.getD 0 (Plane2D.alloc 0 0 0 16)))
    let pU := stackPlanesHorizontal (frames.map (fun f => f.planes.getD 1 (Plane2D.alloc 0 0 0 128)))
    let pV := stackPlanesHorizontal (frames.map (fun f => f.planes.getD 2 (Plane2D.alloc 0 0 0 128)))
    { f0 with width := totalW, planes := #[pY, pU, pV] }

/-- Resample/remap an `AudioFrame` to `(dstRate, dstCh)` (`pan` / `aformat`). -/
def execAudioPanFormat (af : AudioFrame) (dstRate dstCh : Nat) : AudioFrame := Id.run do
  let afSr := if af.sampleRate.toNat == dstRate then af else resampleAudioFrame af dstRate.toUInt32
  let srcCh := Nat.max 1 afSr.channels.toNat
  let tgtCh := Nat.max 1 dstCh
  if srcCh == tgtCh then return afSr
  if srcCh == 2 && tgtCh == 1 then return downmixStereoToMono afSr
  let mut out := AudioFrame.alloc afSr.sampleFmt afSr.sampleRate tgtCh.toUInt32 afSr.numSamples afSr.pts
  for ch in [:tgtCh] do
    let mapCh := ch % srcCh
    for i in [:afSr.numSamples] do
      out := out.setSample ch i (afSr.getSample mapCh i)
  return out

/-- Trim an `AudioFrame` to `[startMs, endMs)`. -/
def execAudioTrim (af : AudioFrame) (startMs endMs : Nat) : AudioFrame := Id.run do
  let sr := Nat.max 1 af.sampleRate.toNat
  let sIdx := Nat.min af.numSamples ((sr * startMs) / 1000)
  let eIdx := Nat.min af.numSamples ((sr * Nat.max startMs endMs) / 1000)
  let outN := eIdx - sIdx
  let nCh := Nat.max 1 af.channels.toNat
  let mut out := AudioFrame.alloc af.sampleFmt af.sampleRate nCh.toUInt32 outN af.pts
  for ch in [:nCh] do
    for i in [:outN] do
      out := out.setSample ch i (af.getSample ch (sIdx + i))
  return out

/-- Mix multiple `AudioFrame`s (`amix`: normalized average when `normalize = true`). -/
def execAudioAmix (inputs : List AudioFrame) (normalize : Bool) : AudioFrame := Id.run do
  let some f0 := inputs.head? | return default
  let k := Nat.max 1 inputs.length
  let outCh := inputs.foldl (fun acc f => Nat.max acc f.channels.toNat) (Nat.max 1 f0.channels.toNat)
  let outN := inputs.foldl (fun acc f => Nat.min acc f.numSamples) f0.numSamples
  let mut out := AudioFrame.alloc f0.sampleFmt f0.sampleRate outCh.toUInt32 outN f0.pts
  for ch in [:outCh] do
    for i in [:outN] do
      let mut sum : Int := 0
      for f in inputs do
        let srcCh := if ch < f.channels.toNat then ch else 0
        sum := sum + (f.getSample srcCh i).toInt
      let mixed : Int := if normalize then sum / (Int.ofNat k) else sum
      out := out.setSample ch i (clipInt16 (Int32.ofInt mixed))
  return out

/-- Merge channels across multiple `AudioFrame`s (`amerge`, e.g. 2 mono -> 1 stereo). -/
def execAudioAmerge (inputs : List AudioFrame) : AudioFrame := Id.run do
  let some f0 := inputs.head? | return default
  let totalCh := inputs.foldl (fun acc f => acc + Nat.max 1 f.channels.toNat) 0
  let outN := inputs.foldl (fun acc f => Nat.min acc f.numSamples) f0.numSamples
  let mut out := AudioFrame.alloc f0.sampleFmt f0.sampleRate totalCh.toUInt32 outN f0.pts
  let mut dstCh : Nat := 0
  for f in inputs do
    let fCh := Nat.max 1 f.channels.toNat
    for c in [:fCh] do
      for i in [:outN] do
        out := out.setSample dstCh i (f.getSample c i)
      dstCh := dstCh + 1
  return out

/-- Concatenate multiple `AudioFrame`s sequentially (`concat=v=0:a=1`). -/
def execAudioConcat (inputs : List AudioFrame) : AudioFrame := Id.run do
  let some f0 := inputs.head? | return default
  let nCh := Nat.max 1 f0.channels.toNat
  let totalN := inputs.foldl (fun acc f => acc + f.numSamples) 0
  let mut out := AudioFrame.alloc f0.sampleFmt f0.sampleRate nCh.toUInt32 totalN f0.pts
  let mut off : Nat := 0
  for f in inputs do
    for c in [:nCh] do
      for i in [:f.numSamples] do
        out := out.setSample c (off + i) (f.getSample c i)
    off := off + f.numSamples
  return out

/-! ## 9. Bounded-Queue Topological DAG Executor -/

/-- Drain all `VideoFrame`s from a pad's `EdgeBufferQueue`. -/
def drainVideoQueue (q : EdgeBufferQueue) : Array VideoFrame := Id.run do
  let mut out : Array VideoFrame := #[]
  for item in q.items do
    match item with
    | .video vf => out := out.push vf
    | .audio _ => pure ()
  return out

/-- Drain and merge all `AudioFrame`s from a pad's `EdgeBufferQueue` into one contiguous `AudioFrame`. -/
def drainAudioQueue (q : EdgeBufferQueue) : AudioFrame :=
  let frames := q.items.toList.filterMap (fun m => match m with | .audio af => some af | .video _ => none)
  execAudioConcat frames

/-- Build a bounded `EdgeBufferQueue` carrying video frames. -/
def buildVideoQueue (cap : Nat) (frames : Array VideoFrame) : EdgeBufferQueue :=
  frames.toList.foldl (fun q vf => EdgeBufferQueue.push q (.video vf))
    (EdgeBufferQueue.empty (Nat.max cap frames.size))

/-- Build a bounded `EdgeBufferQueue` carrying one audio frame. -/
def buildAudioQueue (cap : Nat) (af : AudioFrame) : EdgeBufferQueue :=
  EdgeBufferQueue.push (EdgeBufferQueue.empty (Nat.max 1 cap)) (.audio af)

/-- Execute one compiled `TypedNode` against the pad queue map. -/
def executeTypedNode (node : TypedNode) (padMap : List (String × EdgeBufferQueue))
    (queueCap : Nat := maxLavfiVideoFrames) : Except String (List (String × EdgeBufferQueue)) := do
  let lookupQ (p : String) : Except String EdgeBufferQueue :=
    match (padMap.find? (fun kv => kv.1 == p)).map (·.2) with
    | some q => pure q
    | none => throw s!"missing runtime queue for pad [{p}]"
  let singleOut (q : EdgeBufferQueue) : List (String × EdgeBufferQueue) :=
    match node.outputs with
    | [o] => [(o, q)]
    | _ => []
  match node.op with
  | .srcColor r g b w h fps durMs =>
    let n := lavfiVideoFrameCount fps durMs
    let frames := (Array.range n).map (fun idx => genColorVideoFrame r g b w h fps idx)
    return singleOut (buildVideoQueue queueCap frames)
  | .srcTestsrc w h fps durMs =>
    let n := lavfiVideoFrameCount fps durMs
    let frames := (Array.range n).map (fun idx => genTestsrcVideoFrame w h fps idx)
    return singleOut (buildVideoQueue queueCap frames)
  | .srcNullsrc w h fps durMs =>
    let n := lavfiVideoFrameCount fps durMs
    let frames := (Array.range n).map (fun idx => genNullsrcVideoFrame w h fps idx)
    return singleOut (buildVideoQueue queueCap frames)
  | .srcSine freq sr durMs =>
    return singleOut (buildAudioQueue 4 (genSineAudioFrame freq sr durMs))
  | .srcAnullsrc sr ch durMs =>
    return singleOut (buildAudioQueue 4 (genAnullsrcAudioFrame sr ch durMs))
  | .vfScale dstW dstH =>
    let q ← lookupQ (node.inputs.headD "")
    let vfs := (drainVideoQueue q).map (fun vf => scaleVideoFrameYuv420p vf dstW dstH)
    return singleOut (buildVideoQueue queueCap vfs)
  | .vfCrop x0 y0 cw ch =>
    let q ← lookupQ (node.inputs.headD "")
    let vfs := (drainVideoQueue q).map (fun vf => execVideoCrop vf x0 y0 cw ch)
    return singleOut (buildVideoQueue queueCap vfs)
  | .vfPad pw ph ox oy fr fg fb =>
    let q ← lookupQ (node.inputs.headD "")
    let vfs := (drainVideoQueue q).map (fun vf => execVideoPad vf pw ph ox oy fr fg fb)
    return singleOut (buildVideoQueue queueCap vfs)
  | .vfEq cQ8 bVal inv =>
    let q ← lookupQ (node.inputs.headD "")
    let vfs := (drainVideoQueue q).map (fun vf => execVideoEq vf cQ8 bVal inv)
    return singleOut (buildVideoQueue queueCap vfs)
  | .vfBoxblur rad =>
    let q ← lookupQ (node.inputs.headD "")
    let vfs := (drainVideoQueue q).map (fun vf => execVideoBoxblur vf rad)
    return singleOut (buildVideoQueue queueCap vfs)
  | .vfHflip =>
    let q ← lookupQ (node.inputs.headD "")
    return singleOut (buildVideoQueue queueCap ((drainVideoQueue q).map execVideoHflip))
  | .vfVflip =>
    let q ← lookupQ (node.inputs.headD "")
    return singleOut (buildVideoQueue queueCap ((drainVideoQueue q).map execVideoVflip))
  | .vfFormat pf =>
    let q ← lookupQ (node.inputs.headD "")
    return singleOut (buildVideoQueue queueCap ((drainVideoQueue q).map (fun vf => execVideoFormat vf pf)))
  | .vfFps targetFps =>
    let q ← lookupQ (node.inputs.headD "")
    let srcFrames := drainVideoQueue q
    let srcFps := (node.inFormats.head?.map (·.fpsNum)).getD 25
    let outCount := Nat.max 1 ((srcFrames.size * targetFps) / Nat.max 1 srcFps)
    let outFrames := (Array.range outCount).map (fun i =>
      let srcIdx := Nat.min (srcFrames.size - 1) ((i * Nat.max 1 srcFps) / Nat.max 1 targetFps)
      let base := srcFrames.getD srcIdx default
      { base with pts := i.toUInt64, timeBase := AVRational.mkSafe 1 (Nat.max 1 targetFps).toUInt64 })
    return singleOut (buildVideoQueue queueCap outFrames)
  | .vfTrim sMs eMs =>
    let q ← lookupQ (node.inputs.headD "")
    let srcFrames := drainVideoQueue q
    let fps := Nat.max 1 ((node.inFormats.head?.map (·.fpsNum)).getD 25)
    let sIdx := Nat.min srcFrames.size ((fps * sMs) / 1000)
    let eIdx := Nat.min srcFrames.size ((fps * Nat.max sMs eMs) / 1000)
    let sliced := srcFrames.extract sIdx (Nat.max (Nat.min srcFrames.size (sIdx + 1)) eIdx)
    return singleOut (buildVideoQueue queueCap sliced)
  | .vfNull =>
    let q ← lookupQ (node.inputs.headD "")
    return singleOut q
  | .vfSplit _ =>
    let q ← lookupQ (node.inputs.headD "")
    return node.outputs.map (fun o => (o, q))
  | .vfOverlay ox oy =>
    match node.inputs with
    | [bgP, fgP] =>
      let bgFrames := drainVideoQueue (← lookupQ bgP)
      let fgFrames := drainVideoQueue (← lookupQ fgP)
      let n := bgFrames.size
      let outFrames := (Array.range n).map (fun i =>
        let bg := bgFrames.getD i default
        let fg := if fgFrames.isEmpty then bg else fgFrames.getD (Nat.min (fgFrames.size - 1) i) default
        execVideoOverlay bg fg ox oy)
      return singleOut (buildVideoQueue queueCap outFrames)
    | _ => throw "overlay runtime input mismatch"
  | .vfVstack _ =>
    let qs ← node.inputs.mapM lookupQ
    let streams := qs.map drainVideoQueue
    let n := streams.foldl (fun acc arr => if acc == 0 then arr.size else Nat.min acc arr.size) 0
    let outFrames := (Array.range n).map (fun i =>
      execVideoVstack (streams.map (fun arr => arr.getD i default)))
    return singleOut (buildVideoQueue queueCap outFrames)
  | .vfHstack _ =>
    let qs ← node.inputs.mapM lookupQ
    let streams := qs.map drainVideoQueue
    let n := streams.foldl (fun acc arr => if acc == 0 then arr.size else Nat.min acc arr.size) 0
    let outFrames := (Array.range n).map (fun i =>
      execVideoHstack (streams.map (fun arr => arr.getD i default)))
    return singleOut (buildVideoQueue queueCap outFrames)
  | .vfConcatVideo _ =>
    let qs ← node.inputs.mapM lookupQ
    let outFrames := qs.foldl (fun acc q => acc ++ drainVideoQueue q) #[]
    return singleOut (buildVideoQueue (Nat.max queueCap outFrames.size) outFrames)
  | .vfColorspace tgt =>
    let q ← lookupQ (node.inputs.headD "")
    let vfs := (drainVideoQueue q).map (fun vf => filterVideoColorspace vf tgt)
    return singleOut (buildVideoQueue queueCap vfs)
  | .vfTonemap mode =>
    let q ← lookupQ (node.inputs.headD "")
    let vfs := (drainVideoQueue q).map (fun vf => filterVideoTonemap vf mode)
    return singleOut (buildVideoQueue queueCap vfs)
  | .afVolume gQ8 =>
    let af := drainAudioQueue (← lookupQ (node.inputs.headD ""))
    return singleOut (buildAudioQueue 4 (filterAudioVolumeQ8 af gQ8))
  | .afAresample dstSr =>
    let af := drainAudioQueue (← lookupQ (node.inputs.headD ""))
    return singleOut (buildAudioQueue 4 (resampleAudioFrame af dstSr.toUInt32))
  | .afPanFormat dstSr dstCh =>
    let af := drainAudioQueue (← lookupQ (node.inputs.headD ""))
    return singleOut (buildAudioQueue 4 (execAudioPanFormat af dstSr dstCh))
  | .afAtrim sMs eMs =>
    let af := drainAudioQueue (← lookupQ (node.inputs.headD ""))
    return singleOut (buildAudioQueue 4 (execAudioTrim af sMs eMs))
  | .afAnull =>
    let q ← lookupQ (node.inputs.headD "")
    return singleOut q
  | .afAsplit _ =>
    let q ← lookupQ (node.inputs.headD "")
    return node.outputs.map (fun o => (o, q))
  | .afAmix _ norm =>
    let qs ← node.inputs.mapM lookupQ
    return singleOut (buildAudioQueue 4 (execAudioAmix (qs.map drainAudioQueue) norm))
  | .afAmerge _ =>
    let qs ← node.inputs.mapM lookupQ
    return singleOut (buildAudioQueue 4 (execAudioAmerge (qs.map drainAudioQueue)))
  | .afConcatAudio _ =>
    let qs ← node.inputs.mapM lookupQ
    return singleOut (buildAudioQueue 4 (execAudioConcat (qs.map drainAudioQueue)))

/-- Execute an entire `TypedFilterGraph` in Kahn topological order. -/
def executeTypedFilterGraph (tg : TypedFilterGraph)
    (externalQueues : List (String × EdgeBufferQueue) := []) :
    Except String (List (String × PadFormat × EdgeBufferQueue)) := do
  let mut padMap := externalQueues
  for idx in tg.topoOrder do
    if h : idx < tg.nodes.size then
      let produced ← executeTypedNode tg.nodes[idx] padMap
      padMap := padMap ++ produced
    else
      throw "topological node index out of bounds"
  let mut outs : List (String × PadFormat × EdgeBufferQueue) := []
  for (p, fmt) in tg.openOutputs do
    match (padMap.find? (fun kv => kv.1 == p)).map (·.2) with
    | some q => outs := outs ++ [(p, fmt, q)]
    | none => throw s!"missing output queue for [{p}]"
  return outs

/-- Pack planar `yuv420p` `VideoFrame`s into raw contiguous I420 bytes. -/
def packVideoFramesYuv420pRaw (frames : Array VideoFrame) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for vf in frames do
    if vf.planes.size >= 3 then
      for pIdx in [:3] do
        let p := vf.planes[pIdx]!
        for r in [:p.height] do
          for c in [:p.width] do
            out := out.push (p.getPixel r c)
  return out

/-- Pack `VideoFrame`s into raw `RGB24` bytes (studio BT.601 decode). -/
def packVideoFramesRgb24Raw (frames : Array VideoFrame) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for vf in frames do
    let rgb := yuv420pToRgb24Plane { vf with colorMatrix := .bt601 }
    for r in [:vf.height] do
      for c in [:vf.width * 3] do
        out := out.push (rgb.getPixel r c)
  return out

/-- Pack `VideoFrame`s into raw `GRAY8` luma bytes. -/
def packVideoFramesGray8Raw (frames : Array VideoFrame) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for vf in frames do
    if vf.planes.size >= 1 then
      let p := vf.planes[0]!
      for r in [:vf.height] do
        for c in [:vf.width] do
          out := out.push (p.getPixel r c)
  return out

/-- Direct RGB24 emission when a graph is a single `testsrc` node, avoiding 4:2:0 subsampling loss. -/
def packDirectTestsrcRgb24? (tg : TypedFilterGraph) (srcIndices? : Option (Array Nat) := none) : Option ByteArray :=
  if tg.nodes.size != 1 then none
  else
    match tg.nodes[0]!.op with
    | .srcTestsrc w h fps durMs =>
      let n0 := lavfiVideoFrameCount fps durMs
      let indices : Array Nat :=
        match srcIndices? with
        | some idxs => if n0 == 0 then #[] else idxs.map (fun idx => Nat.min (n0 - 1) idx)
        | none => Array.range n0
      some <| Id.run do
        let mut out := ByteArray.emptyWithCapacity (indices.size * w * h * 3)
        for idx in indices do
          let rgb := genTestsrcRgbPlane w h fps idx
          for r in [:h] do
            for c in [:w * 3] do
              out := out.push (rgb.getPixel r c)
        return out
    | _ => none

/-- Convert an `AudioFrame` into per-channel `Array (Array Int32)` for WAV/FLAC/PCM muxers. -/
def audioFrameToChannelArrays (af : AudioFrame) : Array (Array Int32) := Id.run do
  let nCh := Nat.max 1 af.channels.toNat
  let mut chans : Array (Array Int32) := #[]
  for ch in [:nCh] do
    let mut arr := Array.emptyWithCapacity af.numSamples
    for i in [:af.numSamples] do
      arr := arr.push (af.getSample ch i)
    chans := chans.push arr
  return chans

/-- Convert per-channel `Array (Array Int32)` into a planar `AudioFrame`. -/
def channelArraysToAudioFrame (chans : Array (Array Int32)) (sampleRate : UInt32)
    (bitsPerSample : Nat := 16) : AudioFrame := Id.run do
  let nCh := Nat.max 1 chans.size
  let nS := (chans.getD 0 #[]).size
  let mut af := AudioFrame.alloc (if bitsPerSample > 16 then .s32p else .s16p) sampleRate nCh.toUInt32 nS 0
  for ch in [:chans.size] do
    let arr := chans[ch]!
    for i in [:Nat.min nS arr.size] do
      af := af.setSample ch i (if bitsPerSample > 16 then arr[i]! else clipInt16 arr[i]!)
  return af

/-! ## 10. Lossless All-Intra `I_PCM` H.264 + AAC-LC Synthetic MP4 Muxer -/

private def lavfiChooseH264Level (mbsW mbsH : Nat) : UInt8 :=
  let mbs := mbsW * mbsH
  if mbs ≤ 99 then 12
  else if mbs ≤ 396 then 20
  else if mbs ≤ 1620 then 30
  else if mbs ≤ 3600 then 31
  else if mbs ≤ 8192 then 40
  else 51

private def lavfiBitWriterBits (w : BitWriter) : Array UInt8 :=
  let totalBits := w.bytes.size * 8 + w.bitsUsed
  let bytes := (w.alignToByte).toByteArray
  extractBitArray bytes 0 totalBits

private def packYuv420pMbPcmBytes (vf : VideoFrame) (mbX mbY : Nat) : ByteArray := Id.run do
  let pY := vf.planes[0]!
  let pU := vf.planes[1]!
  let pV := vf.planes[2]!
  let w := Nat.max 1 vf.width
  let h := Nat.max 1 vf.height
  let cw := Nat.max 1 ((w + 1) / 2)
  let ch := Nat.max 1 ((h + 1) / 2)
  let mut out := ByteArray.emptyWithCapacity 384
  for ry in [:16] do
    let y := Nat.min (h - 1) (mbY * 16 + ry)
    for rx in [:16] do
      let x := Nat.min (w - 1) (mbX * 16 + rx)
      out := out.push (pY.getPixel y x)
  for ry in [:8] do
    let y := Nat.min (ch - 1) (mbY * 8 + ry)
    for rx in [:8] do
      let x := Nat.min (cw - 1) (mbX * 8 + rx)
      out := out.push (pU.getPixel y x)
  for ry in [:8] do
    let y := Nat.min (ch - 1) (mbY * 8 + ry)
    for rx in [:8] do
      let x := Nat.min (cw - 1) (mbX * 8 + rx)
      out := out.push (pV.getPixel y x)
  return out

/-- Build a `SynthMp4Track` containing all-IDR `I_PCM` H.264 frames for `frames`. -/
def muxLavfiVideoH264Track (frames : Array VideoFrame) (fpsNum : Nat) : Option SynthMp4Track := do
  let vf0 ← frames[0]?
  let dstW := vf0.width
  let dstH := vf0.height
  if dstW == 0 || dstH == 0 || dstW % 2 != 0 || dstH % 2 != 0 then none
  else
    let mbsW := (dstW + 15) / 16
    let mbsH := (dstH + 15) / 16
    let padW := mbsW * 16 - dstW
    let padH := mbsH * 16 - dstH
    let lvl := lavfiChooseH264Level mbsW mbsH
    let spsSyn : H264SpsFull := {
      nalRefIdc := 3, profileIdc := 66, constraintSet0Flag := true, constraintSet1Flag := true,
      levelIdc := lvl, spsId := 0, chromaFormatIdc := 1, log2MaxFrameNumMinus4 := 0,
      picOrderCntType := 0, log2MaxPicOrderCntLsbMinus4 := 4, maxNumRefFrames := 1,
      picWidthInMbsMinus1 := (mbsW - 1).toUInt16, picHeightInMapUnitsMinus1 := (mbsH - 1).toUInt16,
      frameMbsOnlyFlag := true, direct8x8InferenceFlag := true,
      frameCroppingFlag := padW > 0 || padH > 0,
      frameCropRightOffset := (padW / 2).toUInt16, frameCropBottomOffset := (padH / 2).toUInt16,
      widthPx := dstW.toUInt32, heightPx := dstH.toUInt32
    }
    let ppsSyn : H264PpsFull := {
      nalRefIdc := 3, ppsId := 0, spsId := 0, entropyCodingModeFlag := false,
      deblockingFilterControlPresentFlag := true
    }
    let spsNal ← serializeH264SpsFull spsSyn
    let ppsNal ← serializeH264PpsFull ppsSyn 1 0
    let spsEnt ← parseSpsFull spsNal
    let spsArr := (Array.replicate 32 none).set! 0 (some spsEnt)
    let ppsEnt ← parsePpsFull ppsNal spsArr
    let avccRec : AvcDecoderConfigRecord := {
      configurationVersion := 1, avcProfileIndication := 66,
      profileCompatibility := spsSyn.constraintByte, avcLevelIndication := lvl,
      lengthSizeMinusOne := 3, spsNalus := #[spsNal], ppsNalus := #[ppsNal], hasHighExt := false
    }
    let avccBody ← serializeAvcDecoderConfigRecord avccRec
    let mut samples : Array SynthMp4Sample := Array.mkEmpty frames.size
    for idx in [:frames.size] do
      let vf := frames[idx]!
      if vf.planes.size < 3 then none
      let mut mbs : Array MbSyntax := Array.mkEmpty (mbsW * mbsH)
      for mbY in [:mbsH] do
        for mbX in [:mbsW] do
          let pcm := packYuv420pMbPcmBytes vf mbX mbY
          mbs := mbs.push { isSkip := false, kind := .iPcm, intraIdx := 25, pcmBytes := pcm }
      let wPre :=
        let w0 := writeUNat BitWriter.empty 0 4
        let w1 := writeUENat w0 (idx % 2)
        let w2 := writeUNat w1 0 8
        let w3 := writeU1Nat w2 0
        writeU1Nat w3 0
      let wSuf :=
        let w0 := writeUENat BitWriter.empty 0
        let w1 := writeSEInt w0 0
        writeSEInt w1 0
      let shEnt : SliceHeaderFull := {
        nalHdr := 0x65, firstMbInSlice := 0, sliceType := 7, sliceTypeNos := 2, ppsId := 0,
        prefixBits := lavfiBitWriterBits wPre, cabacInitIdc := 0, sliceQpDelta := 0,
        suffixBits := lavfiBitWriterBits wSuf, numRefL0 := 1, numRefL1 := 1, sliceQpY := 26
      }
      let sliceNal ← encodeSliceCavlc shEnt mbs spsEnt ppsEnt
      let pkt ← packAvccPacket #[sliceNal] 4
      samples := samples.push { data := pkt, dur := 1, cttsOff := 0, isSync := true }
    some {
      kind := .video
      timescale := Nat.max 1 fpsNum
      width := dstW
      height := dstH
      stsdBox := buildAvc1StsdBox dstW dstH avccBody
      samples := samples
    }

private def aacSampleRateIdx? (sr : Nat) : Option UInt8 :=
  match sr with
  | 96000 => some 0 | 88200 => some 1 | 64000 => some 2 | 48000 => some 3
  | 44100 => some 4 | 32000 => some 5 | 24000 => some 6 | 22050 => some 7
  | 16000 => some 8 | 12000 => some 9 | 11025 => some 10 | 8000 => some 11
  | 7350  => some 12 | _ => none

/-- Build a `SynthMp4Track` containing AAC-LC frames for `af` (1 or 2 channels). -/
def muxLavfiAudioAacTrack (af : AudioFrame) : Option SynthMp4Track := do
  let afNorm :=
    if af.channels.toNat > 2 then execAudioPanFormat af af.sampleRate.toNat 2 else af
  let sr := if (aacSampleRateIdx? afNorm.sampleRate.toNat).isSome then afNorm.sampleRate else 48000
  let afReady := if sr == afNorm.sampleRate then afNorm else resampleAudioFrame afNorm sr
  let srIdx ← aacSampleRateIdx? sr.toNat
  let chans := audioFrameToChannelArrays afReady
  if chans.isEmpty || chans.size > 2 then none
  else
    let adts ← aacEncodeAdtsStream chans sr 16 128000 true
    let (_, rawSlices) ← demuxAdtsStream (ByteSlice.ofByteArray adts) false
    if rawSlices.isEmpty then none
    else
      let outSamples := rawSlices.map fun sl =>
        ({ data := sl.toByteArray, dur := 1024, cttsOff := 0, isSync := true } : SynthMp4Sample)
      let asc : AacLcAsc := {
        audioObjectType := 2, samplingFrequencyIndex := srIdx,
        channelConfiguration := chans.size.toUInt8,
        frameLengthFlag := false, dependsOnCoreCoder := false, extensionFlag := false
      }
      let entry ← buildMp4aSampleEntryBox asc
      some {
        kind := .audio, timescale := sr.toNat, width := 0, height := 0,
        stsdBox := buildMp4aStsdBoxFromEntry entry, samples := outSamples
      }

/-- Mux video and/or audio lavfi outputs into an ISO-BMFF `.mp4` ByteArray. -/
def muxLavfiMp4Bytes (vFrames? : Option (Array VideoFrame × Nat)) (aFrame? : Option AudioFrame) :
    Option ByteArray := do
  let mut tracks : Array SynthMp4Track := #[]
  if let some (vfs, fps) := vFrames? then
    let vt ← muxLavfiVideoH264Track vfs fps
    tracks := tracks.push vt
  if let some af := aFrame? then
    let atrk ← muxLavfiAudioAacTrack af
    tracks := tracks.push atrk
  if tracks.isEmpty then none
  else muxSynthMp4Container tracks

/-- Mux lavfi `yuv420p` video frames into a lossless FFV1 v3 `.mkv` or `.avi` ByteArray. -/
def muxLavfiFfv1Bytes (outFmt : String) (vfs : Array VideoFrame) (fps : Nat) : Option ByteArray :=
  if vfs.isEmpty then none
  else
    let vf0 := vfs[0]!
    let rawFrames := vfs.map (fun vf => packVideoFramesYuv420pRaw #[vf])
    match LeanAV.Ffv1.makeEncoderConfiguration .yuv420p 1 4 1 1 with
    | .error _ => none
    | .ok encCfg =>
      let cfgRec := LeanAV.Ffv1.encodeConfiguration encCfg
      Id.run do
        let mut gop : LeanAV.Ffv1.GopState := #[]
        let mut pkts : Array ByteArray := #[]
        let mut kfs : Array Bool := #[]
        for raw in rawFrames do
          match LeanAV.Ffv1.encodeFrameV3 encCfg vf0.width vf0.height .yuv420p raw 0 true gop with
          | .error _ => return none
          | .ok (pkt, nextGop) =>
            pkts := pkts.push pkt
            kfs := kfs.push true
            gop := nextGop
        let st : LeanAV.Ffv1Container.Stream := {
          width := vf0.width, height := vf0.height,
          timeNum := 1, timeDen := Nat.max 1 fps,
          sarNum := 0, sarDen := 1,
          config := cfgRec, packets := pkts, keyframes := kfs
        }
        match LeanAV.Ffv1Container.mux outFmt st with
        | .ok b => return some b
        | .error _ => return none

/-- Format `md5` muxer output over raw video or audio lavfi bytes. -/
def muxLavfiMd5Bytes (rawPayload : ByteArray) : ByteArray :=
  (LeanAV.Md5.formatMd5Muxer rawPayload).toUTF8

/-- Format `framemd5` muxer output over `yuv420p` lavfi video frames. -/
def muxLavfiFrameMd5Bytes (vfs : Array VideoFrame) (fps : Nat) : Option ByteArray :=
  if vfs.isEmpty then none
  else
    let vf0 := vfs[0]!
    let rawFrames := vfs.map (fun vf => packVideoFramesYuv420pRaw #[vf])
    some (LeanAV.Md5.formatFrameMd5Muxer vf0.width vf0.height 1 (Nat.max 1 fps) 0 1 rawFrames).toUTF8

/-- Run a single-stream `-vf` chain through `parseFilterGraph` -> `typecheckFilterGraph` ->
`executeTypedFilterGraph`, bridging decoded `VideoFrame` streams directly into `LavfiGraph`. -/
def runSingleStreamVideoFilterGraph (vfChain : String) (frames : Array VideoFrame) (fps : Nat := 25) :
    Except String (Array VideoFrame × Nat) := do
  let effFps := Nat.max 1 fps
  if vfChain.trimAscii.toString == "" then
    return (frames, effFps)
  if frames.isEmpty then
    return (frames, effFps)
  let vf0 := frames[0]!
  let spec := "[0:v]" ++ vfChain ++ "[vout]"
  let g ← parseFilterGraph spec
  let extFmt : PadFormat := { kind := .video, width := vf0.width, height := vf0.height, fpsNum := effFps }
  let tg ← typecheckFilterGraph g [("0:v", extFmt)]
  let inQ := buildVideoQueue (Nat.max maxLavfiVideoFrames frames.size) frames
  let outs ← executeTypedFilterGraph tg [("0:v", inQ)]
  match outs.find? (fun (lbl, fmt, _) => lbl == "vout" && fmt.kind == .video) with
  | some (_, fmt, outQ) => return (drainVideoQueue outQ, Nat.max 1 fmt.fpsNum)
  | none =>
    match outs.find? (fun (_, fmt, _) => fmt.kind == .video) with
    | some (_, fmt, outQ) => return (drainVideoQueue outQ, Nat.max 1 fmt.fpsNum)
    | none => throw "video filter graph produced no video output pad"

/-- Run a single-stream `-af` chain through `parseFilterGraph` -> `typecheckFilterGraph` ->
`executeTypedFilterGraph`, bridging decoded `AudioFrame` streams directly into `LavfiGraph`. -/
def runSingleStreamAudioFilterGraph (afChain : String) (af : AudioFrame) :
    Except String AudioFrame := do
  if afChain.trimAscii.toString == "" then
    return af
  let spec := "[0:a]" ++ afChain ++ "[aout]"
  let g ← parseFilterGraph spec
  let extFmt : PadFormat := { kind := .audio, sampleRate := Nat.max 1 af.sampleRate.toNat, channels := Nat.max 1 af.channels.toNat }
  let tg ← typecheckFilterGraph g [("0:a", extFmt)]
  let inQ := buildAudioQueue 4 af
  let outs ← executeTypedFilterGraph tg [("0:a", inQ)]
  match outs.find? (fun (lbl, fmt, _) => lbl == "aout" && fmt.kind == .audio) with
  | some (_, _, outQ) => return drainAudioQueue outQ
  | none =>
    match outs.find? (fun (_, fmt, _) => fmt.kind == .audio) with
    | some (_, _, outQ) => return drainAudioQueue outQ
    | none => throw "audio filter graph produced no audio output pad"

/-- Run an arbitrary multi-stream `-filter_complex` DAG over external video and audio input streams. -/
def runMultiStreamFilterGraph (graphSpec : String)
    (videoInputs : List (String × Array VideoFrame × Nat))
    (audioInputs : List (String × AudioFrame)) :
    Except String (List (String × PadFormat × EdgeBufferQueue)) := do
  let g ← parseFilterGraph graphSpec
  let mut extFmts : List (String × PadFormat) := []
  let mut extQs : List (String × EdgeBufferQueue) := []
  for (lbl, vfs, fps) in videoInputs do
    let w := if vfs.isEmpty then 16 else vfs[0]!.width
    let h := if vfs.isEmpty then 16 else vfs[0]!.height
    extFmts := extFmts ++ [(lbl, { kind := .video, width := w, height := h, fpsNum := Nat.max 1 fps })]
    extQs := extQs ++ [(lbl, buildVideoQueue (Nat.max maxLavfiVideoFrames vfs.size) vfs)]
  for (lbl, af) in audioInputs do
    extFmts := extFmts ++ [(lbl, { kind := .audio, sampleRate := Nat.max 1 af.sampleRate.toNat, channels := Nat.max 1 af.channels.toNat })]
    extQs := extQs ++ [(lbl, buildAudioQueue 4 af)]
  let tg ← typecheckFilterGraph g extFmts
  executeTypedFilterGraph tg extQs

/-- Admitted lavfi HDR filter names and modes (`colorspace` and `tonemap`). -/
def LavfiHdrFilterAdmitted (a : String × String) : Prop :=
  let (nm, arg) := a
  (nm = "colorspace" ∧ (arg = "bt709" ∨ arg = "bt601" ∨ arg = "bt2020")) ∨
  (nm = "tonemap" ∧ (arg = "reinhard" ∨ arg = "hable" ∨ arg = "mobius" ∨ arg = "clip" ∨ arg = "linear"))

instance (a : String × String) : Decidable (LavfiHdrFilterAdmitted a) := by
  unfold LavfiHdrFilterAdmitted
  infer_instance

def lavfiHdrFilterGateSpec : AVGateSpec (String × String) LavfiHdrFilterAdmitted where
  gate := fun a => decide (LavfiHdrFilterAdmitted a)
  sound := fun _ h => of_decide_eq_true h
  complete := fun _ h => decide_eq_true h
  posWitness := ("tonemap", "hable")
  negWitness := ("tonemap", "bogus")
  nonVacuous := by decide
  tight := by decide

theorem lavfiHdrFilterGateSpec_iff (a : String × String) :
    lavfiHdrFilterGateSpec.gate a = true ↔ LavfiHdrFilterAdmitted a :=
  lavfiHdrFilterGateSpec.iff_safe a

end LeanAV.LavfiGraph




