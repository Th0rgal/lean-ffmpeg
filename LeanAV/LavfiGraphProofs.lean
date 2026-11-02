/-
  LeanAV.LavfiGraphProofs: Machine-Checked Soundness, Completeness, Non-Vacuity,
  Kahn Topological Acyclicity, Pad MediaKind / Dimension / Rate Conservation,
  and Bounded EdgeBufferQueue Proofs for `LeanAV.LavfiGraph`.
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
import LeanAV.LavfiGraph

namespace LeanAV.LavfiGraphProofs

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
open LeanAV.LavfiGraph

/-! ## 1. Kahn Topological Ordering: Soundness & Completeness -/

/-- Membership characterization for `inNeighbors edges i`. -/
theorem mem_inNeighbors_iff (edges : List GraphEdge) (i p : Nat) :
    p ∈ inNeighbors edges i ↔ ∃ e ∈ edges, e.dst = i ∧ e.src = p := by
  unfold inNeighbors
  simp only [List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨e, ⟨heMem, heDst⟩, heSrc⟩
    exact ⟨e, heMem, heDst, heSrc⟩
  · rintro ⟨e, heMem, heDst, heSrc⟩
    exact ⟨e, ⟨heMem, heDst⟩, heSrc⟩

/-- Removing an element present in a `Nodup` list decreases its length by exactly `1`. -/
theorem filter_bne_length_of_nodup :
    ∀ {xs : List Nat} {i : Nat},
      xs.Nodup → i ∈ xs → (xs.filter (fun j => j != i)).length + 1 = xs.length
  | [], _, _, hMem => by simp at hMem
  | x :: rest, i, hNodup, hMem => by
    rw [List.nodup_cons] at hNodup
    rcases hNodup with ⟨hxNotMem, hRestNodup⟩
    rw [List.mem_cons] at hMem
    rcases hMem with hEqX | hInRest
    · subst hEqX
      have hAllNe : ∀ y ∈ rest, (y != i) = true := by
        intro y hy
        rw [bne_iff_ne]
        intro hEq
        subst hEq
        exact hxNotMem hy
      have hFilt : rest.filter (fun j => j != i) = rest :=
        List.filter_eq_self.mpr hAllNe
      simp [List.filter, hFilt]
    · have hxNe : (x != i) = true := by
        rw [bne_iff_ne]
        intro hEq
        subst hEq
        exact hxNotMem hInRest
      have ih := filter_bne_length_of_nodup hRestNodup hInRest
      simp [List.filter, hxNe]
      omega

/-- Properties of a successful `kahnStepPure` transition. -/
theorem kahnStepPure_spec {remaining rest : List Nat} {edges : List GraphEdge} {i : Nat}
    (hStep : kahnStepPure remaining edges = some (i, rest)) :
    i ∈ remaining ∧
    rest = remaining.filter (fun j => j != i) ∧
    (∀ e ∈ edges, e.dst = i → e.src ∉ remaining) := by
  unfold kahnStepPure at hStep
  split at hStep
  · simp at hStep
  · rename_i iFound hFind
    injection hStep with hPair
    injection hPair with hiEq hRestEq
    subst hiEq
    have hIn : iFound ∈ remaining := List.mem_of_find?_eq_some hFind
    have hPred := @List.find?_some Nat (fun k => !(inNeighbors edges k).any (fun p => remaining.contains p)) iFound remaining hFind
    refine ⟨hIn, hRestEq.symm, ?_⟩
    intro e heMem heDst hSrcRem
    have hMemIn : e.src ∈ inNeighbors edges iFound :=
      (mem_inNeighbors_iff edges iFound e.src).mpr ⟨e, heMem, heDst, rfl⟩
    have hAny : (inNeighbors edges iFound).any (fun p => remaining.contains p) = true := by
      rw [List.any_eq_true]
      exact ⟨e.src, hMemIn, List.contains_iff_mem.mpr hSrcRem⟩
    rw [hAny] at hPred
    simp at hPred

/-- Loop invariant for `kahnLoop` soundness. -/
def KahnInv (n : Nat) (edges : List GraphEdge) (remaining order : List Nat) : Prop :=
  (order ++ remaining).Nodup ∧
  order.length + remaining.length = n ∧
  (∀ u, u < n ↔ u ∈ order ∨ u ∈ remaining) ∧
  (∀ e ∈ edges, e.src < n → e.dst < n → e.dst ∈ order → e.src ∈ order) ∧
  (∀ e ∈ edges, e.src ∈ order → e.dst ∈ order → order.idxOf e.src < order.idxOf e.dst)

/-- Inductive soundness of `kahnLoop`: any `some order'` returned from a state satisfying
    `KahnInv` is a `ValidTopoOrder`. -/
theorem kahnLoop_sound (n : Nat) (edges : List GraphEdge) :
    ∀ (fuel : Nat) (remaining order order' : List Nat),
      KahnInv n edges remaining order →
      kahnLoop fuel remaining edges order = some order' →
      ValidTopoOrder n edges order'
  | 0, remaining, order, order', hInv, hRun => by
    unfold kahnLoop at hRun
    by_cases hEmp : remaining.isEmpty = true
    · simp only [hEmp, ↓reduceIte, Option.some.injEq] at hRun
      subst hRun
      have hRemNil : remaining = [] := List.isEmpty_iff.mp hEmp
      subst hRemNil
      rcases hInv with ⟨hNodup, hLen, hCov, _, hIdx⟩
      simp only [List.append_nil, List.length_nil, Nat.add_zero, List.not_mem_nil, or_false] at hNodup hLen hCov
      refine ⟨hLen, hNodup, fun u hu => (hCov u).mpr hu, ?_⟩
      intro e he hSrc hDst
      exact hIdx e he ((hCov e.src).mp hSrc) ((hCov e.dst).mp hDst)
    · simp [hEmp] at hRun
  | fuel + 1, remaining, order, order', hInv, hRun => by
    unfold kahnLoop at hRun
    match hStep : kahnStepPure remaining edges with
    | none =>
      simp only [hStep] at hRun
      by_cases hEmp : remaining.isEmpty = true
      · simp only [hEmp, ↓reduceIte, Option.some.injEq] at hRun
        subst hRun
        have hRemNil : remaining = [] := List.isEmpty_iff.mp hEmp
        subst hRemNil
        rcases hInv with ⟨hNodup, hLen, hCov, _, hIdx⟩
        simp only [List.append_nil, List.length_nil, Nat.add_zero, List.not_mem_nil, or_false] at hNodup hLen hCov
        refine ⟨hLen, hNodup, fun u hu => (hCov u).mpr hu, ?_⟩
        intro e he hSrc hDst
        exact hIdx e he ((hCov e.src).mp hSrc) ((hCov e.dst).mp hDst)
      · simp [hEmp] at hRun
    | some (i, rest) =>
      simp only [hStep] at hRun
      rcases kahnStepPure_spec hStep with ⟨hiRem, hRestDef, hNoIn⟩
      rcases hInv with ⟨hNodup, hLen, hCov, hClosed, hIdx⟩
      rw [List.nodup_append] at hNodup
      rcases hNodup with ⟨hOrdNodup, hRemNodup, hDisj⟩
      have hiNotOrd : i ∉ order := fun hInO => hDisj i hInO i hiRem rfl
      have hRestLen : rest.length + 1 = remaining.length := by
        rw [hRestDef]
        exact filter_bne_length_of_nodup hRemNodup hiRem
      have hRestMem : ∀ u, u ∈ rest ↔ u ∈ remaining ∧ u ≠ i := by
        intro u
        rw [hRestDef, List.mem_filter, bne_iff_ne]
      have hRestNodup : rest.Nodup := by
        rw [hRestDef]
        exact List.Pairwise.filter _ hRemNodup
      have hOrd1Nodup : (order ++ [i]).Nodup := by
        rw [List.nodup_append]
        refine ⟨hOrdNodup, by simp, ?_⟩
        intro a ha b hb
        rw [List.mem_singleton] at hb
        subst hb
        intro hEq
        subst hEq
        exact hiNotOrd ha
      have hNextNodup : ((order ++ [i]) ++ rest).Nodup := by
        rw [List.nodup_append]
        refine ⟨hOrd1Nodup, hRestNodup, ?_⟩
        intro a ha b hb hEq
        subst hEq
        rcases (hRestMem a).mp hb with ⟨haRem, haNeI⟩
        rw [List.mem_append, List.mem_singleton] at ha
        rcases ha with haOrd | rfl
        · exact hDisj a haOrd a haRem rfl
        · exact haNeI rfl
      have hNextCov : ∀ u, u < n ↔ u ∈ order ++ [i] ∨ u ∈ rest := by
        intro u
        rw [hCov u, List.mem_append, List.mem_singleton, hRestMem]
        constructor
        · rintro (huO | huR)
          · exact Or.inl (Or.inl huO)
          · by_cases hui : u = i
            · exact Or.inl (Or.inr hui)
            · exact Or.inr ⟨huR, hui⟩
        · rintro ((huO | rfl) | ⟨huR, _⟩)
          · exact Or.inl huO
          · exact Or.inr hiRem
          · exact Or.inr huR
      have hNextClosed : ∀ e ∈ edges, e.src < n → e.dst < n → e.dst ∈ order ++ [i] → e.src ∈ order ++ [i] := by
        intro e he hSrc hDst hDstIn
        rw [List.mem_append, List.mem_singleton] at hDstIn ⊢
        rcases hDstIn with hDstOrd | hDstEqI
        · exact Or.inl (hClosed e he hSrc hDst hDstOrd)
        · have hNotRem : e.src ∉ remaining := hNoIn e he hDstEqI
          rcases (hCov e.src).mp hSrc with hSrcOrd | hSrcRem
          · exact Or.inl hSrcOrd
          · exact False.elim (hNotRem hSrcRem)
      have hNextIdx : ∀ e ∈ edges, e.src ∈ order ++ [i] → e.dst ∈ order ++ [i] →
          (order ++ [i]).idxOf e.src < (order ++ [i]).idxOf e.dst := by
        intro e he hSrcIn hDstIn
        have hSrcLtN : e.src < n := (hNextCov e.src).mpr (Or.inl hSrcIn)
        have hDstLtN : e.dst < n := (hNextCov e.dst).mpr (Or.inl hDstIn)
        rw [List.mem_append, List.mem_singleton] at hSrcIn hDstIn
        rcases hDstIn with hDstOrd | hDstEqI
        · have hSrcOrd : e.src ∈ order := hClosed e he hSrcLtN hDstLtN hDstOrd
          rw [List.idxOf_append, List.idxOf_append]
          simp [hSrcOrd, hDstOrd, hIdx e he hSrcOrd hDstOrd]
        · have hSrcNotRem : e.src ∉ remaining := hNoIn e he hDstEqI
          have hSrcOrd : e.src ∈ order := by
            rcases hSrcIn with hSO | hSI
            · exact hSO
            · rw [hSI] at hSrcNotRem
              exact False.elim (hSrcNotRem hiRem)
          have hSrcIdxLt : order.idxOf e.src < order.length :=
            List.idxOf_lt_length_iff.mpr hSrcOrd
          rw [List.idxOf_append, List.idxOf_append]
          simp [hSrcOrd, hDstEqI, hiNotOrd]
          omega
      have hNextInv : KahnInv n edges rest (order ++ [i]) := by
        refine ⟨hNextNodup, ?_, hNextCov, hNextClosed, hNextIdx⟩
        simp only [List.length_append, List.length_singleton]
        omega
      exact kahnLoop_sound n edges fuel rest (order ++ [i]) order' hNextInv hRun

/-- **Kahn Soundness**: whenever `kahnOrder n edges = some order`, `order` is a valid
    topological permutation of `0 .. n-1`. -/
theorem kahnOrder_sound (n : Nat) (edges : List GraphEdge) (order : List Nat)
    (h : kahnOrder n edges = some order) :
    ValidTopoOrder n edges order := by
  unfold kahnOrder at h
  have hInit : KahnInv n edges (List.range n) [] := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa using List.nodup_range
    · simp [List.length_range]
    · intro u
      simp [List.mem_range]
    · intro _ _ _ _ hInNil
      simp at hInNil
    · intro _ _ hInNil _
      simp at hInNil
  exact kahnLoop_sound n edges n (List.range n) [] order hInit h

/-- Any non-empty list `xs` admits an element minimizing `f : Nat → Nat`. -/
theorem exists_min_on_nonempty (f : Nat → Nat) :
    ∀ {xs : List Nat}, xs ≠ [] → ∃ m ∈ xs, ∀ y ∈ xs, f m ≤ f y
  | [], hNe => False.elim (hNe rfl)
  | [x], _ => ⟨x, List.mem_singleton.mpr rfl, fun y hy => by rw [List.mem_singleton.mp hy]; exact Nat.le_refl _⟩
  | x :: y :: rest, _ => by
    rcases exists_min_on_nonempty f (xs := y :: rest) (by simp) with ⟨m, hmMem, hmMin⟩
    by_cases hxm : f x ≤ f m
    · refine ⟨x, List.mem_cons_self, ?_⟩
      intro z hz
      rw [List.mem_cons] at hz
      rcases hz with rfl | hzRest
      · exact Nat.le_refl _
      · exact Nat.le_trans hxm (hmMin z hzRest)
    · refine ⟨m, List.mem_cons_of_mem x hmMem, ?_⟩
      intro z hz
      rw [List.mem_cons] at hz
      rcases hz with rfl | hzRest
      · omega
      · exact hmMin z hzRest

/-- Under a valid topological order `topo`, every non-empty `Nodup` subset of `0 .. n-1`
    has a source picked by `kahnStepPure`. -/
theorem kahnStepPure_some_of_topo {n : Nat} {edges : List GraphEdge} {topo remaining : List Nat}
    (hTopo : ValidTopoOrder n edges topo)
    (hNe : remaining ≠ [])
    (hSub : ∀ u ∈ remaining, u < n) :
    ∃ i rest, kahnStepPure remaining edges = some (i, rest) := by
  rcases hTopo with ⟨_, _, _, hFwd⟩
  rcases exists_min_on_nonempty (fun u => topo.idxOf u) hNe with ⟨m, hmIn, hmMin⟩
  have hmSource : (!(inNeighbors edges m).any (fun p => remaining.contains p)) = true := by
    by_cases hAny : (inNeighbors edges m).any (fun p => remaining.contains p) = true
    · rw [List.any_eq_true] at hAny
      rcases hAny with ⟨p, hpIn, hpRemB⟩
      have hpRem : p ∈ remaining := List.contains_iff_mem.mp hpRemB
      rcases (mem_inNeighbors_iff edges m p).mp hpIn with ⟨e, heMem, heDst, heSrc⟩
      have hLt : topo.idxOf p < topo.idxOf m := by
        rw [← heSrc, ← heDst]
        exact hFwd e heMem (heSrc ▸ hSub p hpRem) (heDst ▸ hSub m hmIn)
      have hLe : topo.idxOf m ≤ topo.idxOf p := hmMin p hpRem
      omega
    · have hF : (inNeighbors edges m).any (fun p => remaining.contains p) = false :=
        Bool.eq_false_iff.mpr hAny
      rw [hF]
      rfl
  unfold kahnStepPure
  match hFind : remaining.find? (fun i => !(inNeighbors edges i).any (fun p => remaining.contains p)) with
  | some i => exact ⟨i, remaining.filter (fun j => j != i), rfl⟩
  | none =>
    have hNone := (List.find?_eq_none.mp hFind) m hmIn
    exact False.elim (hNone hmSource)

/-- Inductive completeness of `kahnLoop`: when `ValidTopoOrder n edges topo` holds,
    `kahnLoop` terminates with `some order'`. -/
theorem kahnLoop_complete (n : Nat) (edges : List GraphEdge) (topo : List Nat)
    (hTopo : ValidTopoOrder n edges topo) :
    ∀ (fuel : Nat) (remaining order : List Nat),
      remaining.length = fuel →
      remaining.Nodup →
      (∀ u ∈ remaining, u < n) →
      ∃ order', kahnLoop fuel remaining edges order = some order'
  | 0, remaining, order, hLen, _, _ => by
    have hNil : remaining = [] := List.eq_nil_of_length_eq_zero hLen
    subst hNil
    exact ⟨order, rfl⟩
  | fuel + 1, remaining, order, hLen, hNodup, hSub => by
    have hNe : remaining ≠ [] := by
      intro hNil
      rw [hNil] at hLen
      simp at hLen
    rcases kahnStepPure_some_of_topo hTopo hNe hSub with ⟨i, rest, hStep⟩
    rcases kahnStepPure_spec hStep with ⟨hiRem, hRestDef, _⟩
    have hRestLen : rest.length = fuel := by
      have hStepLen := filter_bne_length_of_nodup hNodup hiRem
      rw [← hRestDef] at hStepLen
      omega
    have hRestNodup : rest.Nodup := by
      rw [hRestDef]
      exact List.Pairwise.filter _ hNodup
    have hRestSub : ∀ u ∈ rest, u < n := by
      intro u hu
      rw [hRestDef, List.mem_filter] at hu
      exact hSub u hu.1
    unfold kahnLoop
    simp only [hStep]
    exact kahnLoop_complete n edges topo hTopo fuel rest (order ++ [i]) hRestLen hRestNodup hRestSub

/-- **Kahn Completeness**: whenever ANY valid topological permutation `topo` exists,
    `kahnOrder n edges` succeeds (`isSome = true`). -/
theorem kahnOrder_complete (n : Nat) (edges : List GraphEdge) (topo : List Nat)
    (hTopo : ValidTopoOrder n edges topo) :
    (kahnOrder n edges).isSome = true := by
  unfold kahnOrder
  have hSub : ∀ u ∈ List.range n, u < n := fun _ hu => List.mem_range.mp hu
  rcases kahnLoop_complete n edges topo hTopo n (List.range n) [] List.length_range List.nodup_range hSub with
    ⟨order', hEq⟩
  simp [hEq]

/-- Independent mathematical acyclicity predicate: `g` admits a valid topological permutation. -/
def GraphAcyclic (g : FilterGraph) : Prop :=
  ∃ order : List Nat, ValidTopoOrder g.nodes.size (graphEdges g) order

/-- Exact equivalence between Kahn's executable gate and existence of a valid topological order. -/
theorem graphIsAcyclic_iff_graphAcyclic (g : FilterGraph) :
    graphIsAcyclic g = true ↔ GraphAcyclic g := by
  unfold graphIsAcyclic GraphAcyclic
  constructor
  · intro hSome
    match hK : kahnOrder g.nodes.size (graphEdges g) with
    | some order => exact ⟨order, kahnOrder_sound g.nodes.size (graphEdges g) order hK⟩
    | none => simp [hK] at hSome
  · rintro ⟨topo, hTopo⟩
    exact kahnOrder_complete g.nodes.size (graphEdges g) topo hTopo

/-- Verified `AVGateSpec` for Kahn filtergraph acyclicity (`graphIsAcyclic` ↔ `GraphAcyclic`). -/
def graphAcyclicGateSpec : AVGateSpec FilterGraph GraphAcyclic where
  gate := graphIsAcyclic
  sound := fun g h => (graphIsAcyclic_iff_graphAcyclic g).mp h
  complete := fun g h => (graphIsAcyclic_iff_graphAcyclic g).mpr h
  posWitness := kahnPosGraph
  negWitness := kahnNegGraph
  nonVacuous := by native_decide
  tight := by native_decide

theorem graphAcyclicGateSpec_iff (g : FilterGraph) :
    graphAcyclicGateSpec.gate g = true ↔ GraphAcyclic g :=
  graphAcyclicGateSpec.iff_safe g

/-! ## 2. Pad Kind, Dimension, Rate, and Channel Conservation -/

/-- Two pads may be wired when kinds match and geometry or rate/channel are conserved. -/
def PadLinkCompatible (prod cons : PadFormat) : Prop :=
  prod.kind = cons.kind ∧
  (prod.kind = .video →
    0 < prod.width ∧ prod.width % 2 = 0 ∧ 0 < prod.height ∧ prod.height % 2 = 0 ∧
    prod.width = cons.width ∧ prod.height = cons.height) ∧
  (prod.kind = .audio →
    0 < prod.sampleRate ∧ prod.sampleRate = cons.sampleRate ∧
    0 < prod.channels ∧ prod.channels = cons.channels)

instance (prod cons : PadFormat) : Decidable (PadLinkCompatible prod cons) := by
  unfold PadLinkCompatible
  infer_instance

/-- Executable pad-link gate matching `PadLinkCompatible`. -/
def padLinkCompatibleGate (p : PadFormat × PadFormat) : Bool :=
  decide (PadLinkCompatible p.1 p.2)

def padLinkGateSpec : AVGateSpec (PadFormat × PadFormat) (fun p => PadLinkCompatible p.1 p.2) where
  gate := padLinkCompatibleGate
  sound := by
    intro p h
    simpa [padLinkCompatibleGate, PadLinkCompatible] using of_decide_eq_true h
  complete := by
    intro p h
    simpa [padLinkCompatibleGate, PadLinkCompatible] using decide_eq_true h
  posWitness :=
    ({ kind := .video, width := 320, height := 240 },
     { kind := .video, width := 320, height := 240 })
  negWitness :=
    ({ kind := .video, width := 320, height := 240 },
     { kind := .audio, sampleRate := 44100, channels := 1 })
  nonVacuous := by native_decide
  tight := by native_decide

theorem padLinkGateSpec_iff (p : PadFormat × PadFormat) :
    padLinkGateSpec.gate p = true ↔ PadLinkCompatible p.1 p.2 :=
  padLinkGateSpec.iff_safe p

theorem execVideoHflip_dims (vf : VideoFrame) :
    (execVideoHflip vf).width = vf.width ∧ (execVideoHflip vf).height = vf.height := by
  unfold execVideoHflip
  split <;> simp

theorem execVideoVflip_dims (vf : VideoFrame) :
    (execVideoVflip vf).width = vf.width ∧ (execVideoVflip vf).height = vf.height := by
  unfold execVideoVflip
  split <;> simp

theorem execVideoEq_dims (vf : VideoFrame) (cQ8 bVal : Int32) (inv : Bool) :
    (execVideoEq vf cQ8 bVal inv).width = vf.width ∧
    (execVideoEq vf cQ8 bVal inv).height = vf.height := by
  unfold execVideoEq
  split <;> simp

theorem execVideoOverlay_dims (bg fg : VideoFrame) (ox oy : Nat) :
    (execVideoOverlay bg fg ox oy).width = bg.width ∧
    (execVideoOverlay bg fg ox oy).height = bg.height := by
  unfold execVideoOverlay
  split <;> simp

theorem execVideoCrop_dims (vf : VideoFrame) (x0 y0 cw ch : Nat)
    (hPlanes : 3 ≤ vf.planes.size) :
    (execVideoCrop vf x0 y0 cw ch).width = cw ∧
    (execVideoCrop vf x0 y0 cw ch).height = ch := by
  unfold execVideoCrop
  split
  · rename_i hLt
    omega
  · simp

theorem execVideoPad_dims (vf : VideoFrame) (pw ph ox oy : Nat) (fr fg fb : UInt8)
    (hPlanes : 3 ≤ vf.planes.size) :
    (execVideoPad vf pw ph ox oy fr fg fb).width = pw ∧
    (execVideoPad vf pw ph ox oy fr fg fb).height = ph := by
  unfold execVideoPad
  split
  · rename_i hLt
    omega
  · simp

theorem genColorVideoFrame_dims (r g b : UInt8) (w h fps frameIdx : Nat) :
    let vf := genColorVideoFrame r g b w h fps frameIdx
    vf.width = w ∧ vf.height = h ∧ vf.pixFmt = .yuv420p := by
  unfold genColorVideoFrame
  simp

theorem setSample_preserves_meta (af : AudioFrame) (ch i : Nat) (v : Int32) :
    (af.setSample ch i v).sampleRate = af.sampleRate ∧
    (af.setSample ch i v).channels = af.channels ∧
    (af.setSample ch i v).numSamples = af.numSamples := by
  unfold AudioFrame.setSample
  dsimp only
  split <;> simp

theorem foldl_preserves_audio_meta {α : Type} (xs : List α) (f : AudioFrame → α → AudioFrame)
    (init : AudioFrame)
    (hStep : ∀ acc x, (f acc x).sampleRate = acc.sampleRate ∧
      (f acc x).channels = acc.channels ∧ (f acc x).numSamples = acc.numSamples) :
    (xs.foldl f init).sampleRate = init.sampleRate ∧
    (xs.foldl f init).channels = init.channels ∧
    (xs.foldl f init).numSamples = init.numSamples := by
  induction xs generalizing init with
  | nil => simp
  | cons x rest ih =>
    simp only [List.foldl_cons]
    rcases hStep init x with ⟨hSr, hCh, hN⟩
    rcases ih (f init x) with ⟨ihSr, ihCh, ihN⟩
    exact ⟨ihSr.trans hSr, ihCh.trans hCh, ihN.trans hN⟩

theorem genSineAudioFrame_rate_channels (freqHz sampleRate durationMs : Nat) :
    (genSineAudioFrame freqHz sampleRate durationMs).channels = 1 ∧
    (genSineAudioFrame freqHz sampleRate durationMs).numSamples =
      lavfiAudioSampleCount sampleRate durationMs := by
  unfold genSineAudioFrame
  simp

theorem genAnullsrcAudioFrame_rate_channels (sampleRate channels durationMs : Nat) :
    (genAnullsrcAudioFrame sampleRate channels durationMs).sampleRate = sampleRate.toUInt32 ∧
    (genAnullsrcAudioFrame sampleRate channels durationMs).channels = (Nat.max 1 channels).toUInt32 ∧
    (genAnullsrcAudioFrame sampleRate channels durationMs).numSamples =
      lavfiAudioSampleCount sampleRate durationMs := by
  unfold genAnullsrcAudioFrame AudioFrame.alloc
  simp

theorem audioFrame_alloc_meta (fmt : SampleFormat) (sr ch : UInt32) (n : Nat) (pts : UInt64) :
    (AudioFrame.alloc fmt sr ch n pts).sampleRate = sr ∧
    (AudioFrame.alloc fmt sr ch n pts).channels = ch ∧
    (AudioFrame.alloc fmt sr ch n pts).numSamples = n := by
  unfold AudioFrame.alloc
  simp

theorem execVideoVstack_width (frames : List VideoFrame) (f0 : VideoFrame)
    (hHead : frames.head? = some f0) :
    (execVideoVstack frames).width = f0.width := by
  unfold execVideoVstack
  simp [hHead]

theorem execVideoHstack_height (frames : List VideoFrame) (f0 : VideoFrame)
    (hHead : frames.head? = some f0) :
    (execVideoHstack frames).height = f0.height := by
  unfold execVideoHstack
  simp [hHead]

/-- `split`/`asplit` fanout conserves the typed input pad on every output. -/
def SplitOutputConservation (inFmt : PadFormat) (outs : List PadFormat) : Prop :=
  outs ≠ [] ∧ ∀ f ∈ outs, f = inFmt

instance (inFmt : PadFormat) (outs : List PadFormat) : Decidable (SplitOutputConservation inFmt outs) := by
  unfold SplitOutputConservation
  infer_instance

def splitOutputGate (p : PadFormat × List PadFormat) : Bool :=
  decide (SplitOutputConservation p.1 p.2)

def splitOutputGateSpec : AVGateSpec (PadFormat × List PadFormat)
    (fun p => SplitOutputConservation p.1 p.2) where
  gate := splitOutputGate
  sound := by
    intro p h
    simpa [splitOutputGate, SplitOutputConservation] using of_decide_eq_true h
  complete := by
    intro p h
    simpa [splitOutputGate, SplitOutputConservation] using decide_eq_true h
  posWitness := ({ kind := .video, width := 16, height := 16 },
    [{ kind := .video, width := 16, height := 16 }, { kind := .video, width := 16, height := 16 }])
  negWitness := ({ kind := .video, width := 16, height := 16 }, [])
  nonVacuous := by native_decide
  tight := by native_decide

theorem splitOutputGateSpec_iff (p : PadFormat × List PadFormat) :
    splitOutputGateSpec.gate p = true ↔ SplitOutputConservation p.1 p.2 :=
  splitOutputGateSpec.iff_safe p

/-- `amix` conserves sample rate and never shrinks channel count below the first input. -/
def AmixRateConservation (ins : List PadFormat) (outFmt : PadFormat) : Prop :=
  ∃ f0, ins.head? = some f0 ∧ outFmt.kind = .audio ∧ outFmt.sampleRate = f0.sampleRate ∧
    f0.channels ≤ outFmt.channels

instance (ins : List PadFormat) (outFmt : PadFormat) : Decidable (AmixRateConservation ins outFmt) :=
  match ins with
  | [] => isFalse (by rintro ⟨_, hH, _⟩; simp at hH)
  | f0 :: _ =>
    if hRest : outFmt.kind = .audio ∧ outFmt.sampleRate = f0.sampleRate ∧ f0.channels ≤ outFmt.channels then
      isTrue ⟨f0, rfl, hRest⟩
    else
      isFalse (by
        rintro ⟨f1, hH, hKind, hRate, hCh⟩
        simp at hH
        subst hH
        exact hRest ⟨hKind, hRate, hCh⟩)

def amixRateGate (p : List PadFormat × PadFormat) : Bool :=
  decide (AmixRateConservation p.1 p.2)

def amixRateGateSpec : AVGateSpec (List PadFormat × PadFormat)
    (fun p => AmixRateConservation p.1 p.2) where
  gate := amixRateGate
  sound := by
    intro p h
    simpa [amixRateGate, AmixRateConservation] using of_decide_eq_true h
  complete := by
    intro p h
    simpa [amixRateGate, AmixRateConservation] using decide_eq_true h
  posWitness := ([{ kind := .audio, sampleRate := 44100, channels := 1 },
      { kind := .audio, sampleRate := 44100, channels := 2 }],
    { kind := .audio, sampleRate := 44100, channels := 2 })
  negWitness := ([{ kind := .audio, sampleRate := 44100, channels := 2 }],
    { kind := .audio, sampleRate := 48000, channels := 2 })
  nonVacuous := by native_decide
  tight := by native_decide

theorem amixRateGateSpec_iff (p : List PadFormat × PadFormat) :
    amixRateGateSpec.gate p = true ↔ AmixRateConservation p.1 p.2 :=
  amixRateGateSpec.iff_safe p

/-- Overlay keeps the background canvas. -/
def OverlayDimConservation (bg fg outFmt : PadFormat) : Prop :=
  bg.kind = .video ∧ fg.kind = .video ∧ outFmt.kind = .video ∧
  outFmt.width = bg.width ∧ outFmt.height = bg.height

instance (bg fg outFmt : PadFormat) : Decidable (OverlayDimConservation bg fg outFmt) := by
  unfold OverlayDimConservation
  infer_instance

def overlayDimGate (p : PadFormat × PadFormat × PadFormat) : Bool :=
  decide (OverlayDimConservation p.1 p.2.1 p.2.2)

def overlayDimGateSpec : AVGateSpec (PadFormat × PadFormat × PadFormat)
    (fun p => OverlayDimConservation p.1 p.2.1 p.2.2) where
  gate := overlayDimGate
  sound := by
    intro p h
    simpa [overlayDimGate, OverlayDimConservation] using of_decide_eq_true h
  complete := by
    intro p h
    simpa [overlayDimGate, OverlayDimConservation] using decide_eq_true h
  posWitness :=
    ({ kind := .video, width := 320, height := 240 },
     { kind := .video, width := 64, height := 64 },
     { kind := .video, width := 320, height := 240 })
  negWitness :=
    ({ kind := .video, width := 320, height := 240 },
     { kind := .video, width := 64, height := 64 },
     { kind := .video, width := 64, height := 64 })
  nonVacuous := by native_decide
  tight := by native_decide

theorem overlayDimGateSpec_iff (p : PadFormat × PadFormat × PadFormat) :
    overlayDimGateSpec.gate p = true ↔ OverlayDimConservation p.1 p.2.1 p.2.2 :=
  overlayDimGateSpec.iff_safe p

/-- A crop rectangle stays inside an even yuv420p frame. -/
def CropBoundsSafe (srcW srcH x0 y0 cw ch : Nat) : Prop :=
  0 < cw ∧ 0 < ch ∧ cw % 2 = 0 ∧ ch % 2 = 0 ∧ x0 + cw ≤ srcW ∧ y0 + ch ≤ srcH

instance (srcW srcH x0 y0 cw ch : Nat) : Decidable (CropBoundsSafe srcW srcH x0 y0 cw ch) := by
  unfold CropBoundsSafe
  infer_instance

def cropBoundsGate (p : Nat × Nat × Nat × Nat × Nat × Nat) : Bool :=
  decide (CropBoundsSafe p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)

def cropBoundsGateSpec : AVGateSpec (Nat × Nat × Nat × Nat × Nat × Nat)
    (fun p => CropBoundsSafe p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) where
  gate := cropBoundsGate
  sound := by intro p h; simpa [cropBoundsGate] using of_decide_eq_true h
  complete := by intro p h; simpa [cropBoundsGate] using decide_eq_true h
  posWitness := (320, 240, 16, 16, 64, 48)
  negWitness := (32, 32, 0, 0, 64, 48)
  nonVacuous := by native_decide
  tight := by native_decide

theorem cropBoundsGateSpec_iff (p : Nat × Nat × Nat × Nat × Nat × Nat) :
    cropBoundsGateSpec.gate p = true ↔
      CropBoundsSafe p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 :=
  cropBoundsGateSpec.iff_safe p

/-- A pad canvas covers the source and stays even. -/
def PadBoundsSafe (srcW srcH pw ph ox oy : Nat) : Prop :=
  pw % 2 = 0 ∧ ph % 2 = 0 ∧ ox + srcW ≤ pw ∧ oy + srcH ≤ ph

instance (srcW srcH pw ph ox oy : Nat) : Decidable (PadBoundsSafe srcW srcH pw ph ox oy) := by
  unfold PadBoundsSafe
  infer_instance

def padBoundsGate (p : Nat × Nat × Nat × Nat × Nat × Nat) : Bool :=
  decide (PadBoundsSafe p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)

def padBoundsGateSpec : AVGateSpec (Nat × Nat × Nat × Nat × Nat × Nat)
    (fun p => PadBoundsSafe p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) where
  gate := padBoundsGate
  sound := by intro p h; simpa [padBoundsGate] using of_decide_eq_true h
  complete := by intro p h; simpa [padBoundsGate] using decide_eq_true h
  posWitness := (320, 240, 640, 480, 0, 0)
  negWitness := (320, 240, 160, 120, 0, 0)
  nonVacuous := by native_decide
  tight := by native_decide

theorem padBoundsGateSpec_iff (p : Nat × Nat × Nat × Nat × Nat × Nat) :
    padBoundsGateSpec.gate p = true ↔
      PadBoundsSafe p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 :=
  padBoundsGateSpec.iff_safe p

/-- `amerge` channel totals stay within the 8-channel static limit. -/
def AmergeChannelSafe (ins : List PadFormat) (outCh : Nat) : Prop :=
  outCh = ins.foldl (fun acc f => acc + f.channels) 0 ∧ outCh ≤ 8 ∧ ins ≠ []

instance (ins : List PadFormat) (outCh : Nat) : Decidable (AmergeChannelSafe ins outCh) := by
  unfold AmergeChannelSafe
  infer_instance

def amergeChannelGate (p : List PadFormat × Nat) : Bool :=
  decide (AmergeChannelSafe p.1 p.2)

def amergeChannelGateSpec : AVGateSpec (List PadFormat × Nat)
    (fun p => AmergeChannelSafe p.1 p.2) where
  gate := amergeChannelGate
  sound := by
    intro p h
    simpa [amergeChannelGate, AmergeChannelSafe] using of_decide_eq_true h
  complete := by
    intro p h
    simpa [amergeChannelGate, AmergeChannelSafe] using decide_eq_true h
  posWitness := ([{ kind := .audio, sampleRate := 48000, channels := 1 },
      { kind := .audio, sampleRate := 48000, channels := 1 }], 2)
  negWitness := ([{ kind := .audio, sampleRate := 48000, channels := 6 },
      { kind := .audio, sampleRate := 48000, channels := 6 }], 12)
  nonVacuous := by native_decide
  tight := by native_decide

theorem amergeChannelGateSpec_iff (p : List PadFormat × Nat) :
    amergeChannelGateSpec.gate p = true ↔ AmergeChannelSafe p.1 p.2 :=
  amergeChannelGateSpec.iff_safe p

/-- Positive rates and durations materialize non-zero frame/sample counts inside the static caps. -/
def LavfiDurationBoundSafe (fps sr durationMs : Nat) : Prop :=
  0 < fps ∧ 0 < sr ∧ 0 < durationMs ∧
  lavfiVideoFrameCount fps durationMs ≤ maxLavfiVideoFrames ∧
  lavfiAudioSampleCount sr durationMs ≤ maxLavfiAudioSamples

instance (fps sr durationMs : Nat) : Decidable (LavfiDurationBoundSafe fps sr durationMs) := by
  unfold LavfiDurationBoundSafe
  infer_instance

def lavfiDurationBoundGate (p : Nat × Nat × Nat) : Bool :=
  decide (LavfiDurationBoundSafe p.1 p.2.1 p.2.2)

def lavfiDurationBoundGateSpec : AVGateSpec (Nat × Nat × Nat)
    (fun p => LavfiDurationBoundSafe p.1 p.2.1 p.2.2) where
  gate := lavfiDurationBoundGate
  sound := by intro p h; simpa [lavfiDurationBoundGate] using of_decide_eq_true h
  complete := by intro p h; simpa [lavfiDurationBoundGate] using decide_eq_true h
  posWitness := (25, 44100, 1000)
  negWitness := (0, 0, 0)
  nonVacuous := by native_decide
  tight := by native_decide

theorem lavfiDurationBoundGateSpec_iff (p : Nat × Nat × Nat) :
    lavfiDurationBoundGateSpec.gate p = true ↔ LavfiDurationBoundSafe p.1 p.2.1 p.2.2 :=
  lavfiDurationBoundGateSpec.iff_safe p

/-! ## 3. Bounded Edge Queues Built by the Executor -/

theorem list_foldl_push_bounded (frames : List VideoFrame) (q : EdgeBufferQueue)
    (h : EdgeBufferQueueBounded q) :
    EdgeBufferQueueBounded (frames.foldl (fun acc vf => EdgeBufferQueue.push acc (MediaFrame.video vf)) q) := by
  induction frames generalizing q with
  | nil => simpa using h
  | cons vf rest ih =>
    simp
    exact ih _ (edgeBufferQueue_push_preserves_bound q _ h)

theorem buildVideoQueue_bounded (cap : Nat) (frames : Array VideoFrame) :
    EdgeBufferQueueBounded (buildVideoQueue cap frames) := by
  unfold buildVideoQueue
  exact list_foldl_push_bounded frames.toList _ (edgeBufferQueue_empty_bounded _)

theorem buildAudioQueue_bounded (cap : Nat) (af : AudioFrame) :
    EdgeBufferQueueBounded (buildAudioQueue cap af) := by
  unfold buildAudioQueue
  have hEmpty : EdgeBufferQueueBounded (EdgeBufferQueue.empty (Nat.max 1 cap)) := by
    unfold EdgeBufferQueueBounded EdgeBufferQueue.empty
    simp
  exact edgeBufferQueue_push_preserves_bound _ _ hEmpty

end LeanAV.LavfiGraphProofs

