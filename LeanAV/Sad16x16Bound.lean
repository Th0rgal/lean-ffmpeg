import Std

namespace LeanAV

theorem sad16x16_u8_bound (pixels : List (Fin 256 × Fin 256))
    (hSize : pixels.length = 256) :
    (pixels.map (fun p => (p.1.val - p.2.val) + (p.2.val - p.1.val))).sum ≤ 65280 := by
  have bound (xs : List (Fin 256 × Fin 256)) :
      (xs.map (fun p => (p.1.val - p.2.val) + (p.2.val - p.1.val))).sum ≤ xs.length * 255 := by
    induction xs with
    | nil => simp
    | cons p ps ih =>
      have ha := p.1.isLt
      have hb := p.2.isLt
      have hd : (p.1.val - p.2.val) + (p.2.val - p.1.val) ≤ 255 := by omega
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega
  have h := bound pixels
  rw [hSize] at h
  exact h

end LeanAV
