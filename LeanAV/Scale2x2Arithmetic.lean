import Std

namespace LeanAV

theorem scale2x2_rounded_sum_shift_eq_box (s : Nat) (_h : s ≤ 1020) :
    (s + 2) >>> 2 = (s + 2) / 4 := by
  rw [Nat.shiftRight_eq_div_pow]

end LeanAV
