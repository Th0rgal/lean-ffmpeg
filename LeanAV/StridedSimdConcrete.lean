import Std

namespace LeanAV

theorem luma_4k_simd_load_bound (dx dy : Nat)
    (hx : dx + 32 ≤ 1920) (hy : dy < 1080) :
    (dy * 2) * 3840 + dx * 2 + 64 ≤ 8294400 ∧
    (dy * 2 + 1) * 3840 + dx * 2 + 64 ≤ 8294400 := by
  omega

end LeanAV
