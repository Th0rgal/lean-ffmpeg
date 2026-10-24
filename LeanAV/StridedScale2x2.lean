import Std

namespace LeanAV

def stridedScale2x2Pixel (src : Nat → Fin 256) (stride x y : Nat) : Nat :=
  ((src ((2 * y) * stride + 2 * x)).val +
    (src ((2 * y) * stride + 2 * x + 1)).val +
    (src ((2 * y) * stride + stride + 2 * x)).val +
    (src ((2 * y) * stride + stride + 2 * x + 1)).val + 2) >>> 2

def exactBox2x2Pixel (src : Nat → Fin 256) (stride x y : Nat) : Nat :=
  ((src ((2 * y) * stride + 2 * x)).val +
    (src ((2 * y) * stride + 2 * x + 1)).val +
    (src ((2 * y + 1) * stride + 2 * x)).val +
    (src ((2 * y + 1) * stride + 2 * x + 1)).val + 2) / 4

theorem strided_scale2x2_pixel_eq_exact_box (src : Nat → Fin 256) (stride x y : Nat) :
    stridedScale2x2Pixel src stride x y = exactBox2x2Pixel src stride x y := by
  unfold stridedScale2x2Pixel exactBox2x2Pixel
  rw [Nat.add_mul, Nat.one_mul, Nat.shiftRight_eq_div_pow]

end LeanAV
