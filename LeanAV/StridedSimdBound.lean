import Std

namespace LeanAV

theorem strided_simd_load_bound
    (stride cap vecBytes offset rowBase : Nat)
    (hStride : stride ≤ 1000000000) (hCap : cap ≤ 1000000000)
    (hVec : vecBytes ≤ 1000000000) (hOffset : offset ≤ 1000000000)
    (hBase : rowBase ≤ 1000000000)
    (hRow : rowBase + stride ≤ cap)
    (hLoad : offset + vecBytes ≤ stride) :
    rowBase + offset + vecBytes ≤ cap := by
  omega

end LeanAV
