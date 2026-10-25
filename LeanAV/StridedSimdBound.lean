import Std

namespace LeanAV

theorem strided_simd_load_bound
    (stride cap vecBytes offset rowBase : Nat)
    (_hStride : stride ≤ 1000000000) (_hCap : cap ≤ 1000000000)
    (_hVec : vecBytes ≤ 1000000000) (_hOffset : offset ≤ 1000000000)
    (_hBase : rowBase ≤ 1000000000)
    (hRow : rowBase + stride ≤ cap)
    (hLoad : offset + vecBytes ≤ stride) :
    rowBase + offset + vecBytes ≤ cap := by
  omega

end LeanAV
