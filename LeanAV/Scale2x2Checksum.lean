import Std

namespace LeanAV

def box2x2 (a b c d : Nat) : Nat := (a + b + c + d + 2) >>> 2

def checksum64 : Nat :=
  (List.range 64).foldl (fun acc i =>
    acc + box2x2 i (i + 1) (i + 2) (i + 3)) 0

theorem checksum64_is_stable :
    (List.range 64).foldl (fun acc i => acc + ((i + (i + 1) + (i + 2) + (i + 3) + 2) >>> 2)) 0 = 2144 := by
  decide

end LeanAV
