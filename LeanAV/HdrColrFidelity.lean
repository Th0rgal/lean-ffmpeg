import LeanAV.Format

namespace LeanAV.Format

def hdrBt2020PqLimited : ColrNclxView := {
  colourPrimaries := 9
  transferCharacteristics := 16
  matrixCoefficients := 9
  fullRangeFlag := false }

theorem hdr_colr_bt2020_pq_limited_roundtrip :
    decodeColrNclxBoxSpec (encodeColrNclxBoxSpec hdrBt2020PqLimited) = some hdrBt2020PqLimited ∧
    encodeColrNclxBoxSpec hdrBt2020PqLimited =
      [0, 0, 0, 19, 99, 111, 108, 114, 110, 99, 108, 120, 0, 9, 0, 16, 0, 9, 0] := by
  decide

end LeanAV.Format
