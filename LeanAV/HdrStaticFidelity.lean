import LeanAV.Format

namespace LeanAV.Format

def hdrMdcvClip : MdcvLuminanceView := {
  maxDisplayMasteringLuminance := 10000000
  minDisplayMasteringLuminance := 1 }

def hdrClliClip : ClliBoxView := {
  maxContentLightLevel := 774
  maxPicAverageLightLevel := 263 }

theorem hdr_static_clip_roundtrip :
    decodeMdcvDciP3BoxSpec (encodeMdcvDciP3BoxSpec hdrMdcvClip) = some hdrMdcvClip ∧
    decodeClliBoxSpec (encodeClliBoxSpec hdrClliClip) = some hdrClliClip := by
  decide

end LeanAV.Format
