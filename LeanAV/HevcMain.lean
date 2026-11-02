/-
  LeanAV.HevcMain: ITU-T H.265 / ISO/IEC 23008-2 HEVC Main 8-bit 4:2:0 In-Process Codec
  - Annex-B + ISO/IEC 14496-15 `hvc1`/`hev1`/`hvcC` container framing and RBSP emulation-prevention
  - Full Main profile VPS/SPS/PPS/SliceHeader syntax, ST/LT RPS, scaling lists, tiles, WPP, weighted prediction
  - Context-adaptive binary arithmetic coder (`CabacReader` / `CabacWriter`) and 4x4/8x8/16x16/32x32 residual coding
  - Integer DST-VII 4x4 & DCT-II 4/8/16/32, 35 intra modes, 8-tap luma / 4-tap chroma MC, deblocking, and SAO
  - Deterministic in-process I/P encoder and bit-exact POC-ordered decoder failing closed outside Main 8-bit 4:2:0
-/
import LeanSys.Posix
import LeanAV.Spec
import LeanAV.Core
import LeanAV.Bitstream
import LeanAV.Video
import LeanAV.H264Entropy
import LeanAV.Format

namespace LeanAV.HevcMain

open LeanSys.Posix
open LeanAV.Spec
open LeanAV.Core
open LeanAV.Bitstream
open LeanAV.Video
open LeanAV.H264Entropy
open LeanAV.Format

def nalTrailN : Nat := 0
def nalTrailR : Nat := 1
def nalTsaN : Nat := 2
def nalTsaR : Nat := 3
def nalStsaN : Nat := 4
def nalStsaR : Nat := 5
def nalRadlN : Nat := 6
def nalRadlR : Nat := 7
def nalRaslN : Nat := 8
def nalRaslR : Nat := 9
def nalBlaWLp : Nat := 16
def nalBlaWRadl : Nat := 17
def nalBlaNLp : Nat := 18
def nalIdrWRadl : Nat := 19
def nalIdrNLp : Nat := 20
def nalCraNut : Nat := 21
def nalVps : Nat := 32
def nalSps : Nat := 33
def nalPps : Nat := 34
def nalAud : Nat := 35
def nalEosNut : Nat := 36
def nalEobNut : Nat := 37
def nalFdNut : Nat := 38
def nalSeiPrefix : Nat := 39
def nalSeiSuffix : Nat := 40

def sliceB : Nat := 0
def sliceP : Nat := 1
def sliceI : Nat := 2

@[inline]
def clipInt (v lo hi : Int) : Int :=
  if v < lo then lo else if v > hi then hi else v

@[inline]
def clipU8Int (v : Int) : UInt8 :=
  if v <= 0 then 0 else if v >= 255 then 255 else v.toNat.toUInt8

def ceilLog2Nat (x : Nat) : Nat :=
  if x <= 1 then 0
  else
    let rec go (v acc fuel : Nat) : Nat :=
      match fuel with
      | 0 => acc
      | fuel' + 1 =>
        if v == 0 then acc else go (v >>> 1) (acc + 1) fuel'
    go (x - 1) 0 64

@[inline]
def natBitLen (x : Nat) : Nat :=
  let rec go (v acc fuel : Nat) : Nat :=
    match fuel with
    | 0 => acc
    | fuel' + 1 =>
      if v == 0 then acc else go (v >>> 1) (acc + 1) fuel'
  go x 0 64
def hevcCabacElemOffset : Array Nat := #[
  0, 1, 2, 2, 2, 2, 2, 2, 5, 6, 9, 12, 13, 17, 17, 18,
  18, 18, 20, 21, 22, 27, 29, 31, 33, 35, 35, 35, 36, 37, 40, 42,
  47, 49, 51, 53, 71, 89, 89, 89, 93, 137, 161, 167, 167, 167, 175, 177,
  178
]

def hevcCabacInitValues : Array (Array Nat) := #[
  #[
    153, 200, 139, 141, 157, 154, 154, 154, 154, 154, 154, 154, 154, 184, 154, 154,
    154, 184, 63, 139, 154, 154, 154, 154, 154, 154, 154, 154, 154, 154, 154, 154,
    154, 154, 154, 154, 154, 153, 138, 138, 111, 141, 94, 138, 182, 154, 154, 139,
    139, 139, 139, 139, 139, 110, 110, 124, 125, 140, 153, 125, 127, 140, 109, 111,
    143, 127, 111, 79, 108, 123, 63, 110, 110, 124, 125, 140, 153, 125, 127, 140,
    109, 111, 143, 127, 111, 79, 108, 123, 63, 91, 171, 134, 141, 111, 111, 125,
    110, 110, 94, 124, 108, 124, 107, 125, 141, 179, 153, 125, 107, 125, 141, 179,
    153, 125, 107, 125, 141, 179, 153, 125, 140, 139, 182, 182, 152, 136, 152, 136,
    153, 136, 139, 111, 136, 139, 111, 141, 111, 140, 92, 137, 138, 140, 152, 138,
    139, 153, 74, 149, 92, 139, 107, 122, 152, 140, 179, 166, 182, 140, 227, 122,
    197, 138, 153, 136, 167, 152, 152, 154, 154, 154, 154, 154, 154, 154, 154, 154,
    154, 154, 154
  ],
  #[
    153, 185, 107, 139, 126, 154, 197, 185, 201, 154, 154, 154, 149, 154, 139, 154,
    154, 154, 152, 139, 110, 122, 95, 79, 63, 31, 31, 153, 153, 153, 153, 140,
    198, 140, 198, 168, 79, 124, 138, 94, 153, 111, 149, 107, 167, 154, 154, 139,
    139, 139, 139, 139, 139, 125, 110, 94, 110, 95, 79, 125, 111, 110, 78, 110,
    111, 111, 95, 94, 108, 123, 108, 125, 110, 94, 110, 95, 79, 125, 111, 110,
    78, 110, 111, 111, 95, 94, 108, 123, 108, 121, 140, 61, 154, 155, 154, 139,
    153, 139, 123, 123, 63, 153, 166, 183, 140, 136, 153, 154, 166, 183, 140, 136,
    153, 154, 166, 183, 140, 136, 153, 154, 170, 153, 123, 123, 107, 121, 107, 121,
    167, 151, 183, 140, 151, 183, 140, 140, 140, 154, 196, 196, 167, 154, 152, 167,
    182, 182, 134, 149, 136, 153, 121, 136, 137, 169, 194, 166, 167, 154, 167, 137,
    182, 107, 167, 91, 122, 107, 167, 154, 154, 154, 154, 154, 154, 154, 154, 154,
    154, 154, 154
  ],
  #[
    153, 160, 107, 139, 126, 154, 197, 185, 201, 154, 154, 154, 134, 154, 139, 154,
    154, 183, 152, 139, 154, 137, 95, 79, 63, 31, 31, 153, 153, 153, 153, 169,
    198, 169, 198, 168, 79, 224, 167, 122, 153, 111, 149, 92, 167, 154, 154, 139,
    139, 139, 139, 139, 139, 125, 110, 124, 110, 95, 94, 125, 111, 111, 79, 125,
    126, 111, 111, 79, 108, 123, 93, 125, 110, 124, 110, 95, 94, 125, 111, 111,
    79, 125, 126, 111, 111, 79, 108, 123, 93, 121, 140, 61, 154, 170, 154, 139,
    153, 139, 123, 123, 63, 124, 166, 183, 140, 136, 153, 154, 166, 183, 140, 136,
    153, 154, 166, 183, 140, 136, 153, 154, 170, 153, 138, 138, 122, 121, 122, 121,
    167, 151, 183, 140, 151, 183, 140, 140, 140, 154, 196, 167, 167, 154, 152, 167,
    182, 182, 134, 149, 136, 153, 121, 136, 122, 169, 208, 166, 167, 154, 152, 167,
    182, 107, 167, 91, 107, 107, 167, 154, 154, 154, 154, 154, 154, 154, 154, 154,
    154, 154, 154
  ]
]

def hevcCabacCtxIdxMap : Array Nat := #[
  0, 1, 4, 5, 2, 3, 4, 5, 6, 6, 8, 8, 7, 7, 8, 8,
  1, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
  2, 2, 2, 2, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0,
  2, 1, 0, 0, 2, 1, 0, 0, 2, 1, 0, 0, 2, 1, 0, 0,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2
]

def hevcScan1x1 : Array Nat := #[
  0
]

def hevcDiagScan2x2X : Array Nat := #[
  0, 0, 1, 1
]

def hevcDiagScan2x2Y : Array Nat := #[
  0, 1, 0, 1
]

def hevcDiagScan2x2Inv : Array (Array Nat) := #[
  #[0, 2],
  #[1, 3]
]

def hevcHorizScan2x2X : Array Nat := #[
  0, 1, 0, 1
]

def hevcHorizScan2x2Y : Array Nat := #[
  0, 0, 1, 1
]

def hevcDiagScan4x4X : Array Nat := #[
  0, 0, 1, 0, 1, 2, 0, 1, 2, 3, 1, 2, 3, 2, 3, 3
]

def hevcDiagScan4x4Y : Array Nat := #[
  0, 1, 0, 2, 1, 0, 3, 2, 1, 0, 3, 2, 1, 3, 2, 3
]

def hevcDiagScan4x4Inv : Array (Array Nat) := #[
  #[0, 2, 5, 9],
  #[1, 4, 8, 12],
  #[3, 7, 11, 14],
  #[6, 10, 13, 15]
]

def hevcHorizScan4x4X : Array Nat := #[
  0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3
]

def hevcHorizScan4x4Y : Array Nat := #[
  0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3
]

def hevcDiagScan8x8X : Array Nat := #[
  0, 0, 1, 0, 1, 2, 0, 1, 2, 3, 0, 1, 2, 3, 4, 0,
  1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3,
  4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 2, 3, 4, 5, 6,
  7, 3, 4, 5, 6, 7, 4, 5, 6, 7, 5, 6, 7, 6, 7, 7
]

def hevcDiagScan8x8Y : Array Nat := #[
  0, 1, 0, 2, 1, 0, 3, 2, 1, 0, 4, 3, 2, 1, 0, 5,
  4, 3, 2, 1, 0, 6, 5, 4, 3, 2, 1, 0, 7, 6, 5, 4,
  3, 2, 1, 0, 7, 6, 5, 4, 3, 2, 1, 7, 6, 5, 4, 3,
  2, 7, 6, 5, 4, 3, 7, 6, 5, 4, 7, 6, 5, 7, 6, 7
]

def hevcDiagScan8x8Inv : Array (Array Nat) := #[
  #[0, 2, 5, 9, 14, 20, 27, 35],
  #[1, 4, 8, 13, 19, 26, 34, 42],
  #[3, 7, 12, 18, 25, 33, 41, 48],
  #[6, 11, 17, 24, 32, 40, 47, 53],
  #[10, 16, 23, 31, 39, 46, 52, 57],
  #[15, 22, 30, 38, 45, 51, 56, 60],
  #[21, 29, 37, 44, 50, 55, 59, 62],
  #[28, 36, 43, 49, 54, 58, 61, 63]
]

def hevcLevelScale : Array Int := #[
  40, 45, 51, 57, 64, 72
]

def hevcQpC : Array Int := #[
  29, 30, 31, 32, 33, 33, 34, 34, 35, 35, 36, 36, 37, 37
]

def hevcBetaTable : Array Int := #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 22, 24,
  26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46, 48, 50, 52, 54, 56,
  58, 60, 62, 64
]

def hevcTcTable : Array Int := #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3,
  3, 3, 3, 4, 4, 4, 5, 5, 6, 6, 7, 8, 9, 10, 11, 13,
  14, 16, 18, 20, 22, 24
]

def hevcDefaultScalingListIntra : Array Int := #[
  16, 16, 16, 16, 17, 18, 21, 24, 16, 16, 16, 16, 17, 19, 22, 25,
  16, 16, 17, 18, 20, 22, 25, 29, 16, 16, 18, 21, 24, 27, 31, 36,
  17, 17, 20, 24, 30, 35, 41, 47, 18, 19, 22, 27, 35, 44, 54, 65,
  21, 22, 25, 31, 41, 54, 70, 88, 24, 25, 29, 36, 47, 65, 88, 115
]

def hevcDefaultScalingListInter : Array Int := #[
  16, 16, 16, 16, 17, 18, 20, 24, 16, 16, 16, 17, 18, 20, 24, 25,
  16, 16, 17, 18, 20, 24, 25, 28, 16, 17, 18, 20, 24, 25, 28, 33,
  17, 18, 20, 24, 25, 28, 33, 41, 18, 20, 24, 25, 28, 33, 41, 54,
  20, 24, 25, 28, 33, 41, 54, 71, 24, 25, 28, 33, 41, 54, 71, 91
]

def hevcSubWidthC : Array Nat := #[
  1, 2, 2, 1
]

def hevcSubHeightC : Array Nat := #[
  1, 2, 1, 1
]

def hevcDspTransform : Array (Array Int) := #[
  #[
    64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64,
    64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64
  ],
  #[
    90, 90, 88, 85, 82, 78, 73, 67, 61, 54, 46, 38, 31, 22, 13, 4,
    -4, -13, -22, -31, -38, -46, -54, -61, -67, -73, -78, -82, -85, -88, -90, -90
  ],
  #[
    90, 87, 80, 70, 57, 43, 25, 9, -9, -25, -43, -57, -70, -80, -87, -90,
    -90, -87, -80, -70, -57, -43, -25, -9, 9, 25, 43, 57, 70, 80, 87, 90
  ],
  #[
    90, 82, 67, 46, 22, -4, -31, -54, -73, -85, -90, -88, -78, -61, -38, -13,
    13, 38, 61, 78, 88, 90, 85, 73, 54, 31, 4, -22, -46, -67, -82, -90
  ],
  #[
    89, 75, 50, 18, -18, -50, -75, -89, -89, -75, -50, -18, 18, 50, 75, 89,
    89, 75, 50, 18, -18, -50, -75, -89, -89, -75, -50, -18, 18, 50, 75, 89
  ],
  #[
    88, 67, 31, -13, -54, -82, -90, -78, -46, -4, 38, 73, 90, 85, 61, 22,
    -22, -61, -85, -90, -73, -38, 4, 46, 78, 90, 82, 54, 13, -31, -67, -88
  ],
  #[
    87, 57, 9, -43, -80, -90, -70, -25, 25, 70, 90, 80, 43, -9, -57, -87,
    -87, -57, -9, 43, 80, 90, 70, 25, -25, -70, -90, -80, -43, 9, 57, 87
  ],
  #[
    85, 46, -13, -67, -90, -73, -22, 38, 82, 88, 54, -4, -61, -90, -78, -31,
    31, 78, 90, 61, 4, -54, -88, -82, -38, 22, 73, 90, 67, 13, -46, -85
  ],
  #[
    83, 36, -36, -83, -83, -36, 36, 83, 83, 36, -36, -83, -83, -36, 36, 83,
    83, 36, -36, -83, -83, -36, 36, 83, 83, 36, -36, -83, -83, -36, 36, 83
  ],
  #[
    82, 22, -54, -90, -61, 13, 78, 85, 31, -46, -90, -67, 4, 73, 88, 38,
    -38, -88, -73, -4, 67, 90, 46, -31, -85, -78, -13, 61, 90, 54, -22, -82
  ],
  #[
    80, 9, -70, -87, -25, 57, 90, 43, -43, -90, -57, 25, 87, 70, -9, -80,
    -80, -9, 70, 87, 25, -57, -90, -43, 43, 90, 57, -25, -87, -70, 9, 80
  ],
  #[
    78, -4, -82, -73, 13, 85, 67, -22, -88, -61, 31, 90, 54, -38, -90, -46,
    46, 90, 38, -54, -90, -31, 61, 88, 22, -67, -85, -13, 73, 82, 4, -78
  ],
  #[
    75, -18, -89, -50, 50, 89, 18, -75, -75, 18, 89, 50, -50, -89, -18, 75,
    75, -18, -89, -50, 50, 89, 18, -75, -75, 18, 89, 50, -50, -89, -18, 75
  ],
  #[
    73, -31, -90, -22, 78, 67, -38, -90, -13, 82, 61, -46, -88, -4, 85, 54,
    -54, -85, 4, 88, 46, -61, -82, 13, 90, 38, -67, -78, 22, 90, 31, -73
  ],
  #[
    70, -43, -87, 9, 90, 25, -80, -57, 57, 80, -25, -90, -9, 87, 43, -70,
    -70, 43, 87, -9, -90, -25, 80, 57, -57, -80, 25, 90, 9, -87, -43, 70
  ],
  #[
    67, -54, -78, 38, 85, -22, -90, 4, 90, 13, -88, -31, 82, 46, -73, -61,
    61, 73, -46, -82, 31, 88, -13, -90, -4, 90, 22, -85, -38, 78, 54, -67
  ],
  #[
    64, -64, -64, 64, 64, -64, -64, 64, 64, -64, -64, 64, 64, -64, -64, 64,
    64, -64, -64, 64, 64, -64, -64, 64, 64, -64, -64, 64, 64, -64, -64, 64
  ],
  #[
    61, -73, -46, 82, 31, -88, -13, 90, -4, -90, 22, 85, -38, -78, 54, 67,
    -67, -54, 78, 38, -85, -22, 90, 4, -90, 13, 88, -31, -82, 46, 73, -61
  ],
  #[
    57, -80, -25, 90, -9, -87, 43, 70, -70, -43, 87, 9, -90, 25, 80, -57,
    -57, 80, 25, -90, 9, 87, -43, -70, 70, 43, -87, -9, 90, -25, -80, 57
  ],
  #[
    54, -85, -4, 88, -46, -61, 82, 13, -90, 38, 67, -78, -22, 90, -31, -73,
    73, 31, -90, 22, 78, -67, -38, 90, -13, -82, 61, 46, -88, 4, 85, -54
  ],
  #[
    50, -89, 18, 75, -75, -18, 89, -50, -50, 89, -18, -75, 75, 18, -89, 50,
    50, -89, 18, 75, -75, -18, 89, -50, -50, 89, -18, -75, 75, 18, -89, 50
  ],
  #[
    46, -90, 38, 54, -90, 31, 61, -88, 22, 67, -85, 13, 73, -82, 4, 78,
    -78, -4, 82, -73, -13, 85, -67, -22, 88, -61, -31, 90, -54, -38, 90, -46
  ],
  #[
    43, -90, 57, 25, -87, 70, 9, -80, 80, -9, -70, 87, -25, -57, 90, -43,
    -43, 90, -57, -25, 87, -70, -9, 80, -80, 9, 70, -87, 25, 57, -90, 43
  ],
  #[
    38, -88, 73, -4, -67, 90, -46, -31, 85, -78, 13, 61, -90, 54, 22, -82,
    82, -22, -54, 90, -61, -13, 78, -85, 31, 46, -90, 67, 4, -73, 88, -38
  ],
  #[
    36, -83, 83, -36, -36, 83, -83, 36, 36, -83, 83, -36, -36, 83, -83, 36,
    36, -83, 83, -36, -36, 83, -83, 36, 36, -83, 83, -36, -36, 83, -83, 36
  ],
  #[
    31, -78, 90, -61, 4, 54, -88, 82, -38, -22, 73, -90, 67, -13, -46, 85,
    -85, 46, 13, -67, 90, -73, 22, 38, -82, 88, -54, -4, 61, -90, 78, -31
  ],
  #[
    25, -70, 90, -80, 43, 9, -57, 87, -87, 57, -9, -43, 80, -90, 70, -25,
    -25, 70, -90, 80, -43, -9, 57, -87, 87, -57, 9, 43, -80, 90, -70, 25
  ],
  #[
    22, -61, 85, -90, 73, -38, -4, 46, -78, 90, -82, 54, -13, -31, 67, -88,
    88, -67, 31, 13, -54, 82, -90, 78, -46, 4, 38, -73, 90, -85, 61, -22
  ],
  #[
    18, -50, 75, -89, 89, -75, 50, -18, -18, 50, -75, 89, -89, 75, -50, 18,
    18, -50, 75, -89, 89, -75, 50, -18, -18, 50, -75, 89, -89, 75, -50, 18
  ],
  #[
    13, -38, 61, -78, 88, -90, 85, -73, 54, -31, 4, 22, -46, 67, -82, 90,
    -90, 82, -67, 46, -22, -4, 31, -54, 73, -85, 90, -88, 78, -61, 38, -13
  ],
  #[
    9, -25, 43, -57, 70, -80, 87, -90, 90, -87, 80, -70, 57, -43, 25, -9,
    -9, 25, -43, 57, -70, 80, -87, 90, -90, 87, -80, 70, -57, 43, -25, 9
  ],
  #[
    4, -13, 22, -31, 38, -46, 54, -61, 67, -73, 78, -82, 85, -88, 90, -90,
    90, -90, 88, -85, 82, -78, 73, -67, 61, -54, 46, -38, 31, -22, 13, -4
  ]
]

def hevcIntraHorVerDistThresh : Array Nat := #[
  7, 1, 0
]

def hevcIntraPredAngle : Array Int := #[
  32, 26, 21, 17, 13, 9, 5, 2, 0, -2, -5, -9, -13, -17, -21, -26,
  -32, -26, -21, -17, -13, -9, -5, -2, 0, 2, 5, 9, 13, 17, 21, 26,
  32
]

def hevcInvAngle : Array Int := #[
  -4096, -1638, -910, -630, -482, -390, -315, -256, -315, -390, -482, -630,
  -910, -1638, -4096
]
@[inline]
def baGetD (ba : ByteArray) (idx : Nat) (d : UInt8 := 0) : UInt8 :=
  ba.data.getD idx d

structure HevcBitReader where
  data : ByteArray
  pos  : Nat
  deriving Inhabited

namespace HevcBitReader

def ofBytes (data : ByteArray) : HevcBitReader :=
  { data := data, pos := 0 }

def totalBits (r : HevcBitReader) : Nat :=
  r.data.size * 8

def bitsLeft (r : HevcBitReader) : Nat :=
  let tot := r.totalBits
  if r.pos <= tot then tot - r.pos else 0

def getBit (r : HevcBitReader) : Option (Nat × HevcBitReader) :=
  if r.pos >= r.totalBits then none
  else
    let b := baGetD r.data (r.pos / 8) 0
    let v := ((b >>> (7 - (r.pos % 8)).toUInt8) &&& 1).toNat
    some (v, { r with pos := r.pos + 1 })

def getBits (r : HevcBitReader) (n : Nat) : Option (Nat × HevcBitReader) :=
  if n == 0 then some (0, r)
  else if r.pos + n > r.totalBits then none
  else
    let rec loop (k : Nat) (cur : HevcBitReader) (acc : Nat) : Nat × HevcBitReader :=
      match k with
      | 0 => (acc, cur)
      | k' + 1 =>
        match cur.getBit with
        | some (b, cur') => loop k' cur' ((acc <<< 1) ||| b)
        | none => (acc, cur)
    some (loop n r 0)

def skipBits (r : HevcBitReader) (n : Nat) : Option HevcBitReader :=
  if r.pos + n > r.totalBits then none else some { r with pos := r.pos + n }

def getUe (r : HevcBitReader) : Option (Nat × HevcBitReader) :=
  let rec loop (fuel lz : Nat) (cur : HevcBitReader) : Option (Nat × HevcBitReader) :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      match cur.getBit with
      | none => none
      | some (b, cur') =>
        if b == 1 then
          if lz == 0 then some (0, cur')
          else
            match cur'.getBits lz with
            | none => none
            | some (suffix, cur'') => some (((1 <<< lz) - 1) + suffix, cur'')
        else if lz >= 31 then none
        else loop fuel' (lz + 1) cur'
  loop 33 0 r

def getSe (r : HevcBitReader) : Option (Int × HevcBitReader) :=
  match r.getUe with
  | none => none
  | some (v, r') =>
    if v % 2 == 1 then some (Int.ofNat ((v + 1) / 2), r')
    else some (-(Int.ofNat (v / 2)), r')

def alignByte (r : HevcBitReader) : HevcBitReader :=
  let rem := r.pos % 8
  if rem == 0 then r else { r with pos := r.pos + (8 - rem) }

private def byteTrailingZeros (b : UInt8) : Nat :=
  let rec loop (rem tz : Nat) : Nat :=
    match rem with
    | 0 => tz
    | rem' + 1 =>
      if ((b >>> tz.toUInt8) &&& 1) == 0 then loop rem' (tz + 1) else tz
  loop 8 0

def rbspEndBit (r : HevcBitReader) : Nat :=
  let rec loop (i : Nat) : Nat :=
    match i with
    | 0 =>
      let b := baGetD r.data 0 0
      if b == 0 then 0 else 7 - byteTrailingZeros b
    | i' + 1 =>
      let b := baGetD r.data i 0
      if b == 0 then loop i' else i * 8 + (7 - byteTrailingZeros b)
  if r.data.size == 0 then 0 else loop (r.data.size - 1)

def moreRbspData (r : HevcBitReader) : Bool :=
  r.pos < r.rbspEndBit

end HevcBitReader

structure HevcBitWriter where
  buf   : ByteArray
  cur   : UInt8
  nbits : Nat
  deriving Inhabited

namespace HevcBitWriter

def empty : HevcBitWriter :=
  { buf := ByteArray.empty, cur := 0, nbits := 0 }

def putBit (w : HevcBitWriter) (b : Nat) : HevcBitWriter :=
  let cur := (w.cur <<< 1) ||| (b &&& 1).toUInt8
  let nbits := w.nbits + 1
  if nbits == 8 then { buf := w.buf.push cur, cur := 0, nbits := 0 }
  else { w with cur := cur, nbits := nbits }

def putBits (w : HevcBitWriter) (val : Nat) (n : Nat) : HevcBitWriter :=
  let rec loop (k : Nat) (cur : HevcBitWriter) : HevcBitWriter :=
    match k with
    | 0 => cur
    | k' + 1 => loop k' (cur.putBit ((val >>> k') &&& 1))
  loop n w

def putUe (w : HevcBitWriter) (val : Nat) : HevcBitWriter :=
  let v := val + 1
  let bl := natBitLen v
  let zeros := if bl == 0 then 0 else bl - 1
  let w1 := w.putBits 0 zeros
  w1.putBits v bl

def putSe (w : HevcBitWriter) (val : Int) : HevcBitWriter :=
  if val <= 0 then w.putUe ((-val).toNat * 2) else w.putUe (val.toNat * 2 - 1)

def alignZero (w : HevcBitWriter) : HevcBitWriter :=
  let rec loop (cur : HevcBitWriter) (fuel : Nat) : HevcBitWriter :=
    match fuel with
    | 0 => cur
    | fuel' + 1 =>
      if cur.nbits == 0 then cur else loop (cur.putBit 0) fuel'
  loop w 8

def rbspTrailingBits (w : HevcBitWriter) : HevcBitWriter :=
  (w.putBit 1).alignZero

def toBytes (w : HevcBitWriter) : Option ByteArray :=
  if w.nbits == 0 then some w.buf else none

end HevcBitWriter

structure RbspMap where
  rbsp : ByteArray
  map  : Array Nat
  deriving Inhabited

def stripRbspWithMap (ebsp : ByteArray) : Option RbspMap :=
  let n := ebsp.size
  let rec loop (fuel i zeros : Nat) (out : Array UInt8) (rmap : Array Nat) : Option RbspMap :=
    match fuel with
    | 0 => some { rbsp := ByteArray.mk out, map := rmap }
    | fuel' + 1 =>
      if i >= n then some { rbsp := ByteArray.mk out, map := rmap }
      else
        let b := baGetD ebsp i 0
        if zeros >= 2 && b == 3 then
          if i + 1 < n && (baGetD ebsp (i + 1) 0).toNat > 3 then none
          else if i + 1 == n then none
          else loop fuel' (i + 1) 0 out rmap
        else
          let out' := out.push b
          let zeros' := if b == 0 then zeros + 1 else 0
          let i' := i + 1
          loop fuel' i' zeros' out' (rmap.push i')
  loop n 0 0 #[] #[0]

def insertRbspEpb (rbsp : ByteArray) : ByteArray :=
  let n := rbsp.size
  let rec loop (fuel i zeros : Nat) (out : Array UInt8) : ByteArray :=
    match fuel with
    | 0 => ByteArray.mk out
    | fuel' + 1 =>
      if i >= n then ByteArray.mk out
      else
        let b := baGetD rbsp i 0
        let (out1, zeros1) :=
          if zeros >= 2 && b.toNat <= 3 then (out.push 3, 0) else (out, zeros)
        let out2 := out1.push b
        let zeros2 := if b == 0 then zeros1 + 1 else 0
        loop fuel' (i + 1) zeros2 out2
  loop n 0 0 #[]

def packHevcNal (nalType layerId tidPlus1 : Nat) (rbspBody : ByteArray) : ByteArray :=
  let b0 : UInt8 := (((nalType &&& 0x3F) <<< 1) ||| ((layerId >>> 5) &&& 1)).toUInt8
  let b1 : UInt8 := (((layerId &&& 0x1F) <<< 3) ||| (tidPlus1 &&& 0x7)).toUInt8
  let body := insertRbspEpb rbspBody
  ByteArray.mk (#[b0, b1] ++ body.data)

def parseNalHeader (nal : ByteArray) : Option (Nat × Nat × Nat) :=
  if nal.size < 2 then none
  else
    let b0 := (baGetD nal 0 0).toNat
    let b1 := (baGetD nal 1 0).toNat
    if (b0 &&& 0x80) != 0 then none
    else
      let nalType := (b0 >>> 1) &&& 0x3F
      let layerId := ((b0 &&& 1) <<< 5) ||| ((b1 >>> 3) &&& 0x1F)
      let tidPlus1 := b1 &&& 0x7
      if tidPlus1 == 0 then none else some (nalType, layerId, tidPlus1 - 1)

def splitAnnexB (data : ByteArray) : Array ByteArray := Id.run do
  let n := data.size
  let mut starts : Array (Nat × Nat) := #[]
  let mut i : Nat := 0
  while i + 2 < n do
    if i + 3 < n && baGetD data i 0 == 0 && baGetD data (i + 1) 0 == 0 &&
        baGetD data (i + 2) 0 == 0 && baGetD data (i + 3) 0 == 1 then
      starts := starts.push (i, 4)
      i := i + 4
    else if baGetD data i 0 == 0 && baGetD data (i + 1) 0 == 0 && baGetD data (i + 2) 0 == 1 then
      starts := starts.push (i, 3)
      i := i + 3
    else
      i := i + 1
  let mut nals : Array ByteArray := #[]
  for idx in [:starts.size] do
    let (pos, slen) := starts[idx]!
    let endPos := if idx + 1 < starts.size then (starts[idx + 1]!).1 else n
    let mut raw := data.extract (pos + slen) endPos
    while raw.size > 2 && baGetD raw (raw.size - 1) 0 == 0 do
      raw := raw.extract 0 (raw.size - 1)
    if raw.size > 0 then nals := nals.push raw
  return nals

def readBeN (buf : ByteArray) (off n : Nat) : Option Nat :=
  if off + n > buf.size then none
  else
    let rec loop (k acc : Nat) : Nat :=
      match k with
      | 0 => acc
      | k' + 1 => loop k' ((acc <<< 8) ||| (baGetD buf (off + (n - 1 - k')) 0).toNat)
    some (loop n 0)

structure Mp4Box where
  typ   : Nat
  start : Nat
  «end» : Nat
  deriving Repr, Inhabited

def boxTag (c0 c1 c2 c3 : UInt8) : Nat :=
  (c0.toNat <<< 24) ||| (c1.toNat <<< 16) ||| (c2.toNat <<< 8) ||| c3.toNat

def iterMp4Boxes (buf : ByteArray) (start «end» : Nat) : Option (Array Mp4Box) := Id.run do
  let mut pos := start
  let mut out : Array Mp4Box := #[]
  let mut fuel := buf.size + 1
  while pos + 8 <= «end» && fuel > 0 do
    fuel := fuel - 1
    let some sz0 := readBeN buf pos 4 | return none
    let some typ := readBeN buf (pos + 4) 4 | return none
    let mut sz := sz0
    let mut hdr := 8
    if sz == 1 then
      if pos + 16 > «end» then return none
      let some sz64 := readBeN buf (pos + 8) 8 | return none
      sz := sz64
      hdr := 16
    else if sz == 0 then
      sz := «end» - pos
    if sz < hdr || pos + sz > «end» then return none
    out := out.push { typ := typ, start := pos + hdr, «end» := pos + sz }
    pos := pos + sz
  return some out
structure Mp4TrackTables where
  hvccBytes?   : Option ByteArray := none
  stszSizes    : Array Nat := #[]
  stscEntries  : Array (Nat × Nat × Nat) := #[]
  chunkOffsets : Array Nat := #[]
  deriving Inhabited

def tagFtyp : Nat := boxTag 0x66 0x74 0x79 0x70
def tagMoov : Nat := boxTag 0x6D 0x6F 0x6F 0x76
def tagTrak : Nat := boxTag 0x74 0x72 0x61 0x6B
def tagMdia : Nat := boxTag 0x6D 0x64 0x69 0x61
def tagMinf : Nat := boxTag 0x6D 0x69 0x6E 0x66
def tagStbl : Nat := boxTag 0x73 0x74 0x62 0x6C
def tagStsd : Nat := boxTag 0x73 0x74 0x73 0x64
def tagHvc1 : Nat := boxTag 0x68 0x76 0x63 0x31
def tagHev1 : Nat := boxTag 0x68 0x65 0x76 0x31
def tagHvcc : Nat := boxTag 0x68 0x76 0x63 0x43
def tagStsz : Nat := boxTag 0x73 0x74 0x73 0x7A
def tagStsc : Nat := boxTag 0x73 0x74 0x73 0x63
def tagStco : Nat := boxTag 0x73 0x74 0x63 0x6F
def tagCo64 : Nat := boxTag 0x63 0x6F 0x36 0x34

def walkMp4Tables (data : ByteArray) (s e : Nat) (acc : Mp4TrackTables) :
    Nat → Option Mp4TrackTables
  | 0 => some acc
  | depth + 1 => Id.run do
    let some boxes := iterMp4Boxes data s e | return none
    let mut cur := acc
    for bx in boxes do
      let typ := bx.typ
      let bs := bx.start
      let be := bx.«end»
      if typ == tagTrak || typ == tagMdia || typ == tagMinf || typ == tagStbl then
        let some next := walkMp4Tables data bs be cur depth | return none
        cur := next
      else if typ == tagStsd then
        if bs + 8 > be then return none
        let some cnt := readBeN data (bs + 4) 4 | return none
        if cnt > 0 then
          let some eboxes := iterMp4Boxes data (bs + 8) be | return none
          for ebx in eboxes do
            if ebx.typ == tagHvc1 || ebx.typ == tagHev1 then
              if ebx.start + 78 > ebx.«end» then return none
              let some cboxes := iterMp4Boxes data (ebx.start + 78) ebx.«end» | return none
              for cbx in cboxes do
                if cbx.typ == tagHvcc then
                  cur := { cur with hvccBytes? := some (data.extract cbx.start cbx.«end») }
      else if typ == tagStsz then
        if bs + 12 > be then return none
        let some sampleSize := readBeN data (bs + 4) 4 | return none
        let some sampleCount := readBeN data (bs + 8) 4 | return none
        if sampleSize != 0 then
          cur := { cur with stszSizes := Array.replicate sampleCount sampleSize }
        else
          if bs + 12 + 4 * sampleCount > be then return none
          let mut szs : Array Nat := Array.mkEmpty sampleCount
          for idx in [:sampleCount] do
            let some v := readBeN data (bs + 12 + 4 * idx) 4 | return none
            szs := szs.push v
          cur := { cur with stszSizes := szs }
      else if typ == tagStsc then
        if bs + 8 > be then return none
        let some ecnt := readBeN data (bs + 4) 4 | return none
        if bs + 8 + 12 * ecnt > be then return none
        let mut ents : Array (Nat × Nat × Nat) := Array.mkEmpty ecnt
        for idx in [:ecnt] do
          let some fc := readBeN data (bs + 8 + 12 * idx) 4 | return none
          let some spc := readBeN data (bs + 12 + 12 * idx) 4 | return none
          let some sdi := readBeN data (bs + 16 + 12 * idx) 4 | return none
          ents := ents.push (fc, spc, sdi)
        cur := { cur with stscEntries := ents }
      else if typ == tagStco then
        if bs + 8 > be then return none
        let some ccnt := readBeN data (bs + 4) 4 | return none
        if bs + 8 + 4 * ccnt > be then return none
        let mut offs : Array Nat := Array.mkEmpty ccnt
        for idx in [:ccnt] do
          let some v := readBeN data (bs + 8 + 4 * idx) 4 | return none
          offs := offs.push v
        cur := { cur with chunkOffsets := offs }
      else if typ == tagCo64 then
        if bs + 8 > be then return none
        let some ccnt := readBeN data (bs + 4) 4 | return none
        if bs + 8 + 8 * ccnt > be then return none
        let mut offs : Array Nat := Array.mkEmpty ccnt
        for idx in [:ccnt] do
          let some v := readBeN data (bs + 8 + 8 * idx) 8 | return none
          offs := offs.push v
        cur := { cur with chunkOffsets := offs }
    return some cur

def parseHvccConfig (hvccBytes : ByteArray) : Option (Nat × Array ByteArray) := Id.run do
  if hvccBytes.size < 23 then return none
  if baGetD hvccBytes 0 0 != 1 then return none
  let lenSize := ((baGetD hvccBytes 21 0).toNat &&& 3) + 1
  let numArrays := (baGetD hvccBytes 22 0).toNat
  let mut pos := 23
  let mut paramNals : Array ByteArray := #[]
  for _ in [:numArrays] do
    if pos + 3 > hvccBytes.size then return none
    let some numNalus := readBeN hvccBytes (pos + 1) 2 | return none
    pos := pos + 3
    for _ in [:numNalus] do
      if pos + 2 > hvccBytes.size then return none
      let some nlen := readBeN hvccBytes pos 2 | return none
      pos := pos + 2
      if nlen == 0 || pos + nlen > hvccBytes.size then return none
      paramNals := paramNals.push (hvccBytes.extract pos (pos + nlen))
      pos := pos + nlen
  return some (lenSize, paramNals)

def demuxMp4Hevc (data : ByteArray) : Option (Array ByteArray × ByteArray) := Id.run do
  let some topBoxes := iterMp4Boxes data 0 data.size | return none
  let mut hasFtyp := false
  let mut moovRange? : Option (Nat × Nat) := none
  for bx in topBoxes do
    if bx.typ == tagFtyp then hasFtyp := true
    else if bx.typ == tagMoov then moovRange? := some (bx.start, bx.«end»)
  let some (ms, me) := moovRange? | return none
  if !hasFtyp then return none
  let some tabs := walkMp4Tables data ms me {} 8 | return none
  let some hvccBytes := tabs.hvccBytes? | return none
  let some (lenSize, paramNals) := parseHvccConfig hvccBytes | return none
  if tabs.stszSizes.isEmpty || tabs.chunkOffsets.isEmpty || tabs.stscEntries.isEmpty then
    return none
  let mut sampleNals := paramNals
  let mut sampleIdx := 0
  for chunkIdx in [:tabs.chunkOffsets.size] do
    let chunkNo := chunkIdx + 1
    let mut spc := (tabs.stscEntries[0]!).2.1
    for (fc, sPerC, _) in tabs.stscEntries do
      if chunkNo >= fc then spc := sPerC
    let mut off := tabs.chunkOffsets[chunkIdx]!
    for _ in [:spc] do
      if sampleIdx < tabs.stszSizes.size then
        let ssz := tabs.stszSizes[sampleIdx]!
        sampleIdx := sampleIdx + 1
        if off + ssz > data.size then return none
        let mut p := 0
        let mut fuel := ssz + 1
        while p < ssz && fuel > 0 do
          fuel := fuel - 1
          if p + lenSize > ssz then return none
          let some nlen := readBeN data (off + p) lenSize | return none
          p := p + lenSize
          if nlen == 0 || p + nlen > ssz then return none
          sampleNals := sampleNals.push (data.extract (off + p) (off + p + nlen))
          p := p + nlen
        off := off + ssz
  return some (sampleNals, hvccBytes)

def extractHevcNals (data : ByteArray) : Option (Array ByteArray × String) :=
  if data.size >= 8 && readBeN data 4 4 == some tagFtyp then
    match demuxMp4Hevc data with
    | some (nals, _) => some (nals, "mp4")
    | none => none
  else
    some (splitAnnexB data, "annexb")

structure HevcPtl where
  profileSpace  : Nat := 0
  tierFlag      : Nat := 0
  profileIdc    : Nat := 0
  compatFlags   : Array Nat := Array.replicate 32 0
  levelIdc      : Nat := 0
  deriving Repr, DecidableEq, Inhabited

def parsePtl (gb0 : HevcBitReader) (profilePresent : Bool)
    (maxSubLayers : Nat) : Option (HevcPtl × HevcBitReader) := Id.run do
  let mut gb := gb0
  let mut profileSpace := 0
  let mut tierFlag := 0
  let mut profileIdc := 0
  let mut compat : Array Nat := Array.replicate 32 0
  if profilePresent then
    let some (ps, g1) := gb.getBits 2 | return none
    let some (tf, g2) := g1.getBit | return none
    let some (pi, g3) := g2.getBits 5 | return none
    profileSpace := ps
    tierFlag := tf
    profileIdc := pi
    gb := g3
    let mut cf : Array Nat := Array.mkEmpty 32
    for _ in [:32] do
      let some (b, gn) := gb.getBit | return none
      cf := cf.push b
      gb := gn
    compat := cf
    if profileIdc == 0 then
      let mut found := 0
      for j in [1:32] do
        if found == 0 && compat.getD j 0 == 1 then found := j
      profileIdc := found
    let some g4 := gb.skipBits 48 | return none
    gb := g4
  let some (lvl, g5) := gb.getBits 8 | return none
  gb := g5
  let mut subProf : Array Nat := #[]
  let mut subLvl : Array Nat := #[]
  if maxSubLayers > 1 then
    for _ in [:maxSubLayers - 1] do
      let some (sp, ga) := gb.getBit | return none
      let some (sl, gb') := ga.getBit | return none
      subProf := subProf.push sp
      subLvl := subLvl.push sl
      gb := gb'
    for _ in [maxSubLayers - 1 : 8] do
      let some gs := gb.skipBits 2 | return none
      gb := gs
    for i in [:maxSubLayers - 1] do
      if subProf.getD i 0 == 1 then
        let some gs := gb.skipBits 88 | return none
        gb := gs
      if subLvl.getD i 0 == 1 then
        let some gs := gb.skipBits 8 | return none
        gb := gs
  return some ({
    profileSpace := profileSpace
    tierFlag := tierFlag
    profileIdc := profileIdc
    compatFlags := compat
    levelIdc := lvl
  }, gb)

structure HevcVps where
  vpsId         : Nat
  maxLayers     : Nat
  maxSubLayers  : Nat
  tempIdNesting : Nat
  ptl           : HevcPtl
  deriving Repr, DecidableEq, Inhabited

def parseVps (rbsp : ByteArray) : Option HevcVps := Id.run do
  let gb0 := HevcBitReader.ofBytes rbsp
  let some (vpsId, g1) := gb0.getBits 4 | return none
  let some (res3, g2) := g1.getBits 2 | return none
  if res3 != 3 then return none
  let some (mlm1, g3) := g2.getBits 6 | return none
  let some (mslm1, g4) := g3.getBits 3 | return none
  let maxLayers := mlm1 + 1
  let maxSubLayers := mslm1 + 1
  let some (tin, g5) := g4.getBit | return none
  let some (resFf, g6) := g5.getBits 16 | return none
  if resFf != 0xFFFF then return none
  let some (ptl, g7) := parsePtl g6 true maxSubLayers | return none
  let some (subOrd, g8) := g7.getBit | return none
  let start := if subOrd == 1 then 0 else maxSubLayers - 1
  let mut gb := g8
  for _ in [start:maxSubLayers] do
    let some (_, ga) := gb.getUe | return none
    let some (_, gb') := ga.getUe | return none
    let some (_, gc) := gb'.getUe | return none
    gb := gc
  return some {
    vpsId := vpsId
    maxLayers := maxLayers
    maxSubLayers := maxSubLayers
    tempIdNesting := tin
    ptl := ptl
  }

structure HevcScalingList where
  sl   : Array (Array (Array Int))
  slDc : Array (Array Int)
  deriving Repr, DecidableEq, Inhabited

def defaultScalingListData : HevcScalingList := Id.run do
  let row0 : Array (Array Int) := Array.replicate 6 (Array.replicate 16 16)
  let mut sl : Array (Array (Array Int)) := #[row0]
  for _ in [1:4] do
    let mut mats : Array (Array Int) := Array.mkEmpty 6
    for matrixId in [:6] do
      let src := if matrixId < 3 then hevcDefaultScalingListIntra else hevcDefaultScalingListInter
      mats := mats.push src
    sl := sl.push mats
  let slDc : Array (Array Int) := Array.replicate 2 (Array.replicate 6 16)
  return { sl := sl, slDc := slDc }

def parseScalingListData (gb0 : HevcBitReader) (chromaFormatIdc : Nat) :
    Option (HevcScalingList × HevcBitReader) := Id.run do
  let d := defaultScalingListData
  let mut sl := d.sl
  let mut slDc := d.slDc
  let mut gb := gb0
  for sizeId in [:4] do
    let step := if sizeId == 3 then 3 else 1
    let mut matrixId := 0
    while matrixId < 6 do
      let some (flag, g1) := gb.getBit | return none
      gb := g1
      if flag == 0 then
        let some (deltaRaw, g2) := gb.getUe | return none
        gb := g2
        let delta := deltaRaw * step
        if delta > matrixId then return none
        if delta == 0 then
          if sizeId == 0 then
            let row := (sl.getD 0 #[]).set! matrixId (Array.replicate 16 16)
            sl := sl.set! 0 row
          else
            if sizeId > 1 then
              let drow := (slDc.getD (sizeId - 2) #[]).set! matrixId 16
              slDc := slDc.set! (sizeId - 2) drow
            let src :=
              if matrixId < 3 then hevcDefaultScalingListIntra else hevcDefaultScalingListInter
            let row := (sl.getD sizeId #[]).set! matrixId src
            sl := sl.set! sizeId row
        else
          let prevMat := (sl.getD sizeId #[]).getD (matrixId - delta) #[]
          let row := (sl.getD sizeId #[]).set! matrixId prevMat
          sl := sl.set! sizeId row
          if sizeId > 1 then
            let pv := (slDc.getD (sizeId - 2) #[]).getD (matrixId - delta) 16
            let drow := (slDc.getD (sizeId - 2) #[]).set! matrixId pv
            slDc := slDc.set! (sizeId - 2) drow
      else
        let mut nextCoef : Int := 8
        let coefNum := Nat.min 64 (1 <<< (4 + (sizeId <<< 1)))
        if sizeId > 1 then
          let some (dcMinus8, g2) := gb.getSe | return none
          gb := g2
          if dcMinus8 < -7 || dcMinus8 > 247 then return none
          nextCoef := dcMinus8 + 8
          let drow := (slDc.getD (sizeId - 2) #[]).set! matrixId nextCoef
          slDc := slDc.set! (sizeId - 2) drow
        let scanX := if sizeId == 0 then hevcDiagScan4x4X else hevcDiagScan8x8X
        let scanY := if sizeId == 0 then hevcDiagScan4x4Y else hevcDiagScan8x8Y
        let side := if sizeId == 0 then 4 else 8
        let mut mat := (sl.getD sizeId #[]).getD matrixId #[]
        for i in [:coefNum] do
          let some (coefDelta, g3) := gb.getSe | return none
          gb := g3
          nextCoef := ((nextCoef + 256 + coefDelta) % 256 + 256) % 256
          let pos := scanY.getD i 0 * side + scanX.getD i 0
          mat := mat.set! pos nextCoef
        let row := (sl.getD sizeId #[]).set! matrixId mat
        sl := sl.set! sizeId row
      matrixId := matrixId + step
  if chromaFormatIdc == 3 then
    let r2 := sl.getD 2 #[]
    let mut r3 := sl.getD 3 #[]
    for m in [1, 2, 4, 5] do
      r3 := r3.set! m (r2.getD m #[])
    sl := sl.set! 3 r3
    let d0 := slDc.getD 0 #[]
    let mut d1 := slDc.getD 1 #[]
    for m in [1, 2, 4, 5] do
      d1 := d1.set! m (d0.getD m 16)
    slDc := slDc.set! 1 d1
  return some ({ sl := sl, slDc := slDc }, gb)

structure HevcShortTermRps where
  numNegativePics : Nat := 0
  numDeltaPocs    : Nat := 0
  deltaPoc        : Array Int := #[]
  used            : Array Nat := #[]
  deriving Repr, DecidableEq, Inhabited

private def sortRpsPairsAsc (pairs : Array (Int × Nat)) : Array (Int × Nat) := Id.run do
  let mut a := pairs
  for i in [:a.size] do
    let mut j := i
    while j > 0 && (a[j]!).1 < (a[j - 1]!).1 do
      let tmp := a[j - 1]!
      a := a.set! (j - 1) (a[j]!)
      a := a.set! j tmp
      j := j - 1
  return a

def parseShortTermRps (gb0 : HevcBitReader) (stRpsList : Array HevcShortTermRps)
    (rpsIdx : Nat) (isSliceHeader : Bool) : Option (HevcShortTermRps × HevcBitReader) := Id.run do
  let mut gb := gb0
  let mut rpsPredict := 0
  if rpsIdx != 0 then
    let some (p, g1) := gb.getBit | return none
    rpsPredict := p
    gb := g1
  if rpsPredict == 1 then
    let mut deltaRpsIdx := 1
    if isSliceHeader then
      let some (d, g1) := gb.getUe | return none
      deltaRpsIdx := d + 1
      gb := g1
    if deltaRpsIdx > rpsIdx || rpsIdx - deltaRpsIdx >= stRpsList.size then return none
    let rpsRidx := stRpsList[rpsIdx - deltaRpsIdx]!
    let some (sign, g2) := gb.getBit | return none
    let some (absM1, g3) := g2.getUe | return none
    gb := g3
    let absDelta : Int := Int.ofNat (absM1 + 1)
    let deltaRps : Int := if sign == 1 then -absDelta else absDelta
    let numR := rpsRidx.deltaPoc.size
    let mut useDelta : Array Nat := Array.replicate (numR + 1) 0
    let mut tmpUsed : Array Nat := Array.replicate (numR + 1) 0
    for i in [:numR + 1] do
      let some (u, ga) := gb.getBit | return none
      gb := ga
      tmpUsed := tmpUsed.set! i u
      if u == 0 then
        let some (ud, gb') := gb.getBit | return none
        gb := gb'
        useDelta := useDelta.set! i ud
      else
        useDelta := useDelta.set! i 1
    let mut pairs : Array (Int × Nat) := #[]
    for i in [:numR] do
      let dPoc := rpsRidx.deltaPoc.getD i 0 + deltaRps
      if useDelta.getD i 0 == 1 then
        pairs := pairs.push (dPoc, tmpUsed.getD i 0)
    if useDelta.getD numR 0 == 1 then
      pairs := pairs.push (deltaRps, tmpUsed.getD numR 0)
    let sorted := sortRpsPairsAsc pairs
    let mut negRev : Array (Int × Nat) := #[]
    let mut posArr : Array (Int × Nat) := #[]
    for p in sorted do
      if p.1 < 0 then negRev := #[p] ++ negRev
      else posArr := posArr.push p
    let allPairs := negRev ++ posArr
    let mut dp : Array Int := Array.mkEmpty allPairs.size
    let mut us : Array Nat := Array.mkEmpty allPairs.size
    for p in allPairs do
      dp := dp.push p.1
      us := us.push p.2
    return some ({
      numNegativePics := negRev.size
      numDeltaPocs := allPairs.size
      deltaPoc := dp
      used := us
    }, gb)
  else
    let some (numNeg, g1) := gb.getUe | return none
    let some (numPos, g2) := g1.getUe | return none
    if numNeg + numPos > 16 then return none
    gb := g2
    let mut dp : Array Int := Array.mkEmpty (numNeg + numPos)
    let mut us : Array Nat := Array.mkEmpty (numNeg + numPos)
    let mut prev : Int := 0
    for _ in [:numNeg] do
      let some (d, ga) := gb.getUe | return none
      let some (u, gb') := ga.getBit | return none
      gb := gb'
      prev := prev - Int.ofNat (d + 1)
      dp := dp.push prev
      us := us.push u
    prev := 0
    for _ in [:numPos] do
      let some (d, ga) := gb.getUe | return none
      let some (u, gb') := ga.getBit | return none
      gb := gb'
      prev := prev + Int.ofNat (d + 1)
      dp := dp.push prev
      us := us.push u
    return some ({
      numNegativePics := numNeg
      numDeltaPocs := dp.size
      deltaPoc := dp
      used := us
    }, gb)

def skipHrdParameters (gb0 : HevcBitReader) (cprmsPresent maxSubLayers : Nat) :
    Option HevcBitReader := Id.run do
  let mut gb := gb0
  let mut nalHrd := 0
  let mut vclHrd := 0
  let mut subPicHrd := 0
  if cprmsPresent == 1 then
    let some (nh, g1) := gb.getBit | return none
    let some (vh, g2) := g1.getBit | return none
    nalHrd := nh
    vclHrd := vh
    gb := g2
    if nalHrd == 1 || vclHrd == 1 then
      let some (sp, g3) := gb.getBit | return none
      subPicHrd := sp
      gb := g3
      if subPicHrd == 1 then
        let some g4 := gb.skipBits 19 | return none
        gb := g4
      let some g5 := gb.skipBits 8 | return none
      gb := g5
      if subPicHrd == 1 then
        let some g6 := gb.skipBits 4 | return none
        gb := g6
      let some g7 := gb.skipBits 15 | return none
      gb := g7
  for _ in [:maxSubLayers] do
    let some (frg, ga) := gb.getBit | return none
    gb := ga
    let mut frw := 1
    if frg == 0 then
      let some (fw, gb') := gb.getBit | return none
      frw := fw
      gb := gb'
    let mut lowDelay := 0
    let mut cpbCnt := 1
    if frw == 1 then
      let some (_, gb') := gb.getUe | return none
      gb := gb'
    else
      let some (ld, gb') := gb.getBit | return none
      lowDelay := ld
      gb := gb'
    if lowDelay == 0 then
      let some (cc, gb') := gb.getUe | return none
      if cc > 31 then return none
      cpbCnt := cc + 1
      gb := gb'
    for flag in [nalHrd, vclHrd] do
      if flag == 1 then
        for _ in [:cpbCnt] do
          let some (_, g1) := gb.getUe | return none
          let some (_, g2) := g1.getUe | return none
          gb := g2
          if subPicHrd == 1 then
            let some (_, g3) := gb.getUe | return none
            let some (_, g4) := g3.getUe | return none
            gb := g4
          let some (_, g5) := gb.getBit | return none
          gb := g5
  return some gb

def skipVui (gb0 : HevcBitReader) (maxSubLayers : Nat) : Option HevcBitReader := Id.run do
  let mut gb := gb0
  let some (arFlag, g1) := gb.getBit | return none
  gb := g1
  if arFlag == 1 then
    let some (ari, g2) := gb.getBits 8 | return none
    gb := g2
    if ari == 255 then
      let some g3 := gb.skipBits 32 | return none
      gb := g3
  let some (osFlag, g2) := gb.getBit | return none
  gb := g2
  if osFlag == 1 then
    let some (_, g3) := gb.getBit | return none
    gb := g3
  let some (vsFlag, g3) := gb.getBit | return none
  gb := g3
  if vsFlag == 1 then
    let some g4 := gb.skipBits 4 | return none
    let some (cdFlag, g5) := g4.getBit | return none
    gb := g5
    if cdFlag == 1 then
      let some g6 := gb.skipBits 24 | return none
      gb := g6
  let some (clFlag, g4) := gb.getBit | return none
  gb := g4
  if clFlag == 1 then
    let some (_, g5) := gb.getUe | return none
    let some (_, g6) := g5.getUe | return none
    gb := g6
  let some g5 := gb.skipBits 3 | return none
  let some (ddFlag, g6) := g5.getBit | return none
  gb := g6
  if ddFlag == 1 then
    for _ in [:4] do
      let some (_, gn) := gb.getUe | return none
      gb := gn
  let some (tiFlag, g7) := gb.getBit | return none
  gb := g7
  if tiFlag == 1 then
    let some g8 := gb.skipBits 64 | return none
    let some (pocProp, g9) := g8.getBit | return none
    gb := g9
    if pocProp == 1 then
      let some (_, g10) := gb.getUe | return none
      gb := g10
    let some (hrdFlag, g11) := gb.getBit | return none
    gb := g11
    if hrdFlag == 1 then
      let some g12 := skipHrdParameters gb 1 maxSubLayers | return none
      gb := g12
  let some (brFlag, g8) := gb.getBit | return none
  gb := g8
  if brFlag == 1 then
    let some g9 := gb.skipBits 3 | return none
    gb := g9
    for _ in [:5] do
      let some (_, gn) := gb.getUe | return none
      gb := gn
  return some gb

structure HevcPcmInfo where
  bitDepth              : Nat
  bitDepthChroma        : Nat
  log2MinPcmCbSize      : Nat
  log2MaxPcmCbSize      : Nat
  loopFilterDisableFlag : Bool
  deriving Repr, DecidableEq, Inhabited

structure HevcSps where
  vpsId                             : Nat := 0
  spsId                             : Nat := 0
  maxSubLayers                      : Nat := 1
  tempIdNesting                     : Nat := 1
  ptl                               : HevcPtl := {}
  chromaFormatIdc                   : Nat := 1
  separateColourPlaneFlag           : Bool := false
  width                             : Nat := 16
  height                            : Nat := 16
  confLeft                          : Nat := 0
  confRight                         : Nat := 0
  confTop                           : Nat := 0
  confBottom                        : Nat := 0
  croppedWidth                      : Nat := 16
  croppedHeight                     : Nat := 16
  bitDepth                          : Nat := 8
  bitDepthChroma                    : Nat := 8
  log2MaxPocLsb                     : Nat := 8
  maxDecPicBuffering                : Array Nat := #[1]
  numReorderPics                    : Array Nat := #[0]
  log2MinCbSize                     : Nat := 3
  log2DiffMaxMinCb                  : Nat := 1
  log2CtbSize                       : Nat := 4
  log2MinTbSize                     : Nat := 2
  log2MaxTrafoSize                  : Nat := 4
  log2MinPuSize                     : Nat := 2
  maxTrafoDepthInter                : Nat := 1
  maxTrafoDepthIntra                : Nat := 1
  scalingListEnableFlag             : Bool := false
  scalingList                       : HevcScalingList := defaultScalingListData
  ampEnabledFlag                    : Bool := false
  saoEnabled                        : Bool := false
  pcmEnabledFlag                    : Bool := false
  pcm?                              : Option HevcPcmInfo := none
  nbStRps                           : Nat := 0
  stRps                             : Array HevcShortTermRps := #[]
  ltPresent                         : Bool := false
  ltPocLsb                          : Array Nat := #[]
  ltUsed                            : Array Nat := #[]
  spsTemporalMvpEnabledFlag         : Bool := false
  spsStrongIntraSmoothingEnableFlag : Bool := false
  ctbWidth                          : Nat := 1
  ctbHeight                         : Nat := 1
  ctbSize                           : Nat := 1
  minCbWidth                        : Nat := 2
  minCbHeight                       : Nat := 2
  minTbWidth                        : Nat := 4
  minTbHeight                       : Nat := 4
  minPuWidth                        : Nat := 4
  minPuHeight                       : Nat := 4
  tbMask                            : Nat := 3
  deriving Repr, DecidableEq, Inhabited

def isMain8Bit420Sps (sps : HevcSps) : Bool :=
  let profOk := sps.ptl.profileIdc == 1 || sps.ptl.compatFlags.getD 1 0 == 1
  let pcmOk :=
    match sps.pcm? with
    | none => true
    | some p => p.bitDepth <= 8 && p.bitDepthChroma <= 8
  profOk &&
  sps.chromaFormatIdc == 1 &&
  !sps.separateColourPlaneFlag &&
  sps.bitDepth == 8 &&
  sps.bitDepthChroma == 8 &&
  pcmOk

def parseSps (rbsp : ByteArray) : Option HevcSps := Id.run do
  let gb0 := HevcBitReader.ofBytes rbsp
  let some (vpsId, g1) := gb0.getBits 4 | return none
  let some (mslM1, g2) := g1.getBits 3 | return none
  let maxSubLayers := mslM1 + 1
  if maxSubLayers > 7 then return none
  let some (tin, g3) := g2.getBit | return none
  let some (ptl, g4) := parsePtl g3 true maxSubLayers | return none
  let some (spsId, g5) := g4.getUe | return none
  if spsId >= 16 then return none
  let some (cfRaw, g6) := g5.getUe | return none
  if cfRaw > 3 then return none
  let mut chromaFormatIdc := cfRaw
  let mut sepPlane := false
  let mut gb := g6
  if chromaFormatIdc == 3 then
    let some (sc, g7) := gb.getBit | return none
    gb := g7
    if sc == 1 then
      sepPlane := true
      chromaFormatIdc := 0
  let some (width, g7) := gb.getUe | return none
  let some (height, g8) := g7.getUe | return none
  if width == 0 || height == 0 || width > 16384 || height > 16384 then return none
  let some (picConf, g9) := g8.getBit | return none
  gb := g9
  let mut confLeft := 0
  let mut confRight := 0
  let mut confTop := 0
  let mut confBottom := 0
  if picConf == 1 then
    let subW := hevcSubWidthC.getD chromaFormatIdc 1
    let subH := hevcSubHeightC.getD chromaFormatIdc 1
    let some (cl, ga) := gb.getUe | return none
    let some (cr, gb') := ga.getUe | return none
    let some (ct, gc) := gb'.getUe | return none
    let some (cb, gd) := gc.getUe | return none
    confLeft := cl * subW
    confRight := cr * subW
    confTop := ct * subH
    confBottom := cb * subH
    gb := gd
  let some (bdY, g10) := gb.getUe | return none
  let some (bdC, g11) := g10.getUe | return none
  let some (lmpl, g12) := g11.getUe | return none
  let bitDepth := bdY + 8
  let bitDepthChroma := bdC + 8
  let log2MaxPocLsb := lmpl + 4
  if log2MaxPocLsb > 16 then return none
  let some (subOrd, g13) := g12.getBit | return none
  gb := g13
  let start := if subOrd == 1 then 0 else maxSubLayers - 1
  let mut maxDecPicBuffering := Array.replicate maxSubLayers 0
  let mut numReorderPics := Array.replicate maxSubLayers 0
  for i in [start:maxSubLayers] do
    let some (mdpb, ga) := gb.getUe | return none
    let some (nrp, gb') := ga.getUe | return none
    let some (_, gc) := gb'.getUe | return none
    maxDecPicBuffering := maxDecPicBuffering.set! i (mdpb + 1)
    numReorderPics := numReorderPics.set! i nrp
    gb := gc
  if subOrd == 0 then
    for i in [:start] do
      maxDecPicBuffering := maxDecPicBuffering.set! i (maxDecPicBuffering.getD start 1)
      numReorderPics := numReorderPics.set! i (numReorderPics.getD start 0)
  let some (lmcbM3, g14) := gb.getUe | return none
  let some (ldmmCb, g15) := g14.getUe | return none
  let some (lmtbM2, g16) := g15.getUe | return none
  let some (ldmmTb, g17) := g16.getUe | return none
  gb := g17
  let log2MinCbSize := lmcbM3 + 3
  let log2CtbSize := log2MinCbSize + ldmmCb
  let log2MinTbSize := lmtbM2 + 2
  let log2MaxTrafoSize := log2MinTbSize + ldmmTb
  if log2MinCbSize < 3 || log2CtbSize < 4 || log2CtbSize > 6 then return none
  if log2MinTbSize >= log2MinCbSize || log2MaxTrafoSize > Nat.min log2CtbSize 5 then return none
  let cbAlign := (1 <<< log2MinCbSize) - 1
  if (width &&& cbAlign) != 0 || (height &&& cbAlign) != 0 then return none
  let some (mtdInter, g18) := gb.getUe | return none
  let some (mtdIntra, g19) := g18.getUe | return none
  let some (slEn, g20) := g19.getBit | return none
  gb := g20
  let mut scalingList := defaultScalingListData
  if slEn == 1 then
    let some (slDataPres, g21) := gb.getBit | return none
    gb := g21
    if slDataPres == 1 then
      let some (slParsed, g22) := parseScalingListData gb chromaFormatIdc | return none
      scalingList := slParsed
      gb := g22
  let some (ampFlag, g21) := gb.getBit | return none
  let some (saoFlag, g22) := g21.getBit | return none
  let some (pcmFlag, g23) := g22.getBit | return none
  gb := g23
  let mut pcm? : Option HevcPcmInfo := none
  if pcmFlag == 1 then
    let some (pbd, ga) := gb.getBits 4 | return none
    let some (pbdc, gb') := ga.getBits 4 | return none
    let some (pminM3, gc) := gb'.getUe | return none
    let some (pdiff, gd) := gc.getUe | return none
    let some (plf, ge) := gd.getBit | return none
    gb := ge
    let pmin := pminM3 + 3
    pcm? := some {
      bitDepth := pbd + 1
      bitDepthChroma := pbdc + 1
      log2MinPcmCbSize := pmin
      log2MaxPcmCbSize := pmin + pdiff
      loopFilterDisableFlag := plf == 1
    }
  let some (nbStRps, g24) := gb.getUe | return none
  if nbStRps > 64 then return none
  gb := g24
  let mut stRps : Array HevcShortTermRps := Array.mkEmpty nbStRps
  for i in [:nbStRps] do
    let some (rpsi, gn) := parseShortTermRps gb stRps i false | return none
    stRps := stRps.push rpsi
    gb := gn
  let some (ltPres, g25) := gb.getBit | return none
  gb := g25
  let mut ltPocLsb : Array Nat := #[]
  let mut ltUsed : Array Nat := #[]
  if ltPres == 1 then
    let some (numLt, g26) := gb.getUe | return none
    if numLt > 32 then return none
    gb := g26
    for _ in [:numLt] do
      let some (lsb, ga) := gb.getBits log2MaxPocLsb | return none
      let some (uf, gb') := ga.getBit | return none
      ltPocLsb := ltPocLsb.push lsb
      ltUsed := ltUsed.push uf
      gb := gb'
  let some (tmvp, g26) := gb.getBit | return none
  let some (sis, g27) := g26.getBit | return none
  let some (vuiPres, g28) := g27.getBit | return none
  gb := g28
  if vuiPres == 1 then
    let some gv := skipVui gb maxSubLayers | return none
    gb := gv
  let some (spsExt, g29) := gb.getBit | return none
  gb := g29
  if spsExt == 1 then
    let some (rextF, ga) := gb.getBit | return none
    let some (mlF, gb') := ga.getBit | return none
    let some (d3F, gc) := gb'.getBit | return none
    let some (sccF, gd) := gc.getBit | return none
    let some ge := gd.skipBits 4 | return none
    gb := ge
    if rextF == 1 then
      let some gf := gb.skipBits 9 | return none
      gb := gf
    if mlF == 1 then
      let some gf := gb.skipBits 1 | return none
      gb := gf
    if d3F == 1 || sccF == 1 then return none
  if confLeft + confRight >= width || confTop + confBottom >= height then
    confLeft := 0
    confRight := 0
    confTop := 0
    confBottom := 0
  let ctbWidth := (width + (1 <<< log2CtbSize) - 1) >>> log2CtbSize
  let ctbHeight := (height + (1 <<< log2CtbSize) - 1) >>> log2CtbSize
  let sps : HevcSps := {
    vpsId := vpsId
    spsId := spsId
    maxSubLayers := maxSubLayers
    tempIdNesting := tin
    ptl := ptl
    chromaFormatIdc := chromaFormatIdc
    separateColourPlaneFlag := sepPlane
    width := width
    height := height
    confLeft := confLeft
    confRight := confRight
    confTop := confTop
    confBottom := confBottom
    croppedWidth := width - confLeft - confRight
    croppedHeight := height - confTop - confBottom
    bitDepth := bitDepth
    bitDepthChroma := bitDepthChroma
    log2MaxPocLsb := log2MaxPocLsb
    maxDecPicBuffering := maxDecPicBuffering
    numReorderPics := numReorderPics
    log2MinCbSize := log2MinCbSize
    log2DiffMaxMinCb := ldmmCb
    log2CtbSize := log2CtbSize
    log2MinTbSize := log2MinTbSize
    log2MaxTrafoSize := log2MaxTrafoSize
    log2MinPuSize := log2MinCbSize - 1
    maxTrafoDepthInter := mtdInter
    maxTrafoDepthIntra := mtdIntra
    scalingListEnableFlag := slEn == 1
    scalingList := scalingList
    ampEnabledFlag := ampFlag == 1
    saoEnabled := saoFlag == 1
    pcmEnabledFlag := pcmFlag == 1
    pcm? := pcm?
    nbStRps := nbStRps
    stRps := stRps
    ltPresent := ltPres == 1
    ltPocLsb := ltPocLsb
    ltUsed := ltUsed
    spsTemporalMvpEnabledFlag := tmvp == 1
    spsStrongIntraSmoothingEnableFlag := sis == 1
    ctbWidth := ctbWidth
    ctbHeight := ctbHeight
    ctbSize := ctbWidth * ctbHeight
    minCbWidth := width >>> log2MinCbSize
    minCbHeight := height >>> log2MinCbSize
    minTbWidth := width >>> log2MinTbSize
    minTbHeight := height >>> log2MinTbSize
    minPuWidth := width >>> (log2MinCbSize - 1)
    minPuHeight := height >>> (log2MinCbSize - 1)
    tbMask := (1 <<< (log2CtbSize - log2MinTbSize)) - 1
  }
  if !isMain8Bit420Sps sps then return none
  return some sps

structure HevcPps where
  ppsId                                   : Nat := 0
  spsId                                   : Nat := 0
  dependentSliceSegmentsEnabledFlag       : Bool := false
  outputFlagPresentFlag                   : Bool := false
  numExtraSliceHeaderBits                 : Nat := 0
  signDataHidingFlag                      : Bool := false
  cabacInitPresentFlag                    : Bool := false
  numRefIdxL0DefaultActive                : Nat := 1
  numRefIdxL1DefaultActive                : Nat := 1
  picInitQpMinus26                        : Int := 0
  constrainedIntraPredFlag                : Bool := false
  transformSkipEnabledFlag                : Bool := false
  log2MaxTransformSkipBlockSize           : Nat := 2
  cuQpDeltaEnabledFlag                    : Bool := false
  diffCuQpDeltaDepth                      : Nat := 0
  cbQpOffset                              : Int := 0
  crQpOffset                              : Int := 0
  picSliceLevelChromaQpOffsetsPresentFlag : Bool := false
  weightedPredFlag                        : Bool := false
  weightedBipredFlag                      : Bool := false
  transquantBypassEnableFlag              : Bool := false
  tilesEnabledFlag                        : Bool := false
  entropyCodingSyncEnabledFlag            : Bool := false
  numTileColumns                          : Nat := 1
  numTileRows                             : Nat := 1
  uniformSpacingFlag                      : Bool := true
  columnWidth                             : Array Nat := #[1]
  rowHeight                               : Array Nat := #[1]
  colBd                                   : Array Nat := #[0, 1]
  rowBd                                   : Array Nat := #[0, 1]
  colIdxX                                 : Array Nat := #[0]
  ctbAddrRsToTs                           : Array Nat := #[0]
  ctbAddrTsToRs                           : Array Nat := #[0]
  tileId                                  : Array Nat := #[0]
  minTbAddrZsTab                          : Array Int := #[-1]
  minTbAddrZsStride                       : Nat := 3
  loopFilterAcrossTilesEnabledFlag        : Bool := true
  seqLoopFilterAcrossSlicesEnabledFlag    : Bool := true
  deblockingFilterControlPresentFlag      : Bool := false
  deblockingFilterOverrideEnabledFlag     : Bool := false
  disableDbf                              : Bool := false
  betaOffset                              : Int := 0
  tcOffset                                : Int := 0
  scalingListDataPresentFlag              : Bool := false
  scalingList                             : HevcScalingList := defaultScalingListData
  listsModificationPresentFlag            : Bool := false
  log2ParallelMergeLevel                  : Nat := 2
  sliceHeaderExtensionPresentFlag         : Bool := false
  chromaQpOffsetEnabled                   : Bool := false
  diffCuChromaQpOffsetDepth               : Nat := 0
  chromaQpOffsetListLenMinus1             : Nat := 0
  cbQpOffsetList                          : Array Int := Array.replicate 6 0
  crQpOffsetList                          : Array Int := Array.replicate 6 0
  deriving Repr, DecidableEq, Inhabited

def buildPpsDerivations (sps : HevcSps) (pps : HevcPps) : Option HevcPps := Id.run do
  let ctbW := sps.ctbWidth
  let ctbH := sps.ctbHeight
  let numCols := pps.numTileColumns
  let numRows := pps.numTileRows
  if numCols == 0 || numRows == 0 then return none
  let mut colW := pps.columnWidth
  let mut rowH := pps.rowHeight
  if pps.uniformSpacingFlag then
    colW := Array.mkEmpty numCols
    for i in [:numCols] do
      colW := colW.push (((i + 1) * ctbW) / numCols - (i * ctbW) / numCols)
    rowH := Array.mkEmpty numRows
    for i in [:numRows] do
      rowH := rowH.push (((i + 1) * ctbH) / numRows - (i * ctbH) / numRows)
  let mut colBd := Array.replicate (numCols + 1) 0
  for i in [:numCols] do
    colBd := colBd.set! (i + 1) (colBd.getD i 0 + colW.getD i 0)
  let mut rowBd := Array.replicate (numRows + 1) 0
  for j in [:numRows] do
    rowBd := rowBd.set! (j + 1) (rowBd.getD j 0 + rowH.getD j 0)
  if colBd.getD numCols 0 != ctbW || rowBd.getD numRows 0 != ctbH then return none
  let mut colIdxX := Array.replicate ctbW 0
  let mut ci := 0
  for x in [:ctbW] do
    if x >= colBd.getD (ci + 1) ctbW then ci := ci + 1
    colIdxX := colIdxX.set! x ci
  let mut rsToTs := Array.replicate sps.ctbSize 0
  let mut tsToRs := Array.replicate sps.ctbSize 0
  let mut tileId := Array.replicate sps.ctbSize 0
  for ctbAddrRs in [:sps.ctbSize] do
    let tbX := ctbAddrRs % ctbW
    let tbY := ctbAddrRs / ctbW
    let tileX := colIdxX.getD tbX 0
    let mut tileY := 0
    for j in [:numRows] do
      if tbY >= rowBd.getD j 0 then tileY := j
    let mut val := 0
    for idx in [:tileX] do
      val := val + rowH.getD tileY 0 * colW.getD idx 0
    for idx in [:tileY] do
      val := val + ctbW * rowH.getD idx 0
    val := val + (tbY - rowBd.getD tileY 0) * colW.getD tileX 0 + (tbX - colBd.getD tileX 0)
    rsToTs := rsToTs.set! ctbAddrRs val
    tsToRs := tsToRs.set! val ctbAddrRs
    tileId := tileId.set! val (tileY * numCols + tileX)
  let log2Diff := sps.log2CtbSize - sps.log2MinTbSize
  let mtbW := sps.minTbWidth
  let mtbH := sps.minTbHeight
  let strideZs := mtbW + 2
  let mut minTbAddrZsTab : Array Int := Array.replicate ((mtbH + 2) * strideZs) (-1)
  for y in [:mtbH] do
    for x in [:mtbW] do
      let tbX := x >>> log2Diff
      let tbY := y >>> log2Diff
      let rs := ctbW * tbY + tbX
      let mut val := (rsToTs.getD rs 0) <<< (log2Diff * 2)
      for k in [:log2Diff] do
        let m := 1 <<< k
        val := val + (((m &&& x) <<< k) + ((m &&& y) <<< (k + 1)))
      minTbAddrZsTab := minTbAddrZsTab.set! ((y + 1) * strideZs + (x + 1)) (Int.ofNat val)
  return some { pps with
    columnWidth := colW
    rowHeight := rowH
    colBd := colBd
    rowBd := rowBd
    colIdxX := colIdxX
    ctbAddrRsToTs := rsToTs
    ctbAddrTsToRs := tsToRs
    tileId := tileId
    minTbAddrZsTab := minTbAddrZsTab
    minTbAddrZsStride := strideZs
  }

@[inline]
def minTbAddrZs (pps : HevcPps) (xTb yTb : Int) : Int :=
  let xi := xTb + 1
  let yi := yTb + 1
  if xi < 0 || yi < 0 then -1
  else
    let idx := yi.toNat * pps.minTbAddrZsStride + xi.toNat
    pps.minTbAddrZsTab.getD idx (-1)

def parsePps (rbsp : ByteArray) (spsMap : Array (Option HevcSps)) : Option HevcPps := Id.run do
  let gb0 := HevcBitReader.ofBytes rbsp
  let some (ppsId, g1) := gb0.getUe | return none
  if ppsId >= 64 then return none
  let some (spsId, g2) := g1.getUe | return none
  if spsId >= spsMap.size then return none
  let some sps := spsMap[spsId]! | return none
  let some (depFlag, g3) := g2.getBit | return none
  let some (outFlag, g4) := g3.getBit | return none
  let some (extraBits, g5) := g4.getBits 3 | return none
  let some (sdh, g6) := g5.getBit | return none
  let some (cabacInit, g7) := g6.getBit | return none
  let some (nr0, g8) := g7.getUe | return none
  let some (nr1, g9) := g8.getUe | return none
  let some (picQp, g10) := g9.getSe | return none
  let some (cip, g11) := g10.getBit | return none
  let some (tskip, g12) := g11.getBit | return none
  let some (cuQpEn, g13) := g12.getBit | return none
  let mut gb := g13
  let mut diffCuQp := 0
  if cuQpEn == 1 then
    let some (d, gn) := gb.getUe | return none
    diffCuQp := d
    gb := gn
  let some (cbOff, g14) := gb.getSe | return none
  let some (crOff, g15) := g14.getSe | return none
  let some (slChroma, g16) := g15.getBit | return none
  let some (wpFlag, g17) := g16.getBit | return none
  let some (wbFlag, g18) := g17.getBit | return none
  let some (tqbFlag, g19) := g18.getBit | return none
  let some (tilesFlag, g20) := g19.getBit | return none
  let some (wppFlag, g21) := g20.getBit | return none
  gb := g21
  let mut numCols := 1
  let mut numRows := 1
  let mut uniform := true
  let mut colW : Array Nat := #[sps.ctbWidth]
  let mut rowH : Array Nat := #[sps.ctbHeight]
  let mut lfAcrossTiles := true
  if tilesFlag == 1 then
    let some (nc, ga) := gb.getUe | return none
    let some (nr, gb') := ga.getUe | return none
    numCols := nc + 1
    numRows := nr + 1
    if numCols > sps.ctbWidth || numRows > sps.ctbHeight then return none
    gb := gb'
    let some (uf, gc) := gb.getBit | return none
    uniform := uf == 1
    gb := gc
    if uf == 0 then
      colW := Array.mkEmpty numCols
      let mut sumW := 0
      for _ in [:numCols - 1] do
        let some (v, gn) := gb.getUe | return none
        colW := colW.push (v + 1)
        sumW := sumW + v + 1
        gb := gn
      if sumW >= sps.ctbWidth then return none
      colW := colW.push (sps.ctbWidth - sumW)
      rowH := Array.mkEmpty numRows
      let mut sumH := 0
      for _ in [:numRows - 1] do
        let some (v, gn) := gb.getUe | return none
        rowH := rowH.push (v + 1)
        sumH := sumH + v + 1
        gb := gn
      if sumH >= sps.ctbHeight then return none
      rowH := rowH.push (sps.ctbHeight - sumH)
    let some (lf, gd) := gb.getBit | return none
    lfAcrossTiles := lf == 1
    gb := gd
  let some (lfSlices, g22) := gb.getBit | return none
  let some (dbfCtrl, g23) := g22.getBit | return none
  gb := g23
  let mut dbfOverride := false
  let mut disableDbf := false
  let mut betaOff : Int := 0
  let mut tcOff : Int := 0
  if dbfCtrl == 1 then
    let some (ov, ga) := gb.getBit | return none
    let some (dis, gb') := ga.getBit | return none
    dbfOverride := ov == 1
    disableDbf := dis == 1
    gb := gb'
    if dis == 0 then
      let some (bo, gc) := gb.getSe | return none
      let some (to, gd) := gc.getSe | return none
      betaOff := bo * 2
      tcOff := to * 2
      gb := gd
  let some (slData, g24) := gb.getBit | return none
  gb := g24
  let mut scalingList := sps.scalingList
  if slData == 1 then
    let some (sl, gn) := parseScalingListData gb sps.chromaFormatIdc | return none
    scalingList := sl
    gb := gn
  let some (lmFlag, g25) := gb.getBit | return none
  let some (lpm, g26) := g25.getUe | return none
  let some (sheFlag, g27) := g26.getBit | return none
  let some (ppsExt, g28) := g27.getBit | return none
  gb := g28
  let mut chromaQpOffsetEnabled := false
  let mut diffCuChromaQpDepth := 0
  let mut chromaQpListLenM1 := 0
  let mut cbQpList := Array.replicate 6 (0 : Int)
  let mut crQpList := Array.replicate 6 (0 : Int)
  let mut log2MaxTskip := 2
  if ppsExt == 1 then
    let some (rext, ga) := gb.getBit | return none
    let some (mlExt, gb') := ga.getBit | return none
    let some (d3Ext, gc) := gb'.getBit | return none
    let some (sccExt, gd) := gc.getBit | return none
    let some ge := gd.skipBits 4 | return none
    gb := ge
    if rext == 1 then
      if tskip == 1 then
        let some (v, gn) := gb.getUe | return none
        log2MaxTskip := v + 2
        gb := gn
      let some (cross, gn) := gb.getBit | return none
      if cross == 1 then return none
      gb := gn
      let some (cqo, gn) := gb.getBit | return none
      gb := gn
      if cqo == 1 then
        chromaQpOffsetEnabled := true
        let some (d, ga') := gb.getUe | return none
        let some (lenM1, gb'') := ga'.getUe | return none
        diffCuChromaQpDepth := d
        chromaQpListLenM1 := lenM1
        gb := gb''
        if lenM1 > 5 then return none
        for i in [:lenM1 + 1] do
          let some (cbo, ga') := gb.getSe | return none
          let some (cro, gb'') := ga'.getSe | return none
          cbQpList := cbQpList.set! i cbo
          crQpList := crQpList.set! i cro
          gb := gb''
      let some (_, ga') := gb.getUe | return none
      let some (_, gb'') := ga'.getUe | return none
      gb := gb''
    if mlExt == 1 || d3Ext == 1 || sccExt == 1 then return none
  let pps0 : HevcPps := { ({} : HevcPps) with
    ppsId := ppsId
    spsId := spsId
    dependentSliceSegmentsEnabledFlag := depFlag == 1
    outputFlagPresentFlag := outFlag == 1
    numExtraSliceHeaderBits := extraBits
    signDataHidingFlag := sdh == 1
    cabacInitPresentFlag := cabacInit == 1
    numRefIdxL0DefaultActive := nr0 + 1
    numRefIdxL1DefaultActive := nr1 + 1
    picInitQpMinus26 := picQp
    constrainedIntraPredFlag := cip == 1
    transformSkipEnabledFlag := tskip == 1
    log2MaxTransformSkipBlockSize := log2MaxTskip
    cuQpDeltaEnabledFlag := cuQpEn == 1
    diffCuQpDeltaDepth := diffCuQp
    cbQpOffset := cbOff
    crQpOffset := crOff
    picSliceLevelChromaQpOffsetsPresentFlag := slChroma == 1
    weightedPredFlag := wpFlag == 1
    weightedBipredFlag := wbFlag == 1
    transquantBypassEnableFlag := tqbFlag == 1
    tilesEnabledFlag := tilesFlag == 1
    entropyCodingSyncEnabledFlag := wppFlag == 1
    numTileColumns := numCols
    numTileRows := numRows
    uniformSpacingFlag := uniform
    columnWidth := colW
    rowHeight := rowH
    loopFilterAcrossTilesEnabledFlag := lfAcrossTiles
    seqLoopFilterAcrossSlicesEnabledFlag := lfSlices == 1
    deblockingFilterControlPresentFlag := dbfCtrl == 1
    deblockingFilterOverrideEnabledFlag := dbfOverride
    disableDbf := disableDbf
    betaOffset := betaOff
    tcOffset := tcOff
    scalingListDataPresentFlag := slData == 1
    scalingList := scalingList
    listsModificationPresentFlag := lmFlag == 1
    log2ParallelMergeLevel := lpm + 2
    sliceHeaderExtensionPresentFlag := sheFlag == 1
    chromaQpOffsetEnabled := chromaQpOffsetEnabled
    diffCuChromaQpOffsetDepth := diffCuChromaQpDepth
    chromaQpOffsetListLenMinus1 := chromaQpListLenM1
    cbQpOffsetList := cbQpList
    crQpOffsetList := crQpList
  }
  buildPpsDerivations sps pps0

structure HevcPredWeight where
  lumaLog2WeightDenom   : Nat
  chromaLog2WeightDenom : Nat
  lumaWeightL0          : Array Int
  lumaOffsetL0          : Array Int
  chromaWeightL0        : Array (Array Int)
  chromaOffsetL0        : Array (Array Int)
  lumaWeightL1          : Array Int
  lumaOffsetL1          : Array Int
  chromaWeightL1        : Array (Array Int)
  chromaOffsetL1        : Array (Array Int)
  weightedLuma          : Bool
  weightedChroma        : Bool
  deriving Repr, DecidableEq, Inhabited

@[inline]
def asrInt (x : Int) (sh : Nat) : Int :=
  if sh == 0 then x
  else if x >= 0 then Int.ofNat (x.toNat >>> sh)
  else -(Int.ofNat (((-x - 1).toNat >>> sh) + 1))

private def parseWeightList (gb0 : HevcBitReader) (sps : HevcSps) (nb lumaDenom chromaDenom : Nat) :
    Option (HevcBitReader × Array Int × Array Int × Array (Array Int) × Array (Array Int) × Bool × Bool) :=
  Id.run do
    let mut gb := gb0
    let mut lumaFlag : Array Nat := Array.mkEmpty nb
    for _ in [:nb] do
      let some (f, gn) := gb.getBit | return none
      lumaFlag := lumaFlag.push f
      gb := gn
    let mut chromaFlag : Array Nat := Array.replicate nb 0
    if sps.chromaFormatIdc != 0 then
      for i in [:nb] do
        let some (f, gn) := gb.getBit | return none
        chromaFlag := chromaFlag.set! i f
        gb := gn
    let baseL := Int.ofNat (1 <<< lumaDenom)
    let baseC := Int.ofNat (1 <<< chromaDenom)
    let mut lw := Array.replicate nb baseL
    let mut lo := Array.replicate nb (0 : Int)
    let mut cw := Array.replicate nb #[baseC, baseC]
    let mut co := Array.replicate nb #[(0 : Int), 0]
    for i in [:nb] do
      if lumaFlag.getD i 0 == 1 then
        let some (dw, ga) := gb.getSe | return none
        let some (doff, gb') := ga.getSe | return none
        lw := lw.set! i (baseL + dw)
        lo := lo.set! i doff
        gb := gb'
      if chromaFlag.getD i 0 == 1 then
        let mut cwRow := cw.getD i #[baseC, baseC]
        let mut coRow := co.getD i #[0, 0]
        for j in [:2] do
          let some (dw, ga) := gb.getSe | return none
          let some (doff, gb') := ga.getSe | return none
          let cwj := baseC + dw
          let pred : Int := 128 - asrInt (128 * cwj) chromaDenom
          coRow := coRow.set! j (clipInt (pred + doff) (-128) 127)
          cwRow := cwRow.set! j cwj
          gb := gb'
        cw := cw.set! i cwRow
        co := co.set! i coRow
    let hasL := lumaFlag.any (· == 1)
    let hasC := chromaFlag.any (· == 1)
    return some (gb, lw, lo, cw, co, hasL, hasC)

def parsePredWeightTable (gb0 : HevcBitReader) (sps : HevcSps) (sliceType nbRefsL0 nbRefsL1 : Nat) :
    Option (HevcPredWeight × HevcBitReader) := Id.run do
  let some (lumaDenom, g1) := gb0.getUe | return none
  if lumaDenom > 7 then return none
  let mut chromaDenom := 0
  let mut gb := g1
  if sps.chromaFormatIdc != 0 then
    let some (delta, g2) := gb.getSe | return none
    chromaDenom := (clipInt (Int.ofNat lumaDenom + delta) 0 7).toNat
    gb := g2
  let some (gb', lw0, lo0, cw0, co0, hasL0Y, hasL0C) :=
    parseWeightList gb sps nbRefsL0 lumaDenom chromaDenom | return none
  gb := gb'
  let mut lw1 : Array Int := #[]
  let mut lo1 : Array Int := #[]
  let mut cw1 : Array (Array Int) := #[]
  let mut co1 : Array (Array Int) := #[]
  let mut hasL1Y := false
  let mut hasL1C := false
  if sliceType == sliceB then
    let some (gb'', a, b, c, d, e, f) :=
      parseWeightList gb sps nbRefsL1 lumaDenom chromaDenom | return none
    gb := gb''
    lw1 := a
    lo1 := b
    cw1 := c
    co1 := d
    hasL1Y := e
    hasL1C := f
  return some ({
    lumaLog2WeightDenom := lumaDenom
    chromaLog2WeightDenom := chromaDenom
    lumaWeightL0 := lw0
    lumaOffsetL0 := lo0
    chromaWeightL0 := cw0
    chromaOffsetL0 := co0
    lumaWeightL1 := lw1
    lumaOffsetL1 := lo1
    chromaWeightL1 := cw1
    chromaOffsetL1 := co1
    weightedLuma := hasL0Y || hasL1Y
    weightedChroma := hasL0C || hasL1C
  }, gb)

structure HevcLtRps where
  poc           : Array Int
  used          : Array Nat
  pocMsbPresent : Array Nat
  deriving Repr, DecidableEq, Inhabited

def emptyLtRps : HevcLtRps := { poc := #[], used := #[], pocMsbPresent := #[] }

@[inline]
def isIrap (nalType : Nat) : Bool :=
  16 <= nalType && nalType <= 23

@[inline]
def isIdr (nalType : Nat) : Bool :=
  nalType == nalIdrWRadl || nalType == nalIdrNLp

@[inline]
def isBla (nalType : Nat) : Bool :=
  nalType == nalBlaWLp || nalType == nalBlaWRadl || nalType == nalBlaNLp

@[inline]
def isSlnr (nalType : Nat) : Bool :=
  nalType == nalTrailN || nalType == nalTsaN || nalType == nalStsaN ||
    nalType == nalRadlN || nalType == nalRaslN

structure HevcSliceHeader where
  nalType                                 : Nat := 0
  tid                                     : Nat := 0
  ppsId                                   : Nat := 0
  spsId                                   : Nat := 0
  firstSliceInPicFlag                     : Bool := true
  noOutputOfPriorPicsFlag                 : Bool := false
  dependentSliceSegmentFlag               : Bool := false
  sliceSegmentAddr                        : Nat := 0
  sliceCtbAddrRs                          : Nat := 0
  sliceAddrRs                             : Nat := 0
  sliceType                               : Nat := sliceI
  picOutputFlag                           : Bool := true
  pocLsb                                  : Nat := 0
  poc                                     : Int := 0
  shortTermRps                            : HevcShortTermRps := {}
  ltRps                                   : HevcLtRps := emptyLtRps
  sliceTemporalMvpEnabledFlag             : Bool := false
  saoLumaFlag                             : Bool := false
  saoChromaFlag                           : Bool := false
  nbRefs                                  : Array Nat := #[0, 0]
  rplModFlag                              : Array Nat := #[0, 0]
  listEntryLx                             : Array (Array Nat) := #[#[], #[]]
  mvdL1ZeroFlag                           : Bool := false
  cabacInitFlag                           : Bool := false
  collocatedList                          : Nat := 0
  collocatedRefIdx                        : Nat := 0
  pwt?                                    : Option HevcPredWeight := none
  maxNumMergeCand                         : Nat := 5
  sliceQp                                 : Int := 26
  cbQpOffset                              : Int := 0
  crQpOffset                              : Int := 0
  cuChromaQpOffsetEnabledFlag             : Bool := false
  disableDeblockingFilterFlag             : Bool := false
  betaOffset                              : Int := 0
  tcOffset                                : Int := 0
  sliceLoopFilterAcrossSlicesEnabledFlag  : Bool := true
  numEntryPointOffsets                    : Nat := 0
  entryPointOffsets                       : Array Nat := #[]
  substreams                              : Array ByteArray := #[]
  deriving Inhabited

def nbRefsTotalCurr (st : HevcShortTermRps) (lt : HevcLtRps) : Nat :=
  let c1 := st.used.foldl (fun acc u => if u == 1 then acc + 1 else acc) 0
  lt.used.foldl (fun acc u => if u == 1 then acc + 1 else acc) c1

def computePoc (sps : HevcSps) (pocTid0 : Int) (pocLsb nalType : Nat) : Int :=
  let maxPocLsb := Int.ofNat (1 <<< sps.log2MaxPocLsb)
  let half := maxPocLsb / 2
  let prevLsbRaw := pocTid0 % maxPocLsb
  let prevLsb := if prevLsbRaw < 0 then prevLsbRaw + maxPocLsb else prevLsbRaw
  let prevMsb := pocTid0 - prevLsb
  let lsb := Int.ofNat pocLsb
  let msb :=
    if lsb < prevLsb && (prevLsb - lsb) >= half then prevMsb + maxPocLsb
    else if lsb > prevLsb && (lsb - prevLsb) > half then prevMsb - maxPocLsb
    else prevMsb
  if isBla nalType then lsb else msb + lsb

def parseSliceHeader (ebspPayload : ByteArray) (nalType tid : Nat)
    (spsMap : Array (Option HevcSps)) (ppsMap : Array (Option HevcPps))
    (prevIndepSh? : Option HevcSliceHeader) (pocTid0 : Int) : Option HevcSliceHeader := Id.run do
  let some rm := stripRbspWithMap ebspPayload | return none
  let rbsp := rm.rbsp
  let rbspToEbsp := rm.map
  let mut gb := HevcBitReader.ofBytes rbsp
  let some (firstSlice, g1) := gb.getBit | return none
  gb := g1
  let mut noOutPrior := 0
  if isIrap nalType then
    let some (nop, g2) := gb.getBit | return none
    noOutPrior := nop
    gb := g2
  let some (ppsId, g2) := gb.getUe | return none
  gb := g2
  if ppsId >= ppsMap.size then return none
  let some pps := ppsMap[ppsId]! | return none
  if pps.spsId >= spsMap.size then return none
  let some sps := spsMap[pps.spsId]! | return none
  let mut depFlag := 0
  let mut sliceSegAddr := 0
  if firstSlice == 0 then
    if pps.dependentSliceSegmentsEnabledFlag then
      let some (df, gn) := gb.getBit | return none
      depFlag := df
      gb := gn
    let addrBits := ceilLog2Nat sps.ctbSize
    let some (addr, gn) := gb.getBits addrBits | return none
    if addr >= sps.ctbSize then return none
    sliceSegAddr := addr
    gb := gn
  let mut sh : HevcSliceHeader := {}
  if depFlag == 0 then
    for _ in [:pps.numExtraSliceHeaderBits] do
      let some (_, gn) := gb.getBit | return none
      gb := gn
    let some (st, gn) := gb.getUe | return none
    gb := gn
    if st != sliceB && st != sliceP && st != sliceI then return none
    if isIrap nalType && st != sliceI then return none
    let mut picOut := 1
    if pps.outputFlagPresentFlag then
      let some (po, gn') := gb.getBit | return none
      picOut := po
      gb := gn'
    let mut pocLsb := 0
    let mut stRps : HevcShortTermRps := {}
    let mut ltPoc : Array Int := #[]
    let mut ltUsed : Array Nat := #[]
    let mut ltMsbPres : Array Nat := #[]
    let mut tmvpFlag := 0
    if !isIdr nalType then
      let some (pl, ga) := gb.getBits sps.log2MaxPocLsb | return none
      let some (stSpsFlag, gb') := ga.getBit | return none
      pocLsb := pl
      gb := gb'
      if stSpsFlag == 0 then
        let some (parsedSt, gc) := parseShortTermRps gb sps.stRps sps.nbStRps true | return none
        stRps := parsedSt
        gb := gc
      else if sps.nbStRps > 1 then
        let idxBits := ceilLog2Nat sps.nbStRps
        let some (stIdx, gc) := gb.getBits idxBits | return none
        if stIdx >= sps.stRps.size then return none
        stRps := sps.stRps[stIdx]!
        gb := gc
      else if sps.nbStRps == 1 then
        if sps.stRps.isEmpty then return none
        stRps := sps.stRps[0]!
      else
        stRps := {}
      if sps.ltPresent then
        let mut nbSps := 0
        if sps.ltPocLsb.size > 0 then
          let some (ns, gc) := gb.getUe | return none
          nbSps := ns
          gb := gc
        let some (nbSh, gd) := gb.getUe | return none
        gb := gd
        let nbLt := nbSps + nbSh
        if nbLt > 32 then return none
        let mut prevDeltaMsb := 0
        for i in [:nbLt] do
          let mut lsb := 0
          let mut usedF := 0
          if i < nbSps then
            let mut ltIdx := 0
            if sps.ltPocLsb.size > 1 then
              let some (li, ge) := gb.getBits (ceilLog2Nat sps.ltPocLsb.size) | return none
              ltIdx := li
              gb := ge
            if ltIdx >= sps.ltPocLsb.size then return none
            lsb := sps.ltPocLsb[ltIdx]!
            usedF := sps.ltUsed.getD ltIdx 0
          else
            let some (ls, ge) := gb.getBits sps.log2MaxPocLsb | return none
            let some (uf, gf) := ge.getBit | return none
            lsb := ls
            usedF := uf
            gb := gf
          let some (dmsbP, gg) := gb.getBit | return none
          gb := gg
          let mut ltVal : Int := Int.ofNat lsb
          if dmsbP == 1 then
            let some (dRaw, gh) := gb.getUe | return none
            gb := gh
            let delta := if i != 0 && i != nbSps then dRaw + prevDeltaMsb else dRaw
            prevDeltaMsb := delta
            ltVal := Int.ofNat lsb - Int.ofNat (delta <<< sps.log2MaxPocLsb)
          ltPoc := ltPoc.push ltVal
          ltUsed := ltUsed.push usedF
          ltMsbPres := ltMsbPres.push dmsbP
      if sps.spsTemporalMvpEnabledFlag then
        let some (tm, gc) := gb.getBit | return none
        tmvpFlag := tm
        gb := gc
    let poc : Int := if isIdr nalType then 0 else computePoc sps pocTid0 pocLsb nalType
    let lsbMask : Int := Int.ofNat ((1 <<< sps.log2MaxPocLsb) - 1)
    let pocLsbMod : Int := ((poc % (lsbMask + 1)) + (lsbMask + 1)) % (lsbMask + 1)
    let pocMsbPart : Int := poc - pocLsbMod
    for idxLt in [:ltPoc.size] do
      if ltMsbPres.getD idxLt 0 == 1 then
        ltPoc := ltPoc.set! idxLt (ltPoc[idxLt]! + pocMsbPart)
    let ltRps : HevcLtRps := { poc := ltPoc, used := ltUsed, pocMsbPresent := ltMsbPres }
    let mut saoY := 0
    let mut saoC := 0
    if sps.saoEnabled then
      let some (sy, ga) := gb.getBit | return none
      saoY := sy
      gb := ga
      if sps.chromaFormatIdc != 0 then
        let some (sc, gb') := gb.getBit | return none
        saoC := sc
        gb := gb'
    let mut nbRefs : Array Nat := #[0, 0]
    let mut rplMod : Array Nat := #[0, 0]
    let mut listEntry : Array (Array Nat) := #[#[], #[]]
    let mut mvdL1Zero := 0
    let mut cabacInit := 0
    let mut collList := 0
    let mut collRefIdx := 0
    let mut pwt? : Option HevcPredWeight := none
    let mut maxMerge := 5
    if st == sliceP || st == sliceB then
      nbRefs := nbRefs.set! 0 pps.numRefIdxL0DefaultActive
      if st == sliceB then
        nbRefs := nbRefs.set! 1 pps.numRefIdxL1DefaultActive
      let some (ov, ga) := gb.getBit | return none
      gb := ga
      if ov == 1 then
        let some (n0, gb') := gb.getUe | return none
        nbRefs := nbRefs.set! 0 (n0 + 1)
        gb := gb'
        if st == sliceB then
          let some (n1, gc) := gb.getUe | return none
          nbRefs := nbRefs.set! 1 (n1 + 1)
          gb := gc
      if nbRefs[0]! > 16 || nbRefs[1]! > 16 then return none
      let nbRpsCurr := nbRefsTotalCurr stRps ltRps
      if pps.listsModificationPresentFlag && nbRpsCurr > 1 then
        let entryBits := ceilLog2Nat nbRpsCurr
        let some (rm0, gb') := gb.getBit | return none
        rplMod := rplMod.set! 0 rm0
        gb := gb'
        if rm0 == 1 then
          let mut le0 : Array Nat := Array.mkEmpty (nbRefs[0]!)
          for _ in [:nbRefs[0]!] do
            let some (e, gc) := gb.getBits entryBits | return none
            if e >= nbRpsCurr then return none
            le0 := le0.push e
            gb := gc
          listEntry := listEntry.set! 0 le0
        if st == sliceB then
          let some (rm1, gb'') := gb.getBit | return none
          rplMod := rplMod.set! 1 rm1
          gb := gb''
          if rm1 == 1 then
            let mut le1 : Array Nat := Array.mkEmpty (nbRefs[1]!)
            for _ in [:nbRefs[1]!] do
              let some (e, gc) := gb.getBits entryBits | return none
              if e >= nbRpsCurr then return none
              le1 := le1.push e
              gb := gc
            listEntry := listEntry.set! 1 le1
      if st == sliceB then
        let some (mz, gb') := gb.getBit | return none
        mvdL1Zero := mz
        gb := gb'
      if pps.cabacInitPresentFlag then
        let some (ci, gb') := gb.getBit | return none
        cabacInit := ci
        gb := gb'
      if tmvpFlag == 1 then
        let mut collFromL0 := 1
        if st == sliceB then
          let some (cf, gb') := gb.getBit | return none
          collFromL0 := cf
          gb := gb'
        collList := if collFromL0 == 1 then 0 else 1
        if nbRefs[collList]! > 1 then
          let some (cri, gb') := gb.getUe | return none
          if cri >= nbRefs[collList]! then return none
          collRefIdx := cri
          gb := gb'
      if (pps.weightedPredFlag && st == sliceP) || (pps.weightedBipredFlag && st == sliceB) then
        let some (pw, gb') := parsePredWeightTable gb sps st (nbRefs[0]!) (nbRefs[1]!) | return none
        pwt? := some pw
        gb := gb'
      let some (fmm, gb') := gb.getUe | return none
      if fmm > 4 then return none
      maxMerge := 5 - fmm
      gb := gb'
    let some (qpDelta, ga) := gb.getSe | return none
    gb := ga
    let sliceQp := 26 + pps.picInitQpMinus26 + qpDelta
    if sliceQp < 0 || sliceQp > 51 then return none
    let mut cbOff : Int := 0
    let mut crOff : Int := 0
    if pps.picSliceLevelChromaQpOffsetsPresentFlag then
      let some (cbo, gb') := gb.getSe | return none
      let some (cro, gc) := gb'.getSe | return none
      cbOff := cbo
      crOff := cro
      gb := gc
    let mut cuChromaQpEn := false
    if pps.chromaQpOffsetEnabled then
      let some (ce, gb') := gb.getBit | return none
      cuChromaQpEn := ce == 1
      gb := gb'
    let mut disDbf := pps.disableDbf
    let mut betaOff := pps.betaOffset
    let mut tcOff := pps.tcOffset
    if pps.deblockingFilterControlPresentFlag then
      let mut dbfOv := 0
      if pps.deblockingFilterOverrideEnabledFlag then
        let some (ov, gb') := gb.getBit | return none
        dbfOv := ov
        gb := gb'
      if dbfOv == 1 then
        let some (dd, gb') := gb.getBit | return none
        disDbf := dd == 1
        gb := gb'
        if dd == 0 then
          let some (bo, gc) := gb.getSe | return none
          let some (to, gd) := gc.getSe | return none
          betaOff := bo * 2
          tcOff := to * 2
          gb := gd
    let mut sliceLfSlices := pps.seqLoopFilterAcrossSlicesEnabledFlag
    if pps.seqLoopFilterAcrossSlicesEnabledFlag && (saoY == 1 || saoC == 1 || !disDbf) then
      let some (lf, gb') := gb.getBit | return none
      sliceLfSlices := lf == 1
      gb := gb'
    sh := {
      nalType := nalType
      tid := tid
      ppsId := ppsId
      spsId := pps.spsId
      firstSliceInPicFlag := firstSlice == 1
      noOutputOfPriorPicsFlag := noOutPrior == 1
      dependentSliceSegmentFlag := false
      sliceSegmentAddr := sliceSegAddr
      sliceCtbAddrRs := sliceSegAddr
      sliceAddrRs := sliceSegAddr
      sliceType := st
      picOutputFlag := picOut == 1
      pocLsb := pocLsb
      poc := poc
      shortTermRps := stRps
      ltRps := ltRps
      sliceTemporalMvpEnabledFlag := tmvpFlag == 1
      saoLumaFlag := saoY == 1
      saoChromaFlag := saoC == 1
      nbRefs := nbRefs
      rplModFlag := rplMod
      listEntryLx := listEntry
      mvdL1ZeroFlag := mvdL1Zero == 1
      cabacInitFlag := cabacInit == 1
      collocatedList := collList
      collocatedRefIdx := collRefIdx
      pwt? := pwt?
      maxNumMergeCand := maxMerge
      sliceQp := sliceQp
      cbQpOffset := cbOff
      crQpOffset := crOff
      cuChromaQpOffsetEnabledFlag := cuChromaQpEn
      disableDeblockingFilterFlag := disDbf
      betaOffset := betaOff
      tcOffset := tcOff
      sliceLoopFilterAcrossSlicesEnabledFlag := sliceLfSlices
    }
  else
    let some prev := prevIndepSh? | return none
    sh := { prev with
      firstSliceInPicFlag := false
      dependentSliceSegmentFlag := true
      sliceSegmentAddr := sliceSegAddr
      sliceCtbAddrRs := sliceSegAddr
    }
  let mut numEpo := 0
  let mut epos : Array Nat := #[]
  if pps.tilesEnabledFlag || pps.entropyCodingSyncEnabledFlag then
    let some (ne, ga) := gb.getUe | return none
    numEpo := ne
    gb := ga
    if numEpo > sps.ctbSize then return none
    if numEpo > 0 then
      let some (olM1, gb') := gb.getUe | return none
      let offLen := olM1 + 1
      if offLen > 32 then return none
      gb := gb'
      for _ in [:numEpo] do
        let some (epoM1, gc) := gb.getBits offLen | return none
        epos := epos.push (epoM1 + 1)
        gb := gc
  if pps.sliceHeaderExtensionPresentFlag then
    let some (extLen, ga) := gb.getUe | return none
    let some gb' := ga.skipBits (extLen * 8) | return none
    gb := gb'
  let some (alignBit, ga) := gb.getBit | return none
  if alignBit != 1 then return none
  gb := ga.alignByte
  let rbspDataByteOff := gb.pos >>> 3
  if rbspDataByteOff >= rbspToEbsp.size then return none
  let mut curEbsp := rbspToEbsp[rbspDataByteOff]!
  let mut substreams : Array ByteArray := Array.mkEmpty (epos.size + 1)
  for epo in epos do
    if curEbsp + epo > ebspPayload.size then return none
    let some subRm := stripRbspWithMap (ebspPayload.extract curEbsp (curEbsp + epo)) | return none
    substreams := substreams.push subRm.rbsp
    curEbsp := curEbsp + epo
  let some lastRm := stripRbspWithMap (ebspPayload.extract curEbsp ebspPayload.size) | return none
  substreams := substreams.push lastRm.rbsp
  return some { sh with
    numEntryPointOffsets := numEpo
    entryPointOffsets := epos
    substreams := substreams
  }

def writeProfileTierLevel (w : HevcBitWriter) : HevcBitWriter :=
  let cur0 := (((w.putBits 0 2).putBit 0).putBits 1 5).putBits 0x40000000 32
  let cur1 := ((((cur0.putBit 1).putBit 0).putBit 1).putBit 1).putBits 0 44
  cur1.putBits 93 8

def writeVps : Option ByteArray := Id.run do
  let mut w := HevcBitWriter.empty
  w := (w.putBits 0 4).putBits 3 2
  w := (w.putBits 0 6).putBits 0 3
  w := (w.putBit 1).putBits 0xFFFF 16
  w := writeProfileTierLevel w
  w := w.putBit 1
  w := ((w.putUe 1).putUe 0).putUe 0
  w := (w.putBits 0 6).putUe 0
  w := (w.putBit 0).putBit 0
  let some body := w.rbspTrailingBits.toBytes | return none
  return some (packHevcNal nalVps 0 1 body)

def writeSps (width height log2Ctb : Nat) (conf : Nat × Nat × Nat × Nat) : Option ByteArray := Id.run do
  let mut w := HevcBitWriter.empty
  w := (w.putBits 0 4).putBits 0 3
  w := w.putBit 1
  w := writeProfileTierLevel w
  w := w.putUe 0
  w := w.putUe 1
  w := (w.putUe width).putUe height
  if conf.1 != 0 || conf.2.1 != 0 || conf.2.2.1 != 0 || conf.2.2.2 != 0 then
    w := w.putBit 1
    w := (w.putUe (conf.1 >>> 1)).putUe (conf.2.1 >>> 1)
    w := (w.putUe (conf.2.2.1 >>> 1)).putUe (conf.2.2.2 >>> 1)
  else
    w := w.putBit 0
  w := (w.putUe 0).putUe 0
  w := w.putUe 4
  w := w.putBit 1
  w := ((w.putUe 1).putUe 0).putUe 0
  w := w.putUe 0
  w := w.putUe (log2Ctb - 3)
  w := w.putUe 0
  w := w.putUe (Nat.min log2Ctb 5 - 2)
  w := (w.putUe 1).putUe 1
  w := (w.putBit 0).putBit 0
  w := w.putBit 1
  w := w.putBit 0
  w := w.putUe 1
  w := (w.putUe 1).putUe 0
  w := (w.putUe 0).putBit 1
  w := w.putBit 0
  w := (w.putBit 1).putBit 1
  w := (w.putBit 0).putBit 0
  let some body := w.rbspTrailingBits.toBytes | return none
  return some (packHevcNal nalSps 0 1 body)

def writePps (numTileColumns numTileRows ctbW ctbH : Nat) : Option ByteArray := Id.run do
  let mut w := HevcBitWriter.empty
  w := (w.putUe 0).putUe 0
  w := (w.putBit 0).putBit 0
  w := w.putBits 0 3
  w := (w.putBit 0).putBit 0
  w := (w.putUe 0).putUe 0
  w := w.putSe 0
  w := (w.putBit 0).putBit 0
  w := w.putBit 0
  w := (w.putSe 0).putSe 0
  w := (w.putBit 0).putBit 0
  w := (w.putBit 0).putBit 0
  let tiles := numTileColumns > 1 || numTileRows > 1
  w := w.putBit (if tiles then 1 else 0)
  w := w.putBit 0
  if tiles then
    w := (w.putUe (numTileColumns - 1)).putUe (numTileRows - 1)
    w := w.putBit 0
    for i in [:numTileColumns - 1] do
      w := w.putUe ((((i + 1) * ctbW) / numTileColumns) - ((i * ctbW) / numTileColumns) - 1)
    for i in [:numTileRows - 1] do
      w := w.putUe ((((i + 1) * ctbH) / numTileRows) - ((i * ctbH) / numTileRows) - 1)
    w := w.putBit 1
  w := w.putBit 1
  w := w.putBit 0
  w := w.putBit 0
  w := w.putBit 0
  w := w.putUe 0
  w := (w.putBit 0).putBit 0
  let some body := w.rbspTrailingBits.toBytes | return none
  return some (packHevcNal nalPps 0 1 body)

def sliceHeaderBits (nalType sliceType pocLsb : Nat) (saoY saoC : Bool)
    (entryLens : Array Nat) (qp : Int) : Option ByteArray := Id.run do
  let mut w := HevcBitWriter.empty
  w := w.putBit 1
  if nalType == nalIdrWRadl then
    w := w.putBit 0
  w := (w.putUe 0).putUe sliceType
  if nalType != nalIdrWRadl then
    w := w.putBits (pocLsb &&& 0xFF) 8
    w := w.putBit 1
    w := w.putBit 1
  w := w.putBit (if saoY then 1 else 0)
  w := w.putBit (if saoC then 1 else 0)
  if sliceType == sliceP then
    w := w.putBit 0
    w := w.putUe 0
  w := w.putSe (qp - 26)
  w := w.putBit 1
  if entryLens.size > 0 then
    w := w.putUe entryLens.size
    let mut maxLen := 1
    for ln in entryLens do
      if ln > maxLen then maxLen := ln
    let offLen := Nat.max (ceilLog2Nat maxLen) 1
    w := w.putUe (offLen - 1)
    for ln in entryLens do
      w := w.putBits (ln - 1) offLen
  w := w.putBit 1
  let some body := w.alignZero.toBytes | return none
  return some body

def buildHvccRecord (vps sps pps : ByteArray) : ByteArray :=
  let arrayBody (nalType : Nat) (nal : ByteArray) : ByteArray :=
    let b0 : UInt8 := (0x80 ||| nalType).toUInt8
    let body := (((ByteArray.empty.push b0).push 0).push 1).push ((nal.size >>> 8).toUInt8)
    ByteArray.append (body.push ((nal.size &&& 0xFF).toUInt8)) nal
  let header : ByteArray := ByteArray.mk #[
    1, 0x01, 0x60, 0x00, 0x00, 0x00, 0x90, 0x00, 0x00, 0x00, 0x00, 0x00,
    93, 0xF0, 0x00, 0xFC, 0xFD, 0xF8, 0xF8, 0x00, 0x00, 0x0F, 3
  ]
  let body := ByteArray.append (arrayBody 32 vps) (ByteArray.append (arrayBody 33 sps) (arrayBody 34 pps))
  ByteArray.append header body

def be32 (v : Nat) : ByteArray :=
  ByteArray.mk #[(v >>> 24).toUInt8, ((v >>> 16) &&& 0xFF).toUInt8,
    ((v >>> 8) &&& 0xFF).toUInt8, (v &&& 0xFF).toUInt8]

def be16 (v : Nat) : ByteArray :=
  ByteArray.mk #[((v >>> 8) &&& 0xFF).toUInt8, (v &&& 0xFF).toUInt8]

def mp4Box (tag : ByteArray) (body : ByteArray) : ByteArray :=
  ByteArray.append (be32 (8 + body.size)) (ByteArray.append tag body)

def mp4FullBox (tag : ByteArray) (ver : UInt8) (body : ByteArray) : ByteArray :=
  let head := ByteArray.mk #[ver, 0, 0, 0]
  mp4Box tag (ByteArray.append head body)

def zerosU8 (n : Nat) : ByteArray :=
  ByteArray.mk (Array.replicate n 0)

def buildHevcMp4 (samples : Array ByteArray) (dispW dispH : Nat) (hvcc : ByteArray) : ByteArray := Id.run do
  let ftyp := mp4Box (ByteArray.mk #[0x66, 0x74, 0x79, 0x70])
    (ByteArray.append (ByteArray.mk #[0x69, 0x73, 0x6F, 0x6D])
      (ByteArray.append (be32 0) (ByteArray.mk #[0x69, 0x73, 0x6F, 0x6D, 0x69, 0x73, 0x6F, 0x32,
        0x68, 0x76, 0x63, 0x31, 0x6D, 0x70, 0x34, 0x31])))
  let mut mdatBody : ByteArray := ByteArray.empty
  let mut sizes : Array Nat := Array.mkEmpty samples.size
  let mut offsets : Array Nat := Array.mkEmpty samples.size
  let base := ftyp.size + 8
  for s in samples do
    offsets := offsets.push (base + mdatBody.size)
    mdatBody := ByteArray.append mdatBody s
    sizes := sizes.push s.size
  let mdat := mp4Box (ByteArray.mk #[0x6D, 0x64, 0x61, 0x74]) mdatBody
  let n := samples.size
  let cfg := mp4Box (ByteArray.mk #[0x68, 0x76, 0x63, 0x43]) hvcc
  let mut vse : ByteArray := ByteArray.append (zerosU8 6) (ByteArray.mk #[0, 1])
  vse := ByteArray.append vse (zerosU8 16)
  vse := ByteArray.append vse (be16 dispW)
  vse := ByteArray.append vse (be16 dispH)
  vse := ByteArray.append vse (ByteArray.mk #[0, 0x48, 0, 0, 0, 0x48, 0, 0, 0, 0, 0, 0, 0, 1])
  vse := ByteArray.append vse (zerosU8 32)
  vse := ByteArray.append vse (ByteArray.mk #[0, 0x18, 0xFF, 0xFF])
  vse := ByteArray.append vse cfg
  let stsd := mp4FullBox (ByteArray.mk #[0x73, 0x74, 0x73, 0x64]) 0
    (ByteArray.append (be32 1) (mp4Box (ByteArray.mk #[0x68, 0x76, 0x63, 0x31]) vse))
  let mut sizeBytes : ByteArray := ByteArray.empty
  for s in sizes do
    sizeBytes := ByteArray.append sizeBytes (be32 s)
  let stsz := mp4FullBox (ByteArray.mk #[0x73, 0x74, 0x73, 0x7A]) 0
    (ByteArray.append (be32 0) (ByteArray.append (be32 n) sizeBytes))
  let stsc := mp4FullBox (ByteArray.mk #[0x73, 0x74, 0x73, 0x63]) 0
    (ByteArray.append (be32 1) (ByteArray.append (be32 1) (ByteArray.append (be32 1) (be32 1))))
  let mut offBytes : ByteArray := ByteArray.empty
  for o in offsets do
    offBytes := ByteArray.append offBytes (be32 o)
  let stco := mp4FullBox (ByteArray.mk #[0x73, 0x74, 0x63, 0x6F]) 0
    (ByteArray.append (be32 n) offBytes)
  let stts := mp4FullBox (ByteArray.mk #[0x73, 0x74, 0x74, 0x73]) 0
    (ByteArray.append (be32 1) (ByteArray.append (be32 n) (be32 1000)))
  let stss := mp4FullBox (ByteArray.mk #[0x73, 0x74, 0x73, 0x73]) 0
    (ByteArray.append (be32 1) (be32 1))
  let stbl := mp4Box (ByteArray.mk #[0x73, 0x74, 0x62, 0x6C])
    (ByteArray.append stsd (ByteArray.append stts (ByteArray.append stss
      (ByteArray.append stsc (ByteArray.append stsz stco)))))
  let dref := mp4FullBox (ByteArray.mk #[0x64, 0x72, 0x65, 0x66]) 0
    (ByteArray.append (be32 1) (mp4FullBox (ByteArray.mk #[0x75, 0x72, 0x6C, 0x20]) 1 ByteArray.empty))
  let dinf := mp4Box (ByteArray.mk #[0x64, 0x69, 0x6E, 0x66]) dref
  let vmhd := mp4FullBox (ByteArray.mk #[0x76, 0x6D, 0x68, 0x64]) 0
    (ByteArray.mk #[0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])
  let minf := mp4Box (ByteArray.mk #[0x6D, 0x69, 0x6E, 0x66])
    (ByteArray.append vmhd (ByteArray.append dinf stbl))
  let mdhd := mp4FullBox (ByteArray.mk #[0x6D, 0x64, 0x68, 0x64]) 0
    (ByteArray.append (be32 0) (ByteArray.append (be32 0) (ByteArray.append (be32 25000)
      (ByteArray.append (be32 (n * 1000)) (ByteArray.mk #[0x55, 0xC4, 0, 0])))))
  let hdlr := mp4FullBox (ByteArray.mk #[0x68, 0x64, 0x6C, 0x72]) 0
    (ByteArray.append (be32 0) (ByteArray.append (ByteArray.mk #[0x76, 0x69, 0x64, 0x65])
      (ByteArray.append (zerosU8 12)
        (ByteArray.mk #[0x56, 0x69, 0x64, 0x65, 0x6F, 0x48, 0x61, 0x6E, 0x64, 0x6C, 0x65, 0x72, 0]))))
  let mdia := mp4Box (ByteArray.mk #[0x6D, 0x64, 0x69, 0x61])
    (ByteArray.append mdhd (ByteArray.append hdlr minf))
  let tkhdHead := ByteArray.mk #[0, 0, 0, 3]
  let matrix : ByteArray :=
    ByteArray.append (be32 0x00010000) (ByteArray.append (be32 0) (ByteArray.append (be32 0)
      (ByteArray.append (be32 0) (ByteArray.append (be32 0x00010000) (ByteArray.append (be32 0)
        (ByteArray.append (be32 0) (ByteArray.append (be32 0) (be32 0x40000000))))))))
  let tkhd := mp4Box (ByteArray.mk #[0x74, 0x6B, 0x68, 0x64])
    (ByteArray.append tkhdHead (ByteArray.append (be32 0) (ByteArray.append (be32 0)
      (ByteArray.append (be32 1) (ByteArray.append (be32 0) (ByteArray.append (be32 (n * 1000))
        (ByteArray.append (be32 0) (ByteArray.append (be32 0) (ByteArray.append (be16 0)
          (ByteArray.append (be16 0) (ByteArray.append (be16 0) (ByteArray.append (be16 0)
            (ByteArray.append matrix (ByteArray.append (be32 (dispW <<< 16))
              (be32 (dispH <<< 16))))))))))))))))
  let trak := mp4Box (ByteArray.mk #[0x74, 0x72, 0x61, 0x6B]) (ByteArray.append tkhd mdia)
  let mvhdBody :=
    ByteArray.append (be32 0) (ByteArray.append (be32 0) (ByteArray.append (be32 25000)
      (ByteArray.append (be32 (n * 1000)) (ByteArray.append (be32 0x00010000)
        (ByteArray.append (be16 0x0100) (ByteArray.append (be16 0) (ByteArray.append (be32 0)
          (ByteArray.append (be32 0) (ByteArray.append matrix
            (ByteArray.append (zerosU8 24) (be32 2)))))))))))
  let mvhd := mp4FullBox (ByteArray.mk #[0x6D, 0x76, 0x68, 0x64]) 0 mvhdBody
  let moov := mp4Box (ByteArray.mk #[0x6D, 0x6F, 0x6F, 0x76]) (ByteArray.append mvhd trak)
  return ByteArray.append ftyp (ByteArray.append mdat moov)

def hevcMain8BitScopeSafe (data : ByteArray) : Bool :=
  match extractHevcNals data with
  | none => false
  | some (nals, _) => Id.run do
    let mut spsMap : Array (Option HevcSps) := Array.replicate 16 none
    let mut ppsMap : Array (Option HevcPps) := Array.replicate 64 none
    let mut sawSlice := false
    let mut ok := true
    let mut prevIndepSh? : Option HevcSliceHeader := none
    for nal in nals do
      match parseNalHeader nal with
      | none => ok := false
      | some (nalType, layerId, tid) =>
        if layerId != 0 then ok := false
        let payload := nal.extract 2 nal.size
        if nalType == nalVps then
          match stripRbspWithMap payload with
          | none => ok := false
          | some rm =>
            match parseVps rm.rbsp with
            | none => ok := false
            | some _ => pure ()
        else if nalType == nalSps then
          match stripRbspWithMap payload with
          | none => ok := false
          | some rm =>
            match parseSps rm.rbsp with
            | none => ok := false
            | some sps => spsMap := spsMap.set! sps.spsId (some sps)
        else if nalType == nalPps then
          match stripRbspWithMap payload with
          | none => ok := false
          | some rm =>
            match parsePps rm.rbsp spsMap with
            | none => ok := false
            | some pps => ppsMap := ppsMap.set! pps.ppsId (some pps)
        else if nalType <= nalRaslR || (16 <= nalType && nalType <= nalCraNut) then
          match parseSliceHeader payload nalType tid spsMap ppsMap prevIndepSh? 0 with
          | none => ok := false
          | some sh =>
            if !sh.dependentSliceSegmentFlag then prevIndepSh? := some sh
            sawSlice := true
            if sh.sliceType != sliceI && sh.sliceType != sliceP && sh.sliceType != sliceB then
              ok := false
    ok && sawSlice

def hevcRangeTabLPS : Array Nat := #[
  128, 176, 208, 240, 128, 167, 197, 227, 128, 158, 187, 216, 123, 150, 178, 205,
  116, 142, 169, 195, 111, 135, 160, 185, 105, 128, 152, 175, 100, 122, 144, 166,
   95, 116, 137, 158,  90, 110, 130, 150,  85, 104, 123, 142,  81,  99, 117, 135,
   77,  94, 111, 128,  73,  89, 105, 122,  69,  85, 100, 116,  66,  80,  95, 110,
   62,  76,  90, 104,  59,  72,  86,  99,  56,  69,  81,  94,  53,  65,  77,  89,
   51,  62,  73,  85,  48,  59,  69,  80,  46,  56,  66,  76,  43,  53,  63,  72,
   41,  50,  59,  69,  39,  48,  56,  65,  37,  45,  54,  62,  35,  43,  51,  59,
   33,  41,  48,  56,  32,  39,  46,  53,  30,  37,  43,  50,  29,  35,  41,  48,
   27,  33,  39,  45,  26,  31,  37,  43,  24,  30,  35,  41,  23,  28,  33,  39,
   22,  27,  32,  37,  21,  26,  30,  35,  20,  24,  29,  33,  19,  23,  27,  31,
   18,  22,  26,  30,  17,  21,  25,  28,  16,  20,  23,  27,  15,  19,  22,  25,
   14,  18,  21,  24,  14,  17,  20,  23,  13,  16,  19,  22,  12,  15,  18,  21,
   12,  14,  17,  20,  11,  14,  16,  19,  11,  13,  15,  18,  10,  12,  15,  17,
   10,  12,  14,  16,   9,  11,  13,  15,   9,  11,  12,  14,   8,  10,  12,  14,
    8,   9,  11,  13,   7,   9,  11,  12,   7,   9,  10,  12,   7,   8,  10,  11,
    6,   8,   9,  11,   6,   7,   9,  10,   6,   7,   8,   9,   2,   2,   2,   2
]

def hevcTransIdxLPS : Array Nat := #[
   0,  0,  1,  2,  2,  4,  4,  5,  6,  7,  8,  9,  9, 11, 11, 12,
  13, 13, 15, 15, 16, 16, 18, 18, 19, 19, 21, 21, 22, 22, 23, 24,
  24, 25, 26, 26, 27, 27, 28, 29, 29, 30, 30, 30, 31, 32, 32, 33,
  33, 33, 34, 34, 35, 35, 35, 36, 36, 36, 37, 37, 37, 38, 38, 63
]

def hevcTransIdxMPS : Array Nat := #[
   1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15, 16,
  17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32,
  33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48,
  49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 62, 63
]

def elemSaoMergeFlag : Nat := 0
def elemSaoTypeIdx : Nat := 1
def elemEndOfSliceFlag : Nat := 6
def elemSplitCuFlag : Nat := 7
def elemCuTransquantBypass : Nat := 8
def elemSkipFlag : Nat := 9
def elemCuQpDelta : Nat := 10
def elemPredModeFlag : Nat := 11
def elemPartMode : Nat := 12
def elemPrevIntraLumaPredFlag : Nat := 14
def elemIntraChromaPredMode : Nat := 17
def elemMergeFlag : Nat := 18
def elemMergeIdx : Nat := 19
def elemInterPredIdc : Nat := 20
def elemRefIdxL0 : Nat := 21
def elemAbsMvdGreater0 : Nat := 23
def elemAbsMvdGreater1 : Nat := 24
def elemMvpLxFlag : Nat := 27
def elemNoResidualDataFlag : Nat := 28
def elemSplitTransformFlag : Nat := 29
def elemCbfLuma : Nat := 30
def elemCbfCbCr : Nat := 31
def elemTransformSkipFlag : Nat := 32
def elemLastSigXPrefix : Nat := 35
def elemLastSigYPrefix : Nat := 36
def elemSigCoeffGroupFlag : Nat := 39
def elemSigCoeffFlag : Nat := 40
def elemCoeffAbsLevelGt1 : Nat := 41
def elemCoeffAbsLevelGt2 : Nat := 42
def elemCuChromaQpOffsetFlag : Nat := 47
def elemCuChromaQpOffsetIdx : Nat := 48

def part2Nx2N : Nat := 0
def part2NxN : Nat := 1
def partNx2N : Nat := 2
def partNxN : Nat := 3
def part2NxnU : Nat := 4
def part2NxnD : Nat := 5
def partNLx2N : Nat := 6
def partNRx2N : Nat := 7

def modeInter : Nat := 0
def modeIntra : Nat := 1
def modeSkip : Nat := 2

def predL0 : Nat := 0
def predL1 : Nat := 1
def predBi : Nat := 2

def saoNone : Nat := 0
def saoBand : Nat := 1
def saoEdge : Nat := 2

def scanDiag : Nat := 0
def scanHoriz : Nat := 1
def scanVert : Nat := 2

def hevcVertScan2x2X : Array Nat := hevcHorizScan2x2Y
def hevcVertScan2x2Y : Array Nat := hevcHorizScan2x2X
def hevcVertScan4x4X : Array Nat := hevcHorizScan4x4Y
def hevcVertScan4x4Y : Array Nat := hevcHorizScan4x4X

def initCabacStates (sliceType cabacInitFlag : Nat) (sliceQp : Int) : Array Nat :=
  let initType0 := 2 - sliceType
  let initType := if cabacInitFlag == 1 && sliceType != 2 then initType0 ^^^ 3 else initType0
  let qp : Int := if sliceQp < 0 then 0 else if sliceQp > 51 then 51 else sliceQp
  let row := hevcCabacInitValues.getD initType #[]
  row.map fun initVal =>
    let m : Int := Int.ofNat (initVal >>> 4) * 5 - 45
    let n : Int := Int.ofNat ((initVal &&& 15) <<< 3) - 16
    let pre0 : Int := 2 * (asrInt (m * qp) 4 + n) - 127
    let pre1 : Int := if pre0 < 0 then -pre0 - 1 else pre0
    let pre2 : Int := if pre1 > 124 then 124 + Int.ofNat (pre1.toNat &&& 1) else pre1
    pre2.toNat

structure HevcCabacReader where
  rbsp  : ByteArray
  total : Nat
  pos   : Nat
  irange : Nat
  ioffset : Nat
  deriving Inhabited

namespace HevcCabacReader

def rawBit (c : HevcCabacReader) : Nat × HevcCabacReader :=
  let p := c.pos
  let c' := { c with pos := p + 1 }
  if p >= c.total then (0, c')
  else
    let b := (baGetD c.rbsp (p >>> 3) 0).toNat
    ((b >>> (7 - (p &&& 7))) &&& 1, c')

def init? (rbsp : ByteArray) (bitPos : Nat) : Option HevcCabacReader := do
  if rbsp.size == 0 then none
  let aligned := if (bitPos &&& 7) == 0 then bitPos else bitPos + (8 - (bitPos &&& 7))
  if (aligned >>> 3) > rbsp.size then none
  let c0 : HevcCabacReader := { rbsp := rbsp, total := rbsp.size * 8, pos := aligned, irange := 510, ioffset := 0 }
  let rec load (k : Nat) (ioff : Nat) (c : HevcCabacReader) : Nat × HevcCabacReader :=
    match k with
    | 0 => (ioff, c)
    | k' + 1 =>
      let (b, c') := c.rawBit
      load k' ((ioff <<< 1) ||| b) c'
  let (ioff, c1) := load 9 0 c0
  if ioff >= 510 then none else some { c1 with ioffset := ioff }

def decodeDecision (c : HevcCabacReader) (st : Array Nat) (ctx : Nat) : Nat × HevcCabacReader × Array Nat :=
  let entry := st.getD ctx 0
  let p := entry >>> 1
  let mps := entry &&& 1
  let qIdx := (c.irange >>> 6) &&& 3
  let rLps := hevcRangeTabLPS.getD ((p <<< 2) + qIdx) 2
  let rMps := c.irange - rLps
  let (binVal, mpsNext, pNext, rng0, off0) :=
    if c.ioffset >= rMps then
      let mpsN := if p == 0 then 1 - mps else mps
      (1 - mps, mpsN, hevcTransIdxLPS.getD p 0, rLps, c.ioffset - rMps)
    else
      (mps, mps, hevcTransIdxMPS.getD p 0, rMps, c.ioffset)
  let st' := st.set! ctx ((pNext <<< 1) ||| mpsNext)
  let rec ren (fuel : Nat) (rng off : Nat) (cur : HevcCabacReader) : Nat × Nat × HevcCabacReader :=
    match fuel with
    | 0 => (rng, off, cur)
    | fuel' + 1 =>
      if rng < 256 then
        let (b, cur') := cur.rawBit
        ren fuel' (rng <<< 1) ((off <<< 1) ||| b) cur'
      else (rng, off, cur)
  let (rng', off', cur') := ren 16 rng0 off0 c
  (binVal, { cur' with irange := rng', ioffset := off' }, st')

def decodeBypass (c : HevcCabacReader) : Nat × HevcCabacReader :=
  let (b, c1) := c.rawBit
  let off := (c.ioffset <<< 1) ||| b
  if off >= c.irange then (1, { c1 with ioffset := off - c.irange })
  else (0, { c1 with ioffset := off })

def decodeBypassBits (c : HevcCabacReader) (n : Nat) : Nat × HevcCabacReader :=
  let rec loop (k v : Nat) (cur : HevcCabacReader) : Nat × HevcCabacReader :=
    match k with
    | 0 => (v, cur)
    | k' + 1 =>
      let (b, cur') := cur.decodeBypass
      loop k' ((v <<< 1) ||| b) cur'
  loop n 0 c

def decodeTerminate (c : HevcCabacReader) : Nat × HevcCabacReader :=
  let rng := c.irange - 2
  if c.ioffset >= rng then (1, c)
  else
    let rec ren (fuel : Nat) (rng off : Nat) (cur : HevcCabacReader) : Nat × Nat × HevcCabacReader :=
      match fuel with
      | 0 => (rng, off, cur)
      | fuel' + 1 =>
        if rng < 256 then
          let (b, cur') := cur.rawBit
          ren fuel' (rng <<< 1) ((off <<< 1) ||| b) cur'
        else (rng, off, cur)
    let (rng', off', cur') := ren 16 rng c.ioffset c
    (0, { cur' with irange := rng', ioffset := off' })

def readPcmAndReinit (c : HevcCabacReader) (nbytes : Nat) : Option (ByteArray × HevcCabacReader) := do
  let bs := (c.pos + 7) >>> 3
  if bs + nbytes > c.rbsp.size then none
  let rec copyPcm (fuel i : Nat) (acc : Array UInt8) : ByteArray :=
    match fuel with
    | 0 => ByteArray.mk acc
    | fuel' + 1 =>
      if i >= nbytes then ByteArray.mk acc
      else copyPcm fuel' (i + 1) (acc.push (baGetD c.rbsp (bs + i) 0))
  let pcm := copyPcm nbytes 0 #[]
  let c0 := { c with pos := (bs + nbytes) * 8, irange := 510, ioffset := 0 }
  let rec load (k ioff : Nat) (cur : HevcCabacReader) : Nat × HevcCabacReader :=
    match k with
    | 0 => (ioff, cur)
    | k' + 1 =>
      let (b, cur') := cur.rawBit
      load k' ((ioff <<< 1) ||| b) cur'
  let (ioff, c1) := load 9 0 c0
  some (pcm, { c1 with ioffset := ioff })

def reinit (c : HevcCabacReader) : Option HevcCabacReader := do
  let bs := (c.pos + 7) >>> 3
  if bs >= c.rbsp.size then none
  let c0 := { c with pos := bs * 8, irange := 510, ioffset := 0 }
  let rec load (k ioff : Nat) (cur : HevcCabacReader) : Nat × HevcCabacReader :=
    match k with
    | 0 => (ioff, cur)
    | k' + 1 =>
      let (b, cur') := cur.rawBit
      load k' ((ioff <<< 1) ||| b) cur'
  let (ioff, c1) := load 9 0 c0
  some { c1 with ioffset := ioff }

end HevcCabacReader

structure HevcCabacWriter where
  w : HevcBitWriter
  ilow : Nat
  irange : Nat
  bitsOutstanding : Nat
  firstBit : Bool
  deriving Inhabited

namespace HevcCabacWriter

def fresh : HevcCabacWriter :=
  { w := HevcBitWriter.empty, ilow := 0, irange := 510, bitsOutstanding := 0, firstBit := true }

def putBit (c : HevcCabacWriter) (b : Nat) : HevcCabacWriter :=
  let c0 :=
    if c.firstBit then { c with firstBit := false }
    else { c with w := c.w.putBit b }
  let inv := 1 - b
  let rec flushOut (fuel : Nat) (cur : HevcBitWriter) : HevcBitWriter :=
    match fuel with
    | 0 => cur
    | fuel' + 1 => flushOut fuel' (cur.putBit inv)
  { c0 with w := flushOut c0.bitsOutstanding c0.w, bitsOutstanding := 0 }

def renorm (c : HevcCabacWriter) : HevcCabacWriter :=
  let rec loop (fuel : Nat) (cur : HevcCabacWriter) : HevcCabacWriter :=
    match fuel with
    | 0 => cur
    | fuel' + 1 =>
      if cur.irange >= 256 then cur
      else
        let cur1 :=
          if cur.ilow < 256 then cur.putBit 0
          else if cur.ilow >= 512 then ({ cur with ilow := cur.ilow - 512 }).putBit 1
          else { cur with ilow := cur.ilow - 256, bitsOutstanding := cur.bitsOutstanding + 1 }
        loop fuel' { cur1 with irange := cur1.irange <<< 1, ilow := cur1.ilow <<< 1 }
  loop 32 c

def encodeDecision (c : HevcCabacWriter) (st : Array Nat) (ctx binVal : Nat) :
    HevcCabacWriter × Array Nat :=
  let entry := st.getD ctx 0
  let p := entry >>> 1
  let mps := entry &&& 1
  let qIdx := (c.irange >>> 6) &&& 3
  let rLps := hevcRangeTabLPS.getD ((p <<< 2) + qIdx) 2
  let rMps := c.irange - rLps
  let b := if binVal == 0 then 0 else 1
  if b != mps then
    let mpsN := if p == 0 then 1 - mps else mps
    let st' := st.set! ctx ((hevcTransIdxLPS.getD p 0 <<< 1) ||| mpsN)
    ({ c with ilow := c.ilow + rMps, irange := rLps }.renorm, st')
  else
    let st' := st.set! ctx ((hevcTransIdxMPS.getD p 0 <<< 1) ||| mps)
    ({ c with irange := rMps }.renorm, st')

def encodeBypass (c : HevcCabacWriter) (binVal : Nat) : HevcCabacWriter :=
  let ilow0 := c.ilow <<< 1
  let ilow := if binVal != 0 then ilow0 + c.irange else ilow0
  if ilow >= 1024 then
    { c.putBit 1 with ilow := ilow - 1024 }
  else if ilow < 512 then
    { c.putBit 0 with ilow := ilow }
  else
    { c with ilow := ilow - 512, bitsOutstanding := c.bitsOutstanding + 1 }

def encodeBypassBits (c : HevcCabacWriter) (val n : Nat) : HevcCabacWriter :=
  let rec loop (k : Nat) (cur : HevcCabacWriter) : HevcCabacWriter :=
    match k with
    | 0 => cur
    | k' + 1 => loop k' (cur.encodeBypass ((val >>> k') &&& 1))
  loop n c

def encodeTerminate (c : HevcCabacWriter) (binVal : Nat) : HevcCabacWriter :=
  let rng := c.irange - 2
  if binVal != 0 then
    let c1 := { c with ilow := c.ilow + rng, irange := 2 }.renorm
    let c2 := c1.putBit ((c1.ilow >>> 9) &&& 1)
    let c3 := { c2 with w := c2.w.putBit ((c2.ilow >>> 8) &&& 1) }
    { c3 with w := (c3.w.putBit 1).alignZero }
  else
    { c with irange := rng }.renorm

def writePcmAndReinit (c : HevcCabacWriter) (pcm : ByteArray) : HevcCabacWriter :=
  let n := pcm.size
  let rec loop (fuel i : Nat) (w : HevcBitWriter) : HevcBitWriter :=
    match fuel with
    | 0 => w
    | fuel' + 1 =>
      if i >= n then w
      else loop fuel' (i + 1) (w.putBits (baGetD pcm i 0).toNat 8)
  { w := loop n 0 c.w.alignZero, ilow := 0, irange := 510, bitsOutstanding := 0, firstBit := true }

def toBytes (c : HevcCabacWriter) : Option ByteArray :=
  c.w.toBytes

end HevcCabacWriter

def decSaoMergeFlag (c : HevcCabacReader) (st : Array Nat) : Nat × HevcCabacReader × Array Nat :=
  c.decodeDecision st (hevcCabacElemOffset.getD elemSaoMergeFlag 0)

def decSaoTypeIdx (c : HevcCabacReader) (st : Array Nat) : Nat × HevcCabacReader × Array Nat :=
  let (b, c1, st1) := c.decodeDecision st (hevcCabacElemOffset.getD elemSaoTypeIdx 0)
  if b == 0 then (saoNone, c1, st1)
  else
    let (bp, c2) := c1.decodeBypass
    if bp == 0 then (saoBand, c2, st1) else (saoEdge, c2, st1)

def decSaoBandPosition (c : HevcCabacReader) : Nat × HevcCabacReader :=
  c.decodeBypassBits 5

def decSaoOffsetAbs (c : HevcCabacReader) (bitDepth : Nat) : Nat × HevcCabacReader := Id.run do
  let bd := if bitDepth < 10 then bitDepth else 10
  let length := (1 <<< (bd - 5)) - 1
  let mut i := 0
  let mut c := c
  let mut fuel := length + 1
  while i < length && fuel > 0 do
    fuel := fuel - 1
    let (b, c') := c.decodeBypass
    c := c'
    if b == 0 then break
    i := i + 1
  return (i, c)

def decSaoEoClass (c : HevcCabacReader) : Nat × HevcCabacReader :=
  c.decodeBypassBits 2

def decSplitCuFlag (c : HevcCabacReader) (st : Array Nat) (depthLeft depthTop ctDepth : Nat) :
    Nat × HevcCabacReader × Array Nat :=
  let inc := (if depthLeft > ctDepth then 1 else 0) + (if depthTop > ctDepth then 1 else 0)
  c.decodeDecision st (hevcCabacElemOffset.getD elemSplitCuFlag 0 + inc)

def decCuTransquantBypass (c : HevcCabacReader) (st : Array Nat) : Nat × HevcCabacReader × Array Nat :=
  c.decodeDecision st (hevcCabacElemOffset.getD elemCuTransquantBypass 0)

def decSkipFlag (c : HevcCabacReader) (st : Array Nat) (skipLeft skipUp : Nat) :
    Nat × HevcCabacReader × Array Nat :=
  let inc := (if skipLeft != 0 then 1 else 0) + (if skipUp != 0 then 1 else 0)
  c.decodeDecision st (hevcCabacElemOffset.getD elemSkipFlag 0 + inc)

def decPredMode (c : HevcCabacReader) (st : Array Nat) : Nat × HevcCabacReader × Array Nat :=
  let (b, c1, st1) := c.decodeDecision st (hevcCabacElemOffset.getD elemPredModeFlag 0)
  if b != 0 then (modeIntra, c1, st1) else (modeInter, c1, st1)

def decPartMode (c : HevcCabacReader) (st : Array Nat)
    (log2CbSize log2MinCbSize predMode ampEnabled : Nat) : Nat × HevcCabacReader × Array Nat :=
  let base := hevcCabacElemOffset.getD elemPartMode 0
  let (b0, c1, st1) := c.decodeDecision st base
  if b0 != 0 then (part2Nx2N, c1, st1)
  else if log2CbSize == log2MinCbSize then
    if predMode == modeIntra then (partNxN, c1, st1)
    else
      let (b1, c2, st2) := c1.decodeDecision st1 (base + 1)
      if b1 != 0 then (part2NxN, c2, st2)
      else if log2CbSize == 3 then (partNx2N, c2, st2)
      else
        let (b2, c3, st3) := c2.decodeDecision st2 (base + 2)
        if b2 != 0 then (partNx2N, c3, st3) else (partNxN, c3, st3)
  else if ampEnabled == 0 then
    let (b1, c2, st2) := c1.decodeDecision st1 (base + 1)
    if b1 != 0 then (part2NxN, c2, st2) else (partNx2N, c2, st2)
  else
    let (b1, c2, st2) := c1.decodeDecision st1 (base + 1)
    if b1 != 0 then
      let (b3, c3, st3) := c2.decodeDecision st2 (base + 3)
      if b3 != 0 then (part2NxN, c3, st3)
      else
        let (bp, c4) := c3.decodeBypass
        if bp != 0 then (part2NxnD, c4, st3) else (part2NxnU, c4, st3)
    else
      let (b3, c3, st3) := c2.decodeDecision st2 (base + 3)
      if b3 != 0 then (partNx2N, c3, st3)
      else
        let (bp, c4) := c3.decodeBypass
        if bp != 0 then (partNRx2N, c4, st3) else (partNLx2N, c4, st3)

def decPcmFlag (c : HevcCabacReader) : Nat × HevcCabacReader :=
  c.decodeTerminate

def decPrevIntraLumaPredFlag (c : HevcCabacReader) (st : Array Nat) : Nat × HevcCabacReader × Array Nat :=
  c.decodeDecision st (hevcCabacElemOffset.getD elemPrevIntraLumaPredFlag 0)

def decMpmIdx (c : HevcCabacReader) : Nat × HevcCabacReader := Id.run do
  let mut i := 0
  let mut c := c
  while i < 2 do
    let (b, c') := c.decodeBypass
    c := c'
    if b == 0 then break
    i := i + 1
  return (i, c)

def decRemIntraLumaPredMode (c : HevcCabacReader) : Nat × HevcCabacReader :=
  c.decodeBypassBits 5

def decIntraChromaPredMode (c : HevcCabacReader) (st : Array Nat) : Nat × HevcCabacReader × Array Nat :=
  let (b, c1, st1) := c.decodeDecision st (hevcCabacElemOffset.getD elemIntraChromaPredMode 0)
  if b == 0 then (4, c1, st1) else
    let (v, c2) := c1.decodeBypassBits 2
    (v, c2, st1)

def decMergeFlag (c : HevcCabacReader) (st : Array Nat) : Nat × HevcCabacReader × Array Nat :=
  c.decodeDecision st (hevcCabacElemOffset.getD elemMergeFlag 0)

def decMergeIdx (c : HevcCabacReader) (st : Array Nat) (maxNumMergeCand : Nat) :
    Nat × HevcCabacReader × Array Nat :=
  if maxNumMergeCand <= 1 then (0, c, st)
  else
    let (b, c1, st1) := c.decodeDecision st (hevcCabacElemOffset.getD elemMergeIdx 0)
    if b == 0 then (0, c1, st1)
    else Id.run do
      let mut i := 1
      let mut c := c1
      while i < maxNumMergeCand - 1 do
        let (bp, c') := c.decodeBypass
        c := c'
        if bp == 0 then break
        i := i + 1
      return (i, c, st1)

def decInterPredIdc (c : HevcCabacReader) (st : Array Nat) (nPbW nPbH ctDepth : Nat) :
    Nat × HevcCabacReader × Array Nat :=
  let base := hevcCabacElemOffset.getD elemInterPredIdc 0
  if nPbW + nPbH == 12 then
    c.decodeDecision st (base + 4)
  else
    let (b, c1, st1) := c.decodeDecision st (base + ctDepth)
    if b != 0 then (predBi, c1, st1) else c1.decodeDecision st1 (base + 4)

def decRefIdx (c : HevcCabacReader) (st : Array Nat) (nbRefs : Nat) :
    Nat × HevcCabacReader × Array Nat :=
  if nbRefs <= 1 then (0, c, st)
  else Id.run do
    let maxIdx := nbRefs - 1
    let base := hevcCabacElemOffset.getD elemRefIdxL0 0
    let mut i := 0
    let mut c := c
    let mut st := st
    let lim := if maxIdx < 2 then maxIdx else 2
    while i < lim do
      let (b, c', st') := c.decodeDecision st (base + i)
      c := c'
      st := st'
      if b == 0 then break
      i := i + 1
    if i == 2 then
      while i < maxIdx do
        let (bp, c') := c.decodeBypass
        c := c'
        if bp == 0 then break
        i := i + 1
    return (i, c, st)

def decMvpLxFlag (c : HevcCabacReader) (st : Array Nat) : Nat × HevcCabacReader × Array Nat :=
  c.decodeDecision st (hevcCabacElemOffset.getD elemMvpLxFlag 0)

def decEg1 (c : HevcCabacReader) : Option (Nat × HevcCabacReader) := Id.run do
  let mut k := 1
  let mut val := 2
  let mut c := c
  while k < 17 do
    let (b, c') := c.decodeBypass
    c := c'
    if b == 0 then break
    val := val + (1 <<< k)
    k := k + 1
  if k == 17 then return none
  while k > 0 do
    k := k - 1
    let (b, c') := c.decodeBypass
    c := c'
    val := val + (b <<< k)
  return some (val, c)

def decMvd (c : HevcCabacReader) (st : Array Nat) : Option (Int × Int × HevcCabacReader × Array Nat) := do
  let (gt0x, c1, st1) := c.decodeDecision st (hevcCabacElemOffset.getD elemAbsMvdGreater0 0)
  let (gt0y, c2, st2) := c1.decodeDecision st1 (hevcCabacElemOffset.getD elemAbsMvdGreater0 0)
  let (gt1x, c3, st3) :=
    if gt0x != 0 then c2.decodeDecision st2 (hevcCabacElemOffset.getD elemAbsMvdGreater1 0 + 1)
    else (0, c2, st2)
  let (gt1y, c4, st4) :=
    if gt0y != 0 then c3.decodeDecision st3 (hevcCabacElemOffset.getD elemAbsMvdGreater1 0 + 1)
    else (0, c3, st3)
  let finish (gt0 gt1 : Nat) (cur : HevcCabacReader) : Option (Int × HevcCabacReader) := do
    if gt0 == 0 then some (0, cur)
    else if gt1 == 0 then
      let (s, cur') := cur.decodeBypass
      some (if s != 0 then (-1 : Int) else 1, cur')
    else
      let (val, cur') ← decEg1 cur
      let (s, cur'') := cur'.decodeBypass
      some (if s != 0 then -val else val, cur'')
  let (mx, c5) ← finish gt0x gt1x c4
  let (my, c6) ← finish gt0y gt1y c5
  some (mx, my, c6, st4)

def decNoResidualDataFlag (c : HevcCabacReader) (st : Array Nat) : Nat × HevcCabacReader × Array Nat :=
  c.decodeDecision st (hevcCabacElemOffset.getD elemNoResidualDataFlag 0)

def decSplitTransformFlag (c : HevcCabacReader) (st : Array Nat) (log2TrafoSize : Nat) :
    Nat × HevcCabacReader × Array Nat :=
  c.decodeDecision st (hevcCabacElemOffset.getD elemSplitTransformFlag 0 + 5 - log2TrafoSize)

def decCbfCbCr (c : HevcCabacReader) (st : Array Nat) (trafoDepth : Nat) :
    Nat × HevcCabacReader × Array Nat :=
  c.decodeDecision st (hevcCabacElemOffset.getD elemCbfCbCr 0 + trafoDepth)

def decCbfLuma (c : HevcCabacReader) (st : Array Nat) (trafoDepth : Nat) :
    Nat × HevcCabacReader × Array Nat :=
  c.decodeDecision st (hevcCabacElemOffset.getD elemCbfLuma 0 + (if trafoDepth == 0 then 1 else 0))

def decCuQpDelta (c : HevcCabacReader) (st : Array Nat) : Option (Int × HevcCabacReader × Array Nat) := do
  let mut prefLen := 0
  let mut inc := 0
  let mut c := c
  let mut st := st
  let base := hevcCabacElemOffset.getD elemCuQpDelta 0
  while prefLen < 5 do
    let (b, c', st') := c.decodeDecision st (base + inc)
    c := c'
    st := st'
    if b == 0 then break
    prefLen := prefLen + 1
    inc := 1
  let mut suffix := 0
  if prefLen >= 5 then
    let mut k := 0
    while k < 7 do
      let (b, c') := c.decodeBypass
      c := c'
      if b == 0 then break
      suffix := suffix + (1 <<< k)
      k := k + 1
    if k == 7 then none
    else
      let mut kk := k
      while kk > 0 do
        kk := kk - 1
        let (b, c') := c.decodeBypass
        c := c'
        suffix := suffix + (b <<< kk)
      let absVal := prefLen + suffix
      if absVal == 0 then some (0, c, st)
      else
        let (s, c') := c.decodeBypass
        some (if s != 0 then -Int.ofNat absVal else Int.ofNat absVal, c', st)
  else
    let absVal := prefLen
    if absVal == 0 then some (0, c, st)
    else
      let (s, c') := c.decodeBypass
      some (if s != 0 then -Int.ofNat absVal else Int.ofNat absVal, c', st)

def decCuChromaQpOffset (c : HevcCabacReader) (st : Array Nat) (listLenMinus1 : Nat) :
    Nat × HevcCabacReader × Array Nat :=
  let (b, c1, st1) := c.decodeDecision st (hevcCabacElemOffset.getD elemCuChromaQpOffsetFlag 0)
  if b == 0 then (0, c1, st1)
  else if listLenMinus1 == 0 then (1, c1, st1)
  else Id.run do
    let cMax := if 5 > listLenMinus1 then 5 else listLenMinus1
    let mut i := 0
    let mut c := c1
    let mut st := st1
    let base := hevcCabacElemOffset.getD elemCuChromaQpOffsetIdx 0
    while i < cMax do
      let (b, c', st') := c.decodeDecision st base
      c := c'
      st := st'
      if b == 0 then break
      i := i + 1
    return (i + 1, c, st)

def decTransformSkipFlag (c : HevcCabacReader) (st : Array Nat) (cIdx : Nat) :
    Nat × HevcCabacReader × Array Nat :=
  c.decodeDecision st (hevcCabacElemOffset.getD elemTransformSkipFlag 0 + (if cIdx != 0 then 1 else 0))

def sigCoeffCtxInc (log2TrafoSize cIdx scanIdx xCg yCg prevSig xS yS : Nat) : Nat := Id.run do
  if log2TrafoSize == 2 then
    let scfOffset := if cIdx != 0 then 27 else 0
    return hevcCabacCtxIdxMap.getD ((yS <<< 2) + xS) 0 + scfOffset
  let mut scfOffset := if cIdx != 0 then 27 else 0
  if cIdx == 0 then
    if xCg > 0 || yCg > 0 then scfOffset := scfOffset + 3
    if log2TrafoSize == 3 then
      scfOffset := scfOffset + (if scanIdx == scanDiag then 9 else 15)
    else
      scfOffset := scfOffset + 21
  else
    if log2TrafoSize == 3 then scfOffset := scfOffset + 9 else scfOffset := scfOffset + 12
  if xS == 0 && yS == 0 then
    if xCg == 0 && yCg == 0 then return (if cIdx == 0 then 0 else 27)
    else return 2 + scfOffset
  return hevcCabacCtxIdxMap.getD (((prevSig + 1) <<< 4) + (yS <<< 2) + xS) 0 + scfOffset

def getScanTables (log2TrafoSize scanIdx : Nat) :
    Array Nat × Array Nat × Array Nat × Array Nat :=
  let (sxCg, syCg) :=
    if log2TrafoSize == 2 then (hevcScan1x1, hevcScan1x1)
    else if log2TrafoSize == 3 then
      if scanIdx == scanDiag then (hevcDiagScan2x2X, hevcDiagScan2x2Y)
      else if scanIdx == scanHoriz then (hevcHorizScan2x2X, hevcHorizScan2x2Y)
      else (hevcVertScan2x2X, hevcVertScan2x2Y)
    else if log2TrafoSize == 4 then (hevcDiagScan4x4X, hevcDiagScan4x4Y)
    else (hevcDiagScan8x8X, hevcDiagScan8x8Y)
  let (sxOff, syOff) :=
    if scanIdx == scanDiag then (hevcDiagScan4x4X, hevcDiagScan4x4Y)
    else if scanIdx == scanHoriz then (hevcHorizScan4x4X, hevcHorizScan4x4Y)
    else (hevcVertScan4x4X, hevcVertScan4x4Y)
  (sxCg, syCg, sxOff, syOff)

def lastSigCoeffXY (c : HevcCabacReader) (st : Array Nat) (log2Size cIdx : Nat) :
    Nat × Nat × HevcCabacReader × Array Nat := Id.run do
  let maxPref := (log2Size <<< 1) - 1
  let (ctxOffset, ctxShift) :=
    if cIdx == 0 then
      (3 * (log2Size - 2) + ((log2Size - 1) >>> 2), (log2Size + 1) >>> 2)
    else (15, log2Size - 2)
  let mut px := 0
  let mut c := c
  let mut st := st
  let baseX := hevcCabacElemOffset.getD elemLastSigXPrefix 0
  while px < maxPref do
    let (b, c', st') := c.decodeDecision st (baseX + (px >>> ctxShift) + ctxOffset)
    c := c'
    st := st'
    if b == 0 then break
    px := px + 1
  let mut py := 0
  let baseY := hevcCabacElemOffset.getD elemLastSigYPrefix 0
  while py < maxPref do
    let (b, c', st') := c.decodeDecision st (baseY + (py >>> ctxShift) + ctxOffset)
    c := c'
    st := st'
    if b == 0 then break
    py := py + 1
  let finishLast (pref : Nat) (cur : HevcCabacReader) : Nat × HevcCabacReader :=
    if pref > 3 then
      let nbits := (pref >>> 1) - 1
      let (suff, cur') := cur.decodeBypassBits nbits
      (((2 + (pref &&& 1)) <<< nbits) + suff, cur')
    else (pref, cur)
  let (lx, c1) := finishLast px c
  let (ly, c2) := finishLast py c1
  return (lx, ly, c2, st)

def coeffAbsLevelRemainingDecode (c : HevcCabacReader) (rcRiceParam : Nat) :
    Option (Nat × HevcCabacReader) := do
  let mut prefLen := 0
  let mut c := c
  while prefLen < 32 do
    let (b, c') := c.decodeBypass
    c := c'
    if b == 0 then break
    prefLen := prefLen + 1
  if prefLen < 3 then
    let (suffix, c') := c.decodeBypassBits rcRiceParam
    some ((prefLen <<< rcRiceParam) + suffix, c')
  else if prefLen > 20 then none
  else
    let nbits := prefLen - 3 + rcRiceParam
    let (suffix, c') := c.decodeBypassBits nbits
    some ((((1 <<< (prefLen - 3)) + 2) <<< rcRiceParam) + suffix, c')

structure HevcResidual where
  coeffs : Array Int
  transformSkipFlag : Nat
  dcOnly : Bool
  colLimit : Nat
  deriving Inhabited

def decodeResidualCoding (c0 : HevcCabacReader) (st0 : Array Nat)
    (sps : HevcSps) (pps : HevcPps) (log2TrafoSize scanIdx cIdx predMode
      cuTransquantBypass : Nat) (qpY qpCb qpCr : Int) :
    Option (HevcResidual × HevcCabacReader × Array Nat) := do
  let size := 1 <<< log2TrafoSize
  let mut coeffs : Array Int := Array.replicate (size * size) 0
  let mut c := c0
  let mut st := st0
  let mut transformSkipFlag := 0
  if pps.transformSkipEnabledFlag && cuTransquantBypass == 0 &&
      log2TrafoSize <= pps.log2MaxTransformSkipBlockSize then
    let (f, c', st') := decTransformSkipFlag c st cIdx
    c := c'
    st := st'
    transformSkipFlag := f
  let (lx0, ly0, c1, st1) := lastSigCoeffXY c st log2TrafoSize cIdx
  c := c1
  st := st1
  let (lastX, lastY) := if scanIdx == scanVert then (ly0, lx0) else (lx0, ly0)
  let xCgLast := lastX >>> 2
  let yCgLast := lastY >>> 2
  let lastCg :=
    if log2TrafoSize == 2 then 0
    else if log2TrafoSize == 3 then
      if scanIdx == scanDiag then
        (hevcDiagScan2x2Inv.getD yCgLast #[]).getD xCgLast 0
      else if scanIdx == scanHoriz then yCgLast * 2 + xCgLast
      else xCgLast * 2 + yCgLast
    else if log2TrafoSize == 4 then
      (hevcDiagScan4x4Inv.getD yCgLast #[]).getD xCgLast 0
    else
      (hevcDiagScan8x8Inv.getD yCgLast #[]).getD xCgLast 0
  let (sxCg, syCg, sxOff, syOff) := getScanTables log2TrafoSize scanIdx
  let qp := if cIdx == 0 then qpY else if cIdx == 1 then qpCb else qpCr
  let shiftNat : Nat := 8 + log2TrafoSize - 5
  let add : Int := Int.ofNat (1 <<< (shiftNat - 1))
  let scale : Int := (hevcLevelScale.getD (qp.toNat % 6) 40) * Int.ofNat (1 <<< (qp.toNat / 6))
  let useSl := sps.scalingListEnableFlag && !(transformSkipFlag != 0 && log2TrafoSize > 2)
  let slData := if pps.scalingListDataPresentFlag then pps.scalingList else sps.scalingList
  let matrixId := cIdx + (if predMode != modeIntra then 3 else 0)
  let scaleMatrix := (slData.sl.getD (log2TrafoSize - 2) #[]).getD matrixId #[]
  let dcScale : Int :=
    if useSl && log2TrafoSize >= 4 then
      (slData.slDc.getD (log2TrafoSize - 4) #[]).getD matrixId 16
    else 16
  let cgSide := 1 <<< (log2TrafoSize - 2)
  let mut sigCg : Array (Array Nat) := Array.replicate cgSide (Array.replicate cgSide 0)
  sigCg := sigCg.set! yCgLast ((sigCg.getD yCgLast #[]).set! xCgLast 1)
  let mut greater1Ctx := 1
  let mut dcOnly := true
  let mut maxXC := 0
  let mut i := lastCg
  let mut fuel := lastCg + 1
  while fuel > 0 do
    fuel := fuel - 1
    let xCg := sxCg.getD i 0
    let yCg := syCg.getD i 0
    if i < lastCg && i > 0 then
      let mut ctxCg := 0
      if xCg < cgSide - 1 then ctxCg := ctxCg ||| (sigCg.getD yCg #[]).getD (xCg + 1) 0
      if yCg < cgSide - 1 then ctxCg := ctxCg ||| (sigCg.getD (yCg + 1) #[]).getD xCg 0
      let inc := ctxCg + (if cIdx != 0 then 2 else 0)
      let (f, c', st') := c.decodeDecision st
        (hevcCabacElemOffset.getD elemSigCoeffGroupFlag 0 + inc)
      c := c'
      st := st'
      sigCg := sigCg.set! yCg ((sigCg.getD yCg #[]).set! xCg f)
    else if i == 0 then
      sigCg := sigCg.set! 0 ((sigCg.getD 0 #[]).set! 0 1)
    if (sigCg.getD yCg #[]).getD xCg 0 != 0 then
      let mut prevSig := 0
      if xCg < cgSide - 1 && (sigCg.getD yCg #[]).getD (xCg + 1) 0 != 0 then prevSig := prevSig ||| 1
      if yCg < cgSide - 1 && (sigCg.getD (yCg + 1) #[]).getD xCg 0 != 0 then prevSig := prevSig ||| 2
      let mut nEnd := 15
      if i == lastCg then
        let lx4 := lastX &&& 3
        let ly4 := lastY &&& 3
        nEnd :=
          if scanIdx == scanDiag then (hevcDiagScan4x4Inv.getD ly4 #[]).getD lx4 0
          else if scanIdx == scanHoriz then ly4 * 4 + lx4
          else lx4 * 4 + ly4
      let mut nzPos : Array Nat := #[]
      if i == lastCg then nzPos := nzPos.push nEnd
      let mut implicitNonZero := if i != lastCg && i > 0 then 1 else 0
      let nStart :=
        if i == lastCg then
          if nEnd == 0 then 0 else nEnd - 1
        else 15
      let mut nFuel := if i == lastCg && nEnd == 0 then 0 else nStart + 1
      let mut n := nStart
      while nFuel > 0 do
        nFuel := nFuel - 1
        let mut sig := 0
        if n == 0 && implicitNonZero != 0 then sig := 1
        else
          let xS := sxOff.getD n 0
          let yS := syOff.getD n 0
          let inc := sigCoeffCtxInc log2TrafoSize cIdx scanIdx xCg yCg prevSig xS yS
          let (f, c', st') := c.decodeDecision st
            (hevcCabacElemOffset.getD elemSigCoeffFlag 0 + inc)
          c := c'
          st := st'
          sig := f
          if sig != 0 then implicitNonZero := 0
        if sig != 0 then nzPos := nzPos.push n
        if n == 0 then break
        n := n - 1
      let numNz := nzPos.size
      if numNz != 0 then
        let mut ctxSet := if i > 0 && cIdx == 0 then 2 else 0
        if i != lastCg && greater1Ctx == 0 then ctxSet := ctxSet + 1
        greater1Ctx := 1
        let gt1Base := hevcCabacElemOffset.getD elemCoeffAbsLevelGt1 0 + (ctxSet <<< 2) +
          (if cIdx != 0 then 16 else 0)
        let mut gt1Flags : Array Nat := Array.replicate numNz 0
        let mut firstGt1Idx : Int := -1
        let mut m := 0
        let lim8 := if numNz < 8 then numNz else 8
        while m < lim8 do
          let (g1, c', st') := c.decodeDecision st (gt1Base + greater1Ctx)
          c := c'
          st := st'
          gt1Flags := gt1Flags.set! m g1
          if g1 != 0 then
            greater1Ctx := 0
            if firstGt1Idx == -1 then firstGt1Idx := m
          else if greater1Ctx > 0 && greater1Ctx < 3 then
            greater1Ctx := greater1Ctx + 1
          m := m + 1
        let mut gt2Flag := 0
        if firstGt1Idx != -1 then
          let gt2Ctx := hevcCabacElemOffset.getD elemCoeffAbsLevelGt2 0 + ctxSet +
            (if cIdx != 0 then 4 else 0)
          let (g2, c', st') := c.decodeDecision st gt2Ctx
          c := c'
          st := st'
          gt2Flag := g2
        let firstNzPosInCg := nzPos.getD (numNz - 1) 0
        let lastNzPosInCg := nzPos.getD 0 0
        let signHidden := pps.signDataHidingFlag && cuTransquantBypass == 0 &&
          lastNzPosInCg >= firstNzPosInCg + 4
        let numSigns := if signHidden then numNz - 1 else numNz
        let (signs, c') := c.decodeBypassBits numSigns
        c := c'
        let mut cRice := 0
        let mut sumAbs : Nat := 0
        m := 0
        while m < numNz do
          let baseLvl :=
            if m >= 8 then 1
            else 1 + gt1Flags.getD m 0 + (if m == firstGt1Idx.toNat && firstGt1Idx >= 0 then gt2Flag else 0)
          let needRem := m >= 8 ||
            (gt1Flags.getD m 0 != 0 && !(m == firstGt1Idx.toNat && firstGt1Idx >= 0 && gt2Flag == 0))
          let (transLevel, cNext) ←
            if needRem then
              match coeffAbsLevelRemainingDecode c cRice with
              | none => none
              | some (rem, c'') => some (baseLvl + rem, c'')
            else some (baseLvl, c)
          c := cNext
          if needRem && transLevel > (3 <<< cRice) then cRice := if cRice + 1 < 4 then cRice + 1 else 4
          sumAbs := sumAbs + transLevel
          let sgn :=
            if signHidden && m == numNz - 1 then sumAbs &&& 1
            else (signs >>> (numSigns - 1 - m)) &&& 1
          let signedLevel : Int := if sgn != 0 then -Int.ofNat transLevel else Int.ofNat transLevel
          let nPos := nzPos.getD m 0
          let xC := (xCg <<< 2) + sxOff.getD nPos 0
          let yC := (yCg <<< 2) + syOff.getD nPos 0
          if xC != 0 || yC != 0 then dcOnly := false
          if xC > maxXC then maxXC := xC
          let val : Int :=
            if cuTransquantBypass != 0 then signedLevel
            else
              let scaleM : Int :=
                if !useSl then 16
                else if xC == 0 && yC == 0 && log2TrafoSize >= 4 then dcScale
                else if log2TrafoSize == 2 then scaleMatrix.getD ((yC <<< 2) + xC) 16
                else if log2TrafoSize == 3 then scaleMatrix.getD ((yC <<< 3) + xC) 16
                else if log2TrafoSize == 4 then
                  scaleMatrix.getD (((yC >>> 1) <<< 3) + (xC >>> 1)) 16
                else scaleMatrix.getD (((yC >>> 2) <<< 3) + (xC >>> 2)) 16
              asrInt ((signedLevel * scale * scaleM) + add) shiftNat
          let clipped := if val < -32768 then (-32768 : Int) else if val > 32767 then 32767 else val
          coeffs := coeffs.set! (yC * size + xC) clipped
          m := m + 1
    if i == 0 then break
    i := i - 1
  some ({
    coeffs := coeffs
    transformSkipFlag := transformSkipFlag
    dcOnly := dcOnly
    colLimit := if lastX > lastY then lastX else lastY
  }, c, st)

def lastPrefixEncode (pos : Nat) : Nat × Nat × Nat :=
  if pos <= 3 then (pos, 0, 0)
  else
    let nbits := natBitLen pos - 1
    let base := 1 <<< nbits
    let pref := (nbits <<< 1) + (if pos >= base + (base >>> 1) then 1 else 0)
    (pref, nbits - 1, pos - ((2 + (pref &&& 1)) <<< (nbits - 1)))

def encLastPrefix (w0 : HevcCabacWriter) (st0 : Array Nat) (log2Size cIdx axis pref : Nat) :
    HevcCabacWriter × Array Nat := Id.run do
  let maxPref := (log2Size <<< 1) - 1
  let (ctxOffset, ctxShift) :=
    if cIdx == 0 then
      (3 * (log2Size - 2) + ((log2Size - 1) >>> 2), (log2Size + 1) >>> 2)
    else (15, log2Size - 2)
  let elem := if axis == 0 then elemLastSigXPrefix else elemLastSigYPrefix
  let base := hevcCabacElemOffset.getD elem 0
  let mut w := w0
  let mut st := st0
  for i in [:pref] do
    let (w', st') := w.encodeDecision st (base + (i >>> ctxShift) + ctxOffset) 1
    w := w'
    st := st'
  if pref < maxPref then
    let (w', st') := w.encodeDecision st (base + (pref >>> ctxShift) + ctxOffset) 0
    w := w'
    st := st'
  return (w, st)

def encRemaining (w0 : HevcCabacWriter) (val rice : Nat) : HevcCabacWriter := Id.run do
  let mut w := w0
  if val < (3 <<< rice) then
    let prefLen := val >>> rice
    for _ in [:prefLen] do
      w := w.encodeBypass 1
    w := w.encodeBypass 0
    w := w.encodeBypassBits (val &&& ((1 <<< rice) - 1)) rice
  else
    let mut prefLen := 3
    let mut rest := val - (3 <<< rice)
    let mut fuel := 32
    while rest >= (1 <<< (prefLen - 3 + rice)) && fuel > 0 do
      fuel := fuel - 1
      rest := rest - (1 <<< (prefLen - 3 + rice))
      prefLen := prefLen + 1
    for _ in [:prefLen] do
      w := w.encodeBypass 1
    w := w.encodeBypass 0
    w := w.encodeBypassBits rest (prefLen - 3 + rice)
  return w

def encResidual (w0 : HevcCabacWriter) (st0 : Array Nat) (levels : Array Int)
    (log2Size scanIdx cIdx : Nat) : HevcCabacWriter × Array Nat := Id.run do
  let size := 1 <<< log2Size
  let (sxCg, syCg, sxOff, syOff) := getScanTables log2Size scanIdx
  let cgSide := 1 <<< (log2Size - 2)
  let mut lastCg := 0
  let mut lastX := 0
  let mut lastY := 0
  let mut found := false
  let numCg := cgSide * cgSide
  let mut ci := numCg
  while ci > 0 && !found do
    ci := ci - 1
    let mut ni := 16
    while ni > 0 && !found do
      ni := ni - 1
      let xC := (sxCg.getD ci 0 <<< 2) + sxOff.getD ni 0
      let yC := (syCg.getD ci 0 <<< 2) + syOff.getD ni 0
      if levels.getD (yC * size + xC) 0 != 0 then
        lastCg := ci
        lastX := xC
        lastY := yC
        found := true
  let (lxWire, lyWire) := if scanIdx == scanVert then (lastY, lastX) else (lastX, lastY)
  let (px, pxBits, pxSuff) := lastPrefixEncode lxWire
  let (py, pyBits, pySuff) := lastPrefixEncode lyWire
  let (w1, st1) := encLastPrefix w0 st0 log2Size cIdx 0 px
  let (w2, st2) := encLastPrefix w1 st1 log2Size cIdx 1 py
  let mut w := w2
  let mut st := st2
  if px > 3 then w := w.encodeBypassBits pxSuff pxBits
  if py > 3 then w := w.encodeBypassBits pySuff pyBits
  let mut sigCg : Array (Array Nat) := Array.replicate cgSide (Array.replicate cgSide 0)
  sigCg := sigCg.set! (lastY >>> 2) ((sigCg.getD (lastY >>> 2) #[]).set! (lastX >>> 2) 1)
  let mut greater1Ctx := 1
  let mut i := lastCg
  let mut fuel := lastCg + 1
  while fuel > 0 do
    fuel := fuel - 1
    let xCg := sxCg.getD i 0
    let yCg := syCg.getD i 0
    let mut coded := false
    for n in [:16] do
      let xC := (xCg <<< 2) + sxOff.getD n 0
      let yC := (yCg <<< 2) + syOff.getD n 0
      if levels.getD (yC * size + xC) 0 != 0 then coded := true
    if i < lastCg && i > 0 then
      let mut ctxCg := 0
      if xCg < cgSide - 1 then ctxCg := ctxCg ||| (sigCg.getD yCg #[]).getD (xCg + 1) 0
      if yCg < cgSide - 1 then ctxCg := ctxCg ||| (sigCg.getD (yCg + 1) #[]).getD xCg 0
      let inc := ctxCg + (if cIdx != 0 then 2 else 0)
      let (w', st') := w.encodeDecision st
        (hevcCabacElemOffset.getD elemSigCoeffGroupFlag 0 + inc) (if coded then 1 else 0)
      w := w'
      st := st'
    else if i == 0 then
      coded := true
    if coded then
      sigCg := sigCg.set! yCg ((sigCg.getD yCg #[]).set! xCg 1)
      let mut prevSig := 0
      if xCg < cgSide - 1 && (sigCg.getD yCg #[]).getD (xCg + 1) 0 != 0 then prevSig := prevSig ||| 1
      if yCg < cgSide - 1 && (sigCg.getD (yCg + 1) #[]).getD xCg 0 != 0 then prevSig := prevSig ||| 2
      let mut nEnd := 15
      if i == lastCg then
        let lx4 := lastX &&& 3
        let ly4 := lastY &&& 3
        nEnd :=
          if scanIdx == scanDiag then (hevcDiagScan4x4Inv.getD ly4 #[]).getD lx4 0
          else if scanIdx == scanHoriz then ly4 * 4 + lx4
          else lx4 * 4 + ly4
      let mut nz : Array Nat := #[]
      if i == lastCg then nz := nz.push nEnd
      let mut implicit := if i == lastCg then 0 else if i > 0 then 1 else 0
      let start := if i == lastCg then (if nEnd == 0 then 0 else nEnd - 1) else 15
      let mut nFuel := if i == lastCg && nEnd == 0 then 0 else start + 1
      let mut n := start
      while nFuel > 0 do
        nFuel := nFuel - 1
        let mut sig := 0
        if n == 0 && implicit != 0 then sig := 1
        else
          let inc := sigCoeffCtxInc log2Size cIdx scanIdx xCg yCg prevSig
            (sxOff.getD n 0) (syOff.getD n 0)
          let lv := levels.getD (((yCg <<< 2) + syOff.getD n 0) * size + (xCg <<< 2) + sxOff.getD n 0) 0
          sig := if lv != 0 then 1 else 0
          let (w', st') := w.encodeDecision st
            (hevcCabacElemOffset.getD elemSigCoeffFlag 0 + inc) sig
          w := w'
          st := st'
          if sig != 0 then implicit := 0
        if sig != 0 then nz := nz.push n
        if n == 0 then break
        n := n - 1
      let numNz := nz.size
      if numNz != 0 then
        let mut ctxSet := if i > 0 && cIdx == 0 then 2 else 0
        if i != lastCg && greater1Ctx == 0 then ctxSet := ctxSet + 1
        greater1Ctx := 1
        let gt1Base := hevcCabacElemOffset.getD elemCoeffAbsLevelGt1 0 + (ctxSet <<< 2) +
          (if cIdx != 0 then 16 else 0)
        let mut gt1 : Array Nat := Array.replicate numNz 0
        let mut firstGt1 : Int := -1
        let lim8 := if numNz < 8 then numNz else 8
        for m in [:lim8] do
          let nPos := nz.getD m 0
          let lv := (levels.getD (((yCg <<< 2) + syOff.getD nPos 0) * size +
            (xCg <<< 2) + sxOff.getD nPos 0) 0).natAbs
          let g1 := if lv > 1 then 1 else 0
          let (w', st') := w.encodeDecision st (gt1Base + greater1Ctx) g1
          w := w'
          st := st'
          gt1 := gt1.set! m g1
          if g1 != 0 then
            greater1Ctx := 0
            if firstGt1 == -1 then firstGt1 := m
          else if greater1Ctx > 0 && greater1Ctx < 3 then
            greater1Ctx := greater1Ctx + 1
        let mut gt2 := 0
        if firstGt1 != -1 then
          let nPos := nz.getD firstGt1.toNat 0
          let lv := (levels.getD (((yCg <<< 2) + syOff.getD nPos 0) * size +
            (xCg <<< 2) + sxOff.getD nPos 0) 0).natAbs
          gt2 := if lv > 2 then 1 else 0
          let (w', st') := w.encodeDecision st
            (hevcCabacElemOffset.getD elemCoeffAbsLevelGt2 0 + ctxSet + (if cIdx != 0 then 4 else 0)) gt2
          w := w'
          st := st'
        let mut signs := 0
        for m in [:numNz] do
          let nPos := nz.getD m 0
          let lv := levels.getD (((yCg <<< 2) + syOff.getD nPos 0) * size +
            (xCg <<< 2) + sxOff.getD nPos 0) 0
          signs := (signs <<< 1) ||| (if lv < 0 then 1 else 0)
        w := w.encodeBypassBits signs numNz
        let mut rice := 0
        for m in [:numNz] do
          let nPos := nz.getD m 0
          let lv := (levels.getD (((yCg <<< 2) + syOff.getD nPos 0) * size +
            (xCg <<< 2) + sxOff.getD nPos 0) 0).natAbs
          let base :=
            if m >= 8 then 1
            else 1 + gt1.getD m 0 + (if m == firstGt1.toNat && firstGt1 >= 0 then gt2 else 0)
          let need := m >= 8 ||
            (gt1.getD m 0 != 0 && !(m == firstGt1.toNat && firstGt1 >= 0 && gt2 == 0))
          if need then
            w := encRemaining w (lv - base) rice
            if lv > (3 <<< rice) then rice := if rice + 1 < 4 then rice + 1 else 4
    if i == 0 then break
    i := i - 1
  return (w, st)

def encEg1 (w0 : HevcCabacWriter) (val : Nat) : HevcCabacWriter := Id.run do
  let mut w := w0
  let mut k := 1
  let mut base := 2
  while k < 17 && val >= base + (1 <<< k) do
    w := w.encodeBypass 1
    base := base + (1 <<< k)
    k := k + 1
  w := w.encodeBypass 0
  let rem := val - base
  while k > 0 do
    k := k - 1
    w := w.encodeBypass ((rem >>> k) &&& 1)
  return w

def encMvd (w0 : HevcCabacWriter) (st0 : Array Nat) (mx my : Int) :
    HevcCabacWriter × Array Nat := Id.run do
  let base0 := hevcCabacElemOffset.getD elemAbsMvdGreater0 0
  let base1 := hevcCabacElemOffset.getD elemAbsMvdGreater1 0 + 1
  let (w1, st1) := w0.encodeDecision st0 base0 (if mx != 0 then 1 else 0)
  let (w2, st2) := w1.encodeDecision st1 base0 (if my != 0 then 1 else 0)
  let mut w := w2
  let mut st := st2
  if mx != 0 then
    let (w', st') := w.encodeDecision st base1 (if mx.natAbs > 1 then 1 else 0)
    w := w'
    st := st'
  if my != 0 then
    let (w', st') := w.encodeDecision st base1 (if my.natAbs > 1 then 1 else 0)
    w := w'
    st := st'
  for v in [mx, my] do
    if v != 0 then
      if v.natAbs == 1 then
        w := w.encodeBypass (if v < 0 then 1 else 0)
      else
        w := encEg1 w v.natAbs
        w := w.encodeBypass (if v < 0 then 1 else 0)
  return (w, st)

def encMergeIdx (w0 : HevcCabacWriter) (st0 : Array Nat) (idx maxCand : Nat) :
    HevcCabacWriter × Array Nat := Id.run do
  if maxCand <= 1 then return (w0, st0)
  let base := hevcCabacElemOffset.getD elemMergeIdx 0
  if idx == 0 then
    return w0.encodeDecision st0 base 0
  let (w1, st1) := w0.encodeDecision st0 base 1
  let mut w := w1
  let mut i := 1
  while i < maxCand - 1 do
    let b := if i < idx then 1 else 0
    w := w.encodeBypass b
    if b == 0 then break
    i := i + 1
  return (w, st1)

def pfIntra : Nat := 4
def pfL0 : Nat := 1
def pfL1 : Nat := 2
def pfBi : Nat := 3

def hevcSaoEdgeIdx : Array Nat := #[1, 2, 0, 3, 4]
def hevcSaoEoPos : Array ((Int × Int) × (Int × Int)) := #[
  ((-1, 0), (1, 0)),
  ((0, -1), (0, 1)),
  ((-1, -1), (1, 1)),
  ((1, -1), (-1, 1))
]

def hevcQpelFilters : Array (Array Int) := #[
  #[0, 0, 0, 64, 0, 0, 0, 0],
  #[-1, 4, -10, 58, 17, -5, 1, 0],
  #[-1, 4, -11, 40, 40, -11, 4, -1],
  #[0, 1, -5, 17, 58, -10, 4, -1]
]

def hevcEpelFilters : Array (Array Int) := #[
  #[0, 64, 0, 0],
  #[-2, 58, 10, -2],
  #[-4, 54, 16, -2],
  #[-6, 46, 28, -4],
  #[-4, 36, 36, -4],
  #[-4, 28, 46, -6],
  #[-2, 16, 54, -4],
  #[-2, 10, 58, -2]
]

def hevcDst4Matrix : Array (Array Int) := #[
  #[29, 55, 74, 84],
  #[74, 74, 0, -74],
  #[84, -29, -74, 55],
  #[55, -84, 74, -29]
]

def hevcQuantScale : Array Int := #[26214, 23302, 20560, 18396, 16384, 14564]

@[inline]
def clipInt16 (v : Int) : Int :=
  clipInt v (-32768) 32767

def mapQpC (qpI : Int) : Int :=
  if qpI < 0 then 0
  else if qpI < 30 then qpI
  else if qpI <= 43 then hevcQpC.getD (qpI - 30).toNat 29
  else if qpI > 57 then 51
  else qpI - 6

def transformSkip8 (coeffs : Array Int) (log2Size : Nat) : Array Int := Id.run do
  let size := 1 <<< log2Size
  let mut out : Array Int := Array.replicate (size * size) 0
  if log2Size < 7 then
    let sh := 7 - log2Size
    let off := Int.ofNat (1 <<< (sh - 1))
    for i in [:coeffs.size] do
      out := out.set! i (clipInt16 (asrInt (coeffs.getD i 0 + off) sh))
  else
    for i in [:coeffs.size] do
      out := out.set! i (clipInt16 (coeffs.getD i 0))
  return out

def dst4Pass1D (buf0 : Array Int) (base step : Nat) (add : Int) (shift : Nat) : Array Int :=
  let s0 := buf0.getD base 0
  let s1 := buf0.getD (base + step) 0
  let s2 := buf0.getD (base + 2 * step) 0
  let s3 := buf0.getD (base + 3 * step) 0
  let c0 := s0 + s2
  let c1 := s2 + s3
  let c2 := s0 - s3
  let c3 := 74 * s1
  let b1 := buf0.set! (base + 2 * step) (clipInt16 (asrInt (74 * (s0 - s2 + s3) + add) shift))
  let b2 := b1.set! base (clipInt16 (asrInt (29 * c0 + 55 * c1 + c3 + add) shift))
  let b3 := b2.set! (base + step) (clipInt16 (asrInt (55 * c2 - 29 * c1 + c3 + add) shift))
  b3.set! (base + 3 * step) (clipInt16 (asrInt (55 * c0 + 29 * c2 - c3 + add) shift))

def transform4x4Luma (coeffs : Array Int) : Array Int := Id.run do
  let mut buf := coeffs
  for x in [:4] do
    buf := dst4Pass1D buf x 4 64 7
  for y in [:4] do
    buf := dst4Pass1D buf (y * 4) 1 2048 12
  return buf

def idctTr4 (src : Array Int) (base step : Nat) : Array Int :=
  let s0 := src.getD base 0
  let s1 := src.getD (base + step) 0
  let s2 := src.getD (base + 2 * step) 0
  let s3 := src.getD (base + 3 * step) 0
  let e0 := 64 * s0 + 64 * s2
  let e1 := 64 * s0 - 64 * s2
  let o0 := 83 * s1 + 36 * s3
  let o1 := 36 * s1 - 83 * s3
  #[e0 + o0, e1 + o1, e1 - o1, e0 - o0]

def idctTr8 (src : Array Int) (base step : Nat) : Array Int := Id.run do
  let e8 := idctTr4 src base (2 * step)
  let mut o8 : Array Int := #[0, 0, 0, 0]
  for j in [1, 3, 5, 7] do
    let sj := src.getD (base + j * step) 0
    if sj != 0 then
      let row := hevcDspTransform.getD (4 * j) #[]
      for i in [:4] do
        o8 := o8.set! i (o8.getD i 0 + row.getD i 0 * sj)
  let mut out : Array Int := Array.replicate 8 0
  for i in [:4] do
    let ei := e8.getD i 0
    let oi := o8.getD i 0
    out := out.set! i (ei + oi)
    out := out.set! (7 - i) (ei - oi)
  return out

def idctTr16 (src : Array Int) (base step : Nat) : Array Int := Id.run do
  let e16 := idctTr8 src base (2 * step)
  let mut o16 : Array Int := Array.replicate 8 0
  let mut j := 1
  while j < 16 do
    let sj := src.getD (base + j * step) 0
    if sj != 0 then
      let row := hevcDspTransform.getD (2 * j) #[]
      for i in [:8] do
        o16 := o16.set! i (o16.getD i 0 + row.getD i 0 * sj)
    j := j + 2
  let mut out : Array Int := Array.replicate 16 0
  for i in [:8] do
    let ei := e16.getD i 0
    let oi := o16.getD i 0
    out := out.set! i (ei + oi)
    out := out.set! (15 - i) (ei - oi)
  return out

def idctTr32 (src : Array Int) (base step : Nat) : Array Int := Id.run do
  let e32 := idctTr16 src base (2 * step)
  let mut o32 : Array Int := Array.replicate 16 0
  let mut j := 1
  while j < 32 do
    let sj := src.getD (base + j * step) 0
    if sj != 0 then
      let row := hevcDspTransform.getD j #[]
      for i in [:16] do
        o32 := o32.set! i (o32.getD i 0 + row.getD i 0 * sj)
    j := j + 2
  let mut out : Array Int := Array.replicate 32 0
  for i in [:16] do
    let ei := e32.getD i 0
    let oi := o32.getD i 0
    out := out.set! i (ei + oi)
    out := out.set! (31 - i) (ei - oi)
  return out

def idctDc8 (c0 : Int) (size : Nat) : Array Int :=
  let val := clipInt16 (asrInt (asrInt (c0 + 1) 1 + 32) 6)
  Array.replicate (size * size) val

def idctBlock8 (coeffs : Array Int) (log2Size : Nat) : Array Int := Id.run do
  let size := 1 <<< log2Size
  let mut buf := coeffs
  let tr1d (b : Array Int) (base step : Nat) : Array Int :=
    if size == 4 then idctTr4 b base step
    else if size == 8 then idctTr8 b base step
    else if size == 16 then idctTr16 b base step
    else idctTr32 b base step
  for x in [:size] do
    let col := tr1d buf x size
    for y in [:size] do
      buf := buf.set! (y * size + x) (clipInt16 (asrInt (col.getD y 0 + 64) 7))
  for y in [:size] do
    let base := y * size
    let row := tr1d buf base 1
    for x in [:size] do
      buf := buf.set! (base + x) (clipInt16 (asrInt (row.getD x 0 + 2048) 12))
  return buf

def inverseTransformAndAdd (plane0 : ByteArray) (stride dstX dstY : Nat)
    (coeffs : Array Int) (log2Size cIdx : Nat) (isIntra : Bool)
    (transformSkip cuTransquantBypass maxXY : Nat) : ByteArray := Id.run do
  let size := 1 <<< log2Size
  let res : Array Int :=
    if cuTransquantBypass != 0 then coeffs
    else if transformSkip != 0 then transformSkip8 coeffs log2Size
    else if isIntra && cIdx == 0 && log2Size == 2 then transform4x4Luma coeffs
    else if maxXY == 0 then idctDc8 (coeffs.getD 0 0) size
    else idctBlock8 coeffs log2Size
  let mut plane := plane0
  for y in [:size] do
    let rowOff := (dstY + y) * stride + dstX
    let rOff := y * size
    for x in [:size] do
      let cur := Int.ofNat (baGetD plane (rowOff + x) 0).toNat
      plane := plane.set! (rowOff + x) (clipU8Int (cur + res.getD (rOff + x) 0))
  return plane

def fdst4Pass1D (src : Array Int) (base step shift : Nat) : Array Int := Id.run do
  let add := if shift == 0 then (0 : Int) else Int.ofNat (1 <<< (shift - 1))
  let mut out : Array Int := Array.replicate 4 0
  for i in [:4] do
    let row := hevcDst4Matrix.getD i #[]
    let mut acc : Int := 0
    for k in [:4] do
      acc := acc + row.getD k 0 * src.getD (base + k * step) 0
    out := out.set! i (asrInt (acc + add) shift)
  return out

def fdctPass1D (src : Array Int) (base step size shift : Nat) : Array Int := Id.run do
  let add := if shift == 0 then (0 : Int) else Int.ofNat (1 <<< (shift - 1))
  let stride := 32 / size
  let mut out : Array Int := Array.replicate size 0
  for i in [:size] do
    let row := hevcDspTransform.getD (i * stride) #[]
    let mut acc : Int := 0
    for j in [:size] do
      acc := acc + row.getD j 0 * src.getD (base + j * step) 0
    out := out.set! i (asrInt (acc + add) shift)
  return out

def forwardTransform (res : Array Int) (log2Size : Nat) (isDst : Bool) : Array Int := Id.run do
  let size := 1 <<< log2Size
  let sh1 := log2Size - 1
  let sh2 := log2Size + 6
  let mut tmp : Array Int := Array.replicate (size * size) 0
  for x in [:size] do
    let col := if isDst then fdst4Pass1D res x size sh1 else fdctPass1D res x size size sh1
    for y in [:size] do
      tmp := tmp.set! (y * size + x) (col.getD y 0)
  let mut out : Array Int := Array.replicate (size * size) 0
  for y in [:size] do
    let row := if isDst then fdst4Pass1D tmp (y * size) 1 sh2 else fdctPass1D tmp (y * size) 1 size sh2
    for x in [:size] do
      out := out.set! (y * size + x) (row.getD x 0)
  return out

def quantizeCoeffs (coeffs : Array Int) (log2Size : Nat) (qp : Int) (intra : Bool) : Array Int := Id.run do
  let qS := hevcQuantScale.getD (qp.toNat % 6) 16384
  let shift := 21 + (qp.toNat / 6) - log2Size
  let oneSh := Int.ofNat (1 <<< shift)
  let offset := if intra then oneSh / 3 else oneSh / 6
  let mut out : Array Int := Array.mkEmpty coeffs.size
  for c in coeffs do
    let mag := asrInt (Int.ofNat c.natAbs * qS + offset) shift
    out := out.push (if c < 0 then -mag else mag)
  return out

def dequantLevels (levels : Array Int) (log2Size : Nat) (qp : Int) : Array Int := Id.run do
  let shift := log2Size + 3
  let add := Int.ofNat (1 <<< (shift - 1))
  let scale := (hevcLevelScale.getD (qp.toNat % 6) 40) * Int.ofNat (1 <<< (qp.toNat / 6))
  let mut out : Array Int := Array.mkEmpty levels.size
  for lv in levels do
    out := out.push (clipInt16 (asrInt (lv * scale * 16 + add) shift))
  return out

structure HevcMvf where
  predFlag : Nat := 0
  refIdx0  : Int := -1
  refIdx1  : Int := -1
  mv0      : Int × Int := (0, 0)
  mv1      : Int × Int := (0, 0)
  deriving Repr, DecidableEq, Inhabited

def mvfZero : HevcMvf := {}
def mvfIntra : HevcMvf := { predFlag := pfIntra }

def mvfRefIdx (m : HevcMvf) (lx : Nat) : Int :=
  if lx == 0 then m.refIdx0 else m.refIdx1

def mvfMv (m : HevcMvf) (lx : Nat) : Int × Int :=
  if lx == 0 then m.mv0 else m.mv1

def mvfSet (m : HevcMvf) (lx : Nat) (ridx : Int) (mv : Int × Int) : HevcMvf :=
  if lx == 0 then { m with refIdx0 := ridx, mv0 := mv }
  else { m with refIdx1 := ridx, mv1 := mv }

structure HevcNeighAvail where
  candUp         : Bool := false
  candLeft       : Bool := false
  candUpLeft     : Bool := false
  candUpRightSap : Bool := false
  candUpRight    : Bool := false
  candBottomLeft : Bool := false
  deriving Repr, DecidableEq, Inhabited

def intraPred8 (plane0 : ByteArray) (stride : Nat) (sps : HevcSps) (pps : HevcPps)
    (tabMvf : Array HevcMvf) (na : HevcNeighAvail) (x0 y0 log2Size cIdx mode : Nat) :
    ByteArray := Id.run do
  let hshift := if cIdx == 0 then 0 else 1
  let vshift := if cIdx == 0 then 0 else 1
  let size := 1 <<< log2Size
  let sizeInLumaH := size <<< hshift
  let sizeInLumaV := size <<< vshift
  let log2MinTb := sps.log2MinTbSize
  let tbMask := sps.tbMask
  let sizeInTbsH := sizeInLumaH >>> log2MinTb
  let sizeInTbsV := sizeInLumaV >>> log2MinTb
  let x := x0 >>> hshift
  let y := y0 >>> vshift
  let xTb := x0 >>> log2MinTb
  let yTb := y0 >>> log2MinTb
  let spin := if cIdx != 0 && sizeInTbsV == 0 && ((2 * y0) &&& (1 <<< log2MinTb)) != 0 then 1 else 0
  let curTbAddr := minTbAddrZs pps (Int.ofNat (xTb &&& tbMask)) (Int.ofNat (yTb &&& tbMask))
  let mut candLeft := na.candLeft
  let mut candUpLeft := na.candUpLeft
  let mut candUp := na.candUp
  let mut candBottomLeft := false
  if na.candBottomLeft then
    let ny := Int.ofNat ((yTb + sizeInTbsV + spin) &&& tbMask)
    let nx := Int.ofNat (xTb &&& tbMask) - 1
    if curTbAddr > minTbAddrZs pps nx ny then candBottomLeft := true
  let mut candUpRight := false
  if na.candUpRight && spin == 0 then
    let nx := Int.ofNat ((xTb + sizeInTbsH) &&& tbMask)
    let ny := Int.ofNat (yTb &&& tbMask) - 1
    if curTbAddr > minTbAddrZs pps nx ny then candUpRight := true
  let picW := sps.width
  let picH := sps.height
  let _ := spin
  let bottomLeftSize :=
    if y0 + sizeInLumaV >= picH then 0
    else (Nat.min (y0 + 2 * sizeInLumaV) picH - (y0 + sizeInLumaV)) >>> vshift
  let topRightSize :=
    if x0 + sizeInLumaH >= picW then 0
    else (Nat.min (x0 + 2 * sizeInLumaH) picW - (x0 + sizeInLumaH)) >>> hshift
  let log2MinPu := sps.log2MinPuSize
  let minPuW := sps.minPuWidth
  let minPuH := sps.minPuHeight
  let isIntraRel (rx ry : Int) : Bool :=
    let lx := Int.ofNat x0 + rx * Int.ofNat (1 <<< hshift)
    let ly := Int.ofNat y0 + ry * Int.ofNat (1 <<< vshift)
    if lx < 0 || ly < 0 then false
    else
      let px := lx.toNat >>> log2MinPu
      let py := ly.toNat >>> log2MinPu
      (tabMvf.getD (py * minPuW + px) mvfZero).predFlag == pfIntra
  let mut leftArr : Array Int := Array.replicate (2 * size + 1) 128
  let mut topArr : Array Int := Array.replicate (2 * size + 1) 128
  if pps.constrainedIntraPredFlag then
    let mut sizePuV := sizeInLumaV >>> log2MinPu
    let mut sizePuH := sizeInLumaH >>> log2MinPu
    if sizePuH == 0 then sizePuH := 1
    if sizePuV == 0 then sizePuV := 1
    let onPuEdgeX := (x0 &&& ((1 <<< log2MinPu) - 1)) == 0
    let onPuEdgeY := (y0 &&& ((1 <<< log2MinPu) - 1)) == 0
    if candBottomLeft && onPuEdgeX && x0 > 0 then
      let xLeftPu := (x0 - 1) >>> log2MinPu
      let yBotPu := (y0 + sizeInLumaV) >>> log2MinPu
      let mx := Nat.min sizePuV (minPuH - yBotPu)
      candBottomLeft := false
      let mut i := 0
      while i < mx do
        if (tabMvf.getD ((yBotPu + i) * minPuW + xLeftPu) mvfZero).predFlag == pfIntra then
          candBottomLeft := true
        i := i + 2
    if candLeft && onPuEdgeX && x0 > 0 then
      let xLeftPu := (x0 - 1) >>> log2MinPu
      let yLeftPu := y0 >>> log2MinPu
      let mx := Nat.min sizePuV (minPuH - yLeftPu)
      candLeft := false
      let mut i := 0
      while i < mx do
        if (tabMvf.getD ((yLeftPu + i) * minPuW + xLeftPu) mvfZero).predFlag == pfIntra then
          candLeft := true
        i := i + 2
    if candUpLeft && x0 > 0 && y0 > 0 then
      let xLeftPu := (x0 - 1) >>> log2MinPu
      let yTopPu := (y0 - 1) >>> log2MinPu
      candUpLeft := (tabMvf.getD (yTopPu * minPuW + xLeftPu) mvfZero).predFlag == pfIntra
    if candUp && onPuEdgeY && y0 > 0 then
      let xTopPu := x0 >>> log2MinPu
      let yTopPu := (y0 - 1) >>> log2MinPu
      let mx := Nat.min sizePuH (minPuW - xTopPu)
      candUp := false
      let mut i := 0
      while i < mx do
        if (tabMvf.getD (yTopPu * minPuW + xTopPu + i) mvfZero).predFlag == pfIntra then
          candUp := true
        i := i + 2
    if candUpRight && onPuEdgeY && y0 > 0 then
      let yTopPu := (y0 - 1) >>> log2MinPu
      let xRightPu := (x0 + sizeInLumaH) >>> log2MinPu
      let mx := Nat.min sizePuH (minPuW - xRightPu)
      candUpRight := false
      let mut i := 0
      while i < mx do
        if (tabMvf.getD (yTopPu * minPuW + xRightPu + i) mvfZero).predFlag == pfIntra then
          candUpRight := true
        i := i + 2
  if candUpLeft && x > 0 && y > 0 then
    let v := Int.ofNat (baGetD plane0 ((y - 1) * stride + (x - 1)) 128).toNat
    leftArr := leftArr.set! 0 v
    topArr := topArr.set! 0 v
  if candUp && y > 0 then
    let baseT := (y - 1) * stride + x
    for i in [:size] do
      topArr := topArr.set! (1 + i) (Int.ofNat (baGetD plane0 (baseT + i) 128).toNat)
  if candUpRight && y > 0 && topRightSize > 0 then
    let baseT := (y - 1) * stride + x
    for i in [:topRightSize] do
      topArr := topArr.set! (1 + size + i) (Int.ofNat (baGetD plane0 (baseT + size + i) 128).toNat)
    let extV := Int.ofNat (baGetD plane0 (baseT + size + topRightSize - 1) 128).toNat
    for i in [topRightSize:size] do
      topArr := topArr.set! (1 + size + i) extV
  if candLeft && x > 0 then
    for i in [:size] do
      leftArr := leftArr.set! (1 + i) (Int.ofNat (baGetD plane0 ((y + i) * stride + (x - 1)) 128).toNat)
  if candBottomLeft && x > 0 && bottomLeftSize > 0 then
    for i in [:bottomLeftSize] do
      leftArr := leftArr.set! (1 + size + i)
        (Int.ofNat (baGetD plane0 ((y + size + i) * stride + (x - 1)) 128).toNat)
    let extV := Int.ofNat (baGetD plane0 ((y + size + bottomLeftSize - 1) * stride + (x - 1)) 128).toNat
    for i in [bottomLeftSize:size] do
      leftArr := leftArr.set! (1 + size + i) extV
  if pps.constrainedIntraPredFlag &&
      (candBottomLeft || candLeft || candUpLeft || candUp || candUpRight) then
    let mut sizeMaxX :=
      if x0 + ((2 * size) <<< hshift) < picW then 2 * size else (picW - x0) >>> hshift
    let mut sizeMaxY :=
      if y0 + ((2 * size) <<< vshift) < picH then 2 * size else (picH - y0) >>> vshift
    if !candUpRight then
      sizeMaxX := if x0 + (size <<< hshift) < picW then size else (picW - x0) >>> hshift
    if !candBottomLeft then
      sizeMaxY := if y0 + (size <<< vshift) < picH then size else (picH - y0) >>> vshift
    let mut j : Int := Int.ofNat (size + (if candBottomLeft then bottomLeftSize else 0)) - 1
    if candBottomLeft || candLeft || candUpLeft then
      let mut fuel := (2 * size + 2)
      while j > -1 && !isIntraRel (-1) j && fuel > 0 do
        fuel := fuel - 1
        j := j - 1
      if !isIntraRel (-1) j then
        let mut jn := 0
        while jn < sizeMaxX && !isIntraRel (Int.ofNat jn) (-1) do
          jn := jn + 1
        let mut ii := jn + 1
        while ii > 0 do
          ii := ii - 1
          if !isIntraRel (Int.ofNat ii - 1) (-1) then
            topArr := topArr.set! ii (topArr.getD (ii + 1) 128)
        leftArr := leftArr.set! 0 (topArr.getD 0 128)
    else
      let mut jn := 0
      while jn < sizeMaxX && !isIntraRel (Int.ofNat jn) (-1) do
        jn := jn + 1
      if jn > 0 then
        let mut ii := jn
        while ii > 0 do
          if !isIntraRel (Int.ofNat ii - 1) (-1) then
            topArr := topArr.set! ii (topArr.getD (ii + 1) 128)
          ii := ii - 1
        topArr := topArr.set! 0 (topArr.getD 1 128)
      leftArr := leftArr.set! 0 (topArr.getD 0 128)
    leftArr := leftArr.set! 0 (topArr.getD 0 128)
    if candBottomLeft || candLeft then
      let mut aVal := leftArr.getD 0 128
      let mut i := 0
      while i < sizeMaxY do
        if !isIntraRel (-1) (Int.ofNat i) then
          for k in [:4] do
            if i + k < 2 * size then leftArr := leftArr.set! (1 + i + k) aVal
        else
          aVal := leftArr.getD (1 + Nat.min (i + 3) (2 * size - 1)) 128
        i := i + 4
    if !candLeft then
      for i in [:size] do
        leftArr := leftArr.set! (1 + i) (leftArr.getD 0 128)
    if !candBottomLeft then
      for i in [:size] do
        leftArr := leftArr.set! (1 + size + i) (leftArr.getD size 128)
    if x0 != 0 && y0 != 0 then
      if sizeMaxY > 0 then
        let mut aVal := leftArr.getD sizeMaxY 128
        let mut ii : Int := Int.ofNat sizeMaxY - 1
        let mut fuel := sizeMaxY + 2
        while ii >= 0 && fuel > 0 do
          fuel := fuel - 1
          if !isIntraRel (-1) (ii - 3) then
            for k in [:4] do
              let idxL := ii - 3 + Int.ofNat k
              if idxL >= 0 then leftArr := leftArr.set! (1 + idxL.toNat) aVal
          else
            let idxM := if ii - 3 > 0 then (ii - 3).toNat else 0
            aVal := leftArr.getD (1 + idxM) 128
          ii := ii - 4
      if !isIntraRel (-1) (-1) then leftArr := leftArr.set! 0 (leftArr.getD 1 128)
    else if x0 == 0 then
      for i in [:sizeMaxY] do
        leftArr := leftArr.set! (1 + i) 0
    else if sizeMaxY > 0 then
      let mut aVal := leftArr.getD sizeMaxY 128
      let mut ii : Int := Int.ofNat sizeMaxY - 1
      let mut fuel := sizeMaxY + 2
      while ii >= 0 && fuel > 0 do
        fuel := fuel - 1
        if !isIntraRel (-1) (ii - 3) then
          for k in [:4] do
            let idxL := ii - 3 + Int.ofNat k
            if idxL >= 0 then leftArr := leftArr.set! (1 + idxL.toNat) aVal
        else
          let idxM := if ii - 3 > 0 then (ii - 3).toNat else 0
          aVal := leftArr.getD (1 + idxM) 128
        ii := ii - 4
    topArr := topArr.set! 0 (leftArr.getD 0 128)
    if y0 != 0 then
      let mut aVal := leftArr.getD 0 128
      let mut i := 0
      while i < sizeMaxX do
        if !isIntraRel (Int.ofNat i) (-1) then
          for k in [:4] do
            if i + k < 2 * size then topArr := topArr.set! (1 + i + k) aVal
        else
          aVal := topArr.getD (1 + Nat.min (i + 3) (2 * size - 1)) 128
        i := i + 4
  if !candBottomLeft then
    if candLeft then
      let v := leftArr.getD size 128
      for i in [:size] do
        leftArr := leftArr.set! (1 + size + i) v
    else if candUpLeft then
      let v := leftArr.getD 0 128
      for i in [:2 * size] do
        leftArr := leftArr.set! (1 + i) v
      candLeft := true
    else if candUp then
      let v := topArr.getD 1 128
      leftArr := leftArr.set! 0 v
      for i in [:2 * size] do
        leftArr := leftArr.set! (1 + i) v
      candUpLeft := true
      candLeft := true
    else if candUpRight then
      let v := topArr.getD (1 + size) 128
      for i in [:size] do
        topArr := topArr.set! (1 + i) v
      leftArr := leftArr.set! 0 v
      for i in [:2 * size] do
        leftArr := leftArr.set! (1 + i) v
      candUp := true
      candUpLeft := true
      candLeft := true
    else
      leftArr := leftArr.set! 0 128
      for i in [:2 * size] do
        topArr := topArr.set! (1 + i) 128
        leftArr := leftArr.set! (1 + i) 128
  if !candLeft then
    let v := leftArr.getD (1 + size) 128
    for i in [:size] do
      leftArr := leftArr.set! (1 + i) v
  if !candUpLeft then
    leftArr := leftArr.set! 0 (leftArr.getD 1 128)
  if !candUp then
    let v := leftArr.getD 0 128
    for i in [:size] do
      topArr := topArr.set! (1 + i) v
  if !candUpRight then
    let v := topArr.getD size 128
    for i in [:size] do
      topArr := topArr.set! (1 + size + i) v
  topArr := topArr.set! 0 (leftArr.getD 0 128)
  if cIdx == 0 && mode != 1 && size != 4 then
    let d1 := (Int.ofNat mode - 26).natAbs
    let d2 := (Int.ofNat mode - 10).natAbs
    let minDist := Nat.min d1 d2
    if minDist > hevcIntraHorVerDistThresh.getD (log2Size - 3) 0 then
      let t0 := topArr.getD 0 128
      let t32 := topArr.getD 32 128
      let t64 := topArr.getD 64 128
      let l0 := leftArr.getD 0 128
      let l32 := leftArr.getD 32 128
      let l64 := leftArr.getD 64 128
      if sps.spsStrongIntraSmoothingEnableFlag && log2Size == 5 &&
          (t0 + t64 - 2 * t32).natAbs < 8 && (l0 + l64 - 2 * l32).natAbs < 8 then
        let mut fTop : Array Int := Array.replicate (2 * size + 1) 0
        let mut fLeft : Array Int := Array.replicate (2 * size + 1) 0
        fTop := fTop.set! 0 t0
        fTop := fTop.set! 64 t64
        fLeft := fLeft.set! 0 l0
        fLeft := fLeft.set! 64 l64
        for i in [:63] do
          let k := Int.ofNat (i + 1)
          fTop := fTop.set! (1 + i) (asrInt ((64 - k) * t0 + k * t64 + 32) 6)
          fLeft := fLeft.set! (1 + i) (asrInt ((64 - k) * l0 + k * l64 + 32) 6)
        topArr := fTop
        leftArr := fLeft
      else
        let mut fTop : Array Int := Array.replicate (2 * size + 1) 0
        let mut fLeft : Array Int := Array.replicate (2 * size + 1) 0
        fLeft := fLeft.set! (2 * size) (leftArr.getD (2 * size) 128)
        fTop := fTop.set! (2 * size) (topArr.getD (2 * size) 128)
        for idx in [:2 * size - 1] do
          let i := 2 * size - 2 - idx
          fLeft := fLeft.set! (1 + i)
            (asrInt (leftArr.getD (2 + i) 128 + 2 * leftArr.getD (1 + i) 128 + leftArr.getD i 128 + 2) 2)
          fTop := fTop.set! (1 + i)
            (asrInt (topArr.getD (2 + i) 128 + 2 * topArr.getD (1 + i) 128 + topArr.getD i 128 + 2) 2)
        let corner := asrInt (leftArr.getD 1 128 + 2 * leftArr.getD 0 128 + topArr.getD 1 128 + 2) 2
        fTop := fTop.set! 0 corner
        fLeft := fLeft.set! 0 corner
        topArr := fTop
        leftArr := fLeft
  let mut plane := plane0
  if mode == 0 then
    let topSz := topArr.getD (1 + size) 128
    let leftSz := leftArr.getD (1 + size) 128
    let sh := log2Size + 1
    let szI := Int.ofNat size
    for py in [:size] do
      let ly := leftArr.getD (1 + py) 128
      let rowOff := (y + py) * stride + x
      let pyI := Int.ofNat py
      for px in [:size] do
        let pxI := Int.ofNat px
        let v := asrInt ((szI - 1 - pxI) * ly + (pxI + 1) * topSz +
          (szI - 1 - pyI) * topArr.getD (1 + px) 128 + (pyI + 1) * leftSz + szI) sh
        plane := plane.set! (rowOff + px) (clipU8Int v)
  else if mode == 1 then
    let mut dc : Int := Int.ofNat size
    for i in [:size] do
      dc := dc + leftArr.getD (1 + i) 128 + topArr.getD (1 + i) 128
    dc := asrInt dc (log2Size + 1)
    let dcU8 := clipU8Int dc
    for py in [:size] do
      let rowOff := (y + py) * stride + x
      for px in [:size] do
        plane := plane.set! (rowOff + px) dcU8
    if cIdx == 0 && size < 32 then
      plane := plane.set! (y * stride + x)
        (clipU8Int (asrInt (leftArr.getD 1 128 + 2 * dc + topArr.getD 1 128 + 2) 2))
      for px in [1:size] do
        plane := plane.set! (y * stride + x + px)
          (clipU8Int (asrInt (topArr.getD (1 + px) 128 + 3 * dc + 2) 2))
      for py in [1:size] do
        plane := plane.set! ((y + py) * stride + x)
          (clipU8Int (asrInt (leftArr.getD (1 + py) 128 + 3 * dc + 2) 2))
  else
    let angle := hevcIntraPredAngle.getD (mode - 2) 0
    let last := asrInt (Int.ofNat size * angle) 5
    if mode >= 18 then
      let mut refBuf : Array Int := Array.replicate (3 * size + 4) 0
      if angle < 0 && last < -1 then
        for k in [:size + 1] do
          refBuf := refBuf.set! (size + k) (topArr.getD k 128)
        let inv := hevcInvAngle.getD (mode - 11) (-256)
        let nNeg := (-last).toNat
        for idx in [:nNeg] do
          let k : Int := last + Int.ofNat idx
          let lIdx := asrInt (k * inv + 128) 8
          refBuf := refBuf.set! (Int.ofNat size + k).toNat (leftArr.getD lIdx.toNat 128)
      else
        for k in [:2 * size + 1] do
          refBuf := refBuf.set! (size + k) (topArr.getD k 128)
      for py in [:size] do
        let prod := Int.ofNat (py + 1) * angle
        let idx := asrInt prod 5
        let fact := prod % 32
        let rowOff := (y + py) * stride + x
        if fact != 0 then
          let w0 := 32 - fact
          for px in [:size] do
            let rI := (Int.ofNat (size + px + 1) + idx).toNat
            let v := asrInt (w0 * refBuf.getD rI 128 + fact * refBuf.getD (rI + 1) 128 + 16) 5
            plane := plane.set! (rowOff + px) (clipU8Int v)
        else
          for px in [:size] do
            let rI := (Int.ofNat (size + px + 1) + idx).toNat
            plane := plane.set! (rowOff + px) (clipU8Int (refBuf.getD rI 128))
      if mode == 26 && cIdx == 0 && size < 32 then
        let t0 := topArr.getD 1 128
        let lm1 := leftArr.getD 0 128
        for py in [:size] do
          let v := t0 + asrInt (leftArr.getD (1 + py) 128 - lm1) 1
          plane := plane.set! ((y + py) * stride + x) (clipU8Int v)
    else
      let mut refBuf : Array Int := Array.replicate (3 * size + 4) 0
      if angle < 0 && last < -1 then
        for k in [:size + 1] do
          refBuf := refBuf.set! (size + k) (leftArr.getD k 128)
        let inv := hevcInvAngle.getD (mode - 11) (-256)
        let nNeg := (-last).toNat
        for idx in [:nNeg] do
          let k : Int := last + Int.ofNat idx
          let tIdx := asrInt (k * inv + 128) 8
          refBuf := refBuf.set! (Int.ofNat size + k).toNat (topArr.getD tIdx.toNat 128)
      else
        for k in [:2 * size + 1] do
          refBuf := refBuf.set! (size + k) (leftArr.getD k 128)
      for px in [:size] do
        let prod := Int.ofNat (px + 1) * angle
        let idx := asrInt prod 5
        let fact := prod % 32
        if fact != 0 then
          let w0 := 32 - fact
          for py in [:size] do
            let rI := (Int.ofNat (size + py + 1) + idx).toNat
            let v := asrInt (w0 * refBuf.getD rI 128 + fact * refBuf.getD (rI + 1) 128 + 16) 5
            plane := plane.set! ((y + py) * stride + x + px) (clipU8Int v)
        else
          for py in [:size] do
            let rI := (Int.ofNat (size + py + 1) + idx).toNat
            plane := plane.set! ((y + py) * stride + x + px) (clipU8Int (refBuf.getD rI 128))
      if mode == 10 && cIdx == 0 && size < 32 then
        let l0 := leftArr.getD 1 128
        let tm1 := topArr.getD 0 128
        let rowOff := y * stride + x
        for px in [:size] do
          let v := l0 + asrInt (topArr.getD (1 + px) 128 - tm1) 1
          plane := plane.set! (rowOff + px) (clipU8Int v)
  return plane

def mcLuma14Bit (refY : ByteArray) (picW picH : Nat) (xOff yOff : Int)
    (mx my bw bh : Nat) : Array Int := Id.run do
  let mut out : Array Int := Array.replicate (bw * bh) 0
  let maxX : Int := Int.ofNat picW - 1
  let maxY : Int := Int.ofNat picH - 1
  if mx == 0 && my == 0 then
    for py in [:bh] do
      let ry := (clipInt (yOff + Int.ofNat py) 0 maxY).toNat * picW
      let base := py * bw
      for px in [:bw] do
        let rx := (clipInt (xOff + Int.ofNat px) 0 maxX).toNat
        out := out.set! (base + px) (Int.ofNat ((baGetD refY (ry + rx) 0).toNat <<< 6))
    return out
  if my == 0 then
    let flt := hevcQpelFilters.getD mx #[]
    for py in [:bh] do
      let ry := (clipInt (yOff + Int.ofNat py) 0 maxY).toNat * picW
      let base := py * bw
      for px in [:bw] do
        let mut acc : Int := 0
        for k in [:8] do
          let rx := (clipInt (xOff + Int.ofNat px + Int.ofNat k - 3) 0 maxX).toNat
          acc := acc + flt.getD k 0 * Int.ofNat (baGetD refY (ry + rx) 0).toNat
        out := out.set! (base + px) acc
    return out
  if mx == 0 then
    let flt := hevcQpelFilters.getD my #[]
    for py in [:bh] do
      let base := py * bw
      let mut ys : Array Nat := Array.mkEmpty 8
      for k in [:8] do
        ys := ys.push ((clipInt (yOff + Int.ofNat py + Int.ofNat k - 3) 0 maxY).toNat * picW)
      for px in [:bw] do
        let rx := (clipInt (xOff + Int.ofNat px) 0 maxX).toNat
        let mut acc : Int := 0
        for k in [:8] do
          acc := acc + flt.getD k 0 * Int.ofNat (baGetD refY (ys.getD k 0 + rx) 0).toNat
        out := out.set! (base + px) acc
    return out
  let fh := hevcQpelFilters.getD mx #[]
  let fv := hevcQpelFilters.getD my #[]
  let tmpH := bh + 7
  let mut tmp : Array Int := Array.replicate (tmpH * bw) 0
  for ty in [:tmpH] do
    let ry := (clipInt (yOff + Int.ofNat ty - 3) 0 maxY).toNat * picW
    let tbase := ty * bw
    for px in [:bw] do
      let mut acc : Int := 0
      for k in [:8] do
        let rx := (clipInt (xOff + Int.ofNat px + Int.ofNat k - 3) 0 maxX).toNat
        acc := acc + fh.getD k 0 * Int.ofNat (baGetD refY (ry + rx) 0).toNat
      tmp := tmp.set! (tbase + px) acc
  for py in [:bh] do
    let base := py * bw
    for px in [:bw] do
      let mut acc : Int := 0
      for k in [:8] do
        acc := acc + fv.getD k 0 * tmp.getD ((py + k) * bw + px) 0
      out := out.set! (base + px) (asrInt acc 6)
  return out

def mcChroma14Bit (refC : ByteArray) (cw ch : Nat) (xOff yOff : Int)
    (mx my bw bh : Nat) : Array Int := Id.run do
  let mut out : Array Int := Array.replicate (bw * bh) 0
  let maxX : Int := Int.ofNat cw - 1
  let maxY : Int := Int.ofNat ch - 1
  if mx == 0 && my == 0 then
    for py in [:bh] do
      let ry := (clipInt (yOff + Int.ofNat py) 0 maxY).toNat * cw
      let base := py * bw
      for px in [:bw] do
        let rx := (clipInt (xOff + Int.ofNat px) 0 maxX).toNat
        out := out.set! (base + px) (Int.ofNat ((baGetD refC (ry + rx) 0).toNat <<< 6))
    return out
  if my == 0 then
    let flt := hevcEpelFilters.getD mx #[]
    for py in [:bh] do
      let ry := (clipInt (yOff + Int.ofNat py) 0 maxY).toNat * cw
      let base := py * bw
      for px in [:bw] do
        let mut acc : Int := 0
        for k in [:4] do
          let rx := (clipInt (xOff + Int.ofNat px + Int.ofNat k - 1) 0 maxX).toNat
          acc := acc + flt.getD k 0 * Int.ofNat (baGetD refC (ry + rx) 0).toNat
        out := out.set! (base + px) acc
    return out
  if mx == 0 then
    let flt := hevcEpelFilters.getD my #[]
    for py in [:bh] do
      let base := py * bw
      let mut ys : Array Nat := Array.mkEmpty 4
      for k in [:4] do
        ys := ys.push ((clipInt (yOff + Int.ofNat py + Int.ofNat k - 1) 0 maxY).toNat * cw)
      for px in [:bw] do
        let rx := (clipInt (xOff + Int.ofNat px) 0 maxX).toNat
        let mut acc : Int := 0
        for k in [:4] do
          acc := acc + flt.getD k 0 * Int.ofNat (baGetD refC (ys.getD k 0 + rx) 0).toNat
        out := out.set! (base + px) acc
    return out
  let fh := hevcEpelFilters.getD mx #[]
  let fv := hevcEpelFilters.getD my #[]
  let tmpH := bh + 3
  let mut tmp : Array Int := Array.replicate (tmpH * bw) 0
  for ty in [:tmpH] do
    let ry := (clipInt (yOff + Int.ofNat ty - 1) 0 maxY).toNat * cw
    let tbase := ty * bw
    for px in [:bw] do
      let mut acc : Int := 0
      for k in [:4] do
        let rx := (clipInt (xOff + Int.ofNat px + Int.ofNat k - 1) 0 maxX).toNat
        acc := acc + fh.getD k 0 * Int.ofNat (baGetD refC (ry + rx) 0).toNat
      tmp := tmp.set! (tbase + px) acc
  for py in [:bh] do
    let base := py * bw
    for px in [:bw] do
      let mut acc : Int := 0
      for k in [:4] do
        acc := acc + fv.getD k 0 * tmp.getD ((py + k) * bw + px) 0
      out := out.set! (base + px) (asrInt acc 6)
  return out

def mcUniWrite (dst0 : ByteArray) (stride dx dy bw bh : Nat) (s0 : Array Int)
    (weightFlag : Bool) (denom : Nat) (wx ox : Int) : ByteArray := Id.run do
  let mut dst := dst0
  if !weightFlag then
    for py in [:bh] do
      let roff := (dy + py) * stride + dx
      let boff := py * bw
      for px in [:bw] do
        dst := dst.set! (roff + px) (clipU8Int (asrInt (s0.getD (boff + px) 0 + 32) 6))
  else
    let shift := denom + 6
    let offset := Int.ofNat (1 <<< (shift - 1))
    for py in [:bh] do
      let roff := (dy + py) * stride + dx
      let boff := py * bw
      for px in [:bw] do
        dst := dst.set! (roff + px) (clipU8Int (asrInt (s0.getD (boff + px) 0 * wx + offset) shift + ox))
  return dst

def mcBiWrite (dst0 : ByteArray) (stride dx dy bw bh : Nat) (s0 s1 : Array Int)
    (weightFlag : Bool) (denom : Nat) (wx0 wx1 ox0 ox1 : Int) : ByteArray := Id.run do
  let mut dst := dst0
  if !weightFlag then
    for py in [:bh] do
      let roff := (dy + py) * stride + dx
      let boff := py * bw
      for px in [:bw] do
        dst := dst.set! (roff + px) (clipU8Int (asrInt (s0.getD (boff + px) 0 + s1.getD (boff + px) 0 + 64) 7))
  else
    let log2Wd := denom + 6
    let offBi := (ox0 + ox1 + 1) * Int.ofNat (1 <<< log2Wd)
    let shBi := log2Wd + 1
    for py in [:bh] do
      let roff := (dy + py) * stride + dx
      let boff := py * bw
      for px in [:bw] do
        dst := dst.set! (roff + px)
          (clipU8Int (asrInt (s0.getD (boff + px) 0 * wx0 + s1.getD (boff + px) 0 * wx1 + offBi) shBi))
  return dst

structure HevcRefPlanes where
  planes     : Array ByteArray := #[]
  poc        : Int := 0
  tabMvf     : Array HevcMvf := #[]
  rplPoc     : Array (Array Int) := #[#[], #[]]
  rplLt      : Array (Array Bool) := #[#[], #[]]
  rplTabPoc  : Array (Option (Array (Array Int))) := #[]
  rplTabLt   : Array (Option (Array (Array Bool))) := #[]
  deriving Inhabited

structure HevcRpl where
  refs : Array (Option HevcRefPlanes) := #[]
  poc  : Array Int := #[]
  lt   : Array Bool := #[]
  deriving Inhabited

def mcPu8 (planes0 : Array ByteArray) (sps : HevcSps) (pps : HevcPps) (sh : HevcSliceHeader)
    (mvf : HevcMvf) (rpl : Array HevcRpl) (x0 y0 nPbW nPbH : Nat) : Array ByteArray := Id.run do
  let picW := sps.width
  let picH := sps.height
  let cw := picW >>> 1
  let ch := picH >>> 1
  let pf := mvf.predFlag
  let weightFlag := (pps.weightedPredFlag && sh.sliceType == sliceP) ||
    (pps.weightedBipredFlag && sh.sliceType == sliceB)
  let wLuma (lx ridx : Nat) : Bool × Nat × Int × Int :=
    if !weightFlag then (false, 0, 1, 0)
    else
      match sh.pwt? with
      | none => (false, 0, 1, 0)
      | some pwt =>
        if lx == 0 then (true, pwt.lumaLog2WeightDenom, pwt.lumaWeightL0.getD ridx 1, pwt.lumaOffsetL0.getD ridx 0)
        else (true, pwt.lumaLog2WeightDenom, pwt.lumaWeightL1.getD ridx 1, pwt.lumaOffsetL1.getD ridx 0)
  let wChroma (lx ridx cI : Nat) : Bool × Nat × Int × Int :=
    if !weightFlag then (false, 0, 1, 0)
    else
      match sh.pwt? with
      | none => (false, 0, 1, 0)
      | some pwt =>
        if lx == 0 then
          (true, pwt.chromaLog2WeightDenom,
            (pwt.chromaWeightL0.getD ridx #[]).getD cI 1,
            (pwt.chromaOffsetL0.getD ridx #[]).getD cI 0)
        else
          (true, pwt.chromaLog2WeightDenom,
            (pwt.chromaWeightL1.getD ridx #[]).getD cI 1,
            (pwt.chromaOffsetL1.getD ridx #[]).getD cI 0)
  let mut planes := planes0
  let emptyY := ByteArray.mk (Array.replicate (picW * picH) 128)
  let emptyC := ByteArray.mk (Array.replicate (cw * ch) 128)
  if pf == pfL0 || pf == pfL1 then
    let lx := if pf == pfL0 then 0 else 1
    let ridx := (mvfRefIdx mvf lx).toNat
    let rplLx := rpl.getD lx {}
    let refOpt := rplLx.refs.getD ridx none
    let refY := match refOpt with | some rf => rf.planes.getD 0 emptyY | none => emptyY
    let (mvx, mvy) := mvfMv mvf lx
    let mx := (mvx % 4).toNat
    let my := (mvy % 4).toNat
    let sY := mcLuma14Bit refY picW picH (Int.ofNat x0 + asrInt mvx 2) (Int.ofNat y0 + asrInt mvy 2) mx my nPbW nPbH
    let (wfY, denomY, wy, oy) := wLuma lx ridx
    planes := planes.set! 0 (mcUniWrite (planes.getD 0 ByteArray.empty) picW x0 y0 nPbW nPbH sY wfY denomY wy oy)
    let cbw := nPbW >>> 1
    let cbh := nPbH >>> 1
    let cx0 := x0 >>> 1
    let cy0 := y0 >>> 1
    let cmx := (mvx % 8).toNat
    let cmy := (mvy % 8).toNat
    for cI in [:2] do
      let refC := match refOpt with | some rf => rf.planes.getD (cI + 1) emptyC | none => emptyC
      let sC := mcChroma14Bit refC cw ch (Int.ofNat cx0 + asrInt mvx 3) (Int.ofNat cy0 + asrInt mvy 3) cmx cmy cbw cbh
      let (wfC, denomC, wc, oc) := wChroma lx ridx cI
      planes := planes.set! (cI + 1)
        (mcUniWrite (planes.getD (cI + 1) ByteArray.empty) cw cx0 cy0 cbw cbh sC wfC denomC wc oc)
  else if pf == pfBi then
    let r0 := mvf.refIdx0.toNat
    let r1 := mvf.refIdx1.toNat
    let ref0 := (rpl.getD 0 {}).refs.getD r0 none
    let ref1 := (rpl.getD 1 {}).refs.getD r1 none
    let ref0Y := match ref0 with | some rf => rf.planes.getD 0 emptyY | none => emptyY
    let ref1Y := match ref1 with | some rf => rf.planes.getD 0 emptyY | none => emptyY
    let (mv0x, mv0y) := mvf.mv0
    let (mv1x, mv1y) := mvf.mv1
    let s0Y := mcLuma14Bit ref0Y picW picH (Int.ofNat x0 + asrInt mv0x 2) (Int.ofNat y0 + asrInt mv0y 2)
      (mv0x % 4).toNat (mv0y % 4).toNat nPbW nPbH
    let s1Y := mcLuma14Bit ref1Y picW picH (Int.ofNat x0 + asrInt mv1x 2) (Int.ofNat y0 + asrInt mv1y 2)
      (mv1x % 4).toNat (mv1y % 4).toNat nPbW nPbH
    let (wfY, denomY, wy0, oy0) := wLuma 0 r0
    let (_, _, wy1, oy1) := wLuma 1 r1
    planes := planes.set! 0
      (mcBiWrite (planes.getD 0 ByteArray.empty) picW x0 y0 nPbW nPbH s0Y s1Y wfY denomY wy0 wy1 oy0 oy1)
    let cbw := nPbW >>> 1
    let cbh := nPbH >>> 1
    let cx0 := x0 >>> 1
    let cy0 := y0 >>> 1
    for cI in [:2] do
      let ref0C := match ref0 with | some rf => rf.planes.getD (cI + 1) emptyC | none => emptyC
      let ref1C := match ref1 with | some rf => rf.planes.getD (cI + 1) emptyC | none => emptyC
      let s0C := mcChroma14Bit ref0C cw ch (Int.ofNat cx0 + asrInt mv0x 3) (Int.ofNat cy0 + asrInt mv0y 3)
        (mv0x % 8).toNat (mv0y % 8).toNat cbw cbh
      let s1C := mcChroma14Bit ref1C cw ch (Int.ofNat cx0 + asrInt mv1x 3) (Int.ofNat cy0 + asrInt mv1y 3)
        (mv1x % 8).toNat (mv1y % 8).toNat cbw cbh
      let (wfC, denomC, wc0, oc0) := wChroma 0 r0 cI
      let (_, _, wc1, oc1) := wChroma 1 r1 cI
      planes := planes.set! (cI + 1)
        (mcBiWrite (planes.getD (cI + 1) ByteArray.empty) cw cx0 cy0 cbw cbh s0C s1C wfC denomC wc0 wc1 oc0 oc1)
  return planes

structure HevcDeblockCtb where
  betaOffset : Int := 0
  tcOffset   : Int := 0
  deriving Repr, DecidableEq, Inhabited

structure HevcSaoCtb where
  typeIdx      : Array Nat := #[0, 0, 0]
  eoClass      : Array Nat := #[0, 0, 0]
  bandPosition : Array Nat := #[0, 0, 0]
  offsetVal    : Array (Array Int) := #[#[0, 0, 0, 0, 0], #[0, 0, 0, 0, 0], #[0, 0, 0, 0, 0]]
  deriving Repr, DecidableEq, Inhabited

@[inline]
private def rdPxI (plane : ByteArray) (idx : Nat) : Int :=
  Int.ofNat (baGetD plane idx 0).toNat

def loopFilterLuma8 (plane0 : ByteArray) (baseIdx xstride ystride : Nat) (beta : Int)
    (tcPair : Int × Int) (noPPair noQPair : Nat × Nat) : ByteArray := Id.run do
  let mut plane := plane0
  let mut idx := baseIdx
  for j in [:2] do
    let p3_0 := rdPxI plane (idx - 4 * xstride)
    let p2_0 := rdPxI plane (idx - 3 * xstride)
    let p1_0 := rdPxI plane (idx - 2 * xstride)
    let p0_0 := rdPxI plane (idx - 1 * xstride)
    let q0_0 := rdPxI plane idx
    let q1_0 := rdPxI plane (idx + 1 * xstride)
    let q2_0 := rdPxI plane (idx + 2 * xstride)
    let q3_0 := rdPxI plane (idx + 3 * xstride)
    let idx3 := idx + 3 * ystride
    let tp3 := rdPxI plane (idx3 - 4 * xstride)
    let tp2 := rdPxI plane (idx3 - 3 * xstride)
    let tp1 := rdPxI plane (idx3 - 2 * xstride)
    let tp0 := rdPxI plane (idx3 - 1 * xstride)
    let tq0 := rdPxI plane idx3
    let tq1 := rdPxI plane (idx3 + 1 * xstride)
    let tq2 := rdPxI plane (idx3 + 2 * xstride)
    let tq3 := rdPxI plane (idx3 + 3 * xstride)
    let dp0 := Int.ofNat (p2_0 - 2 * p1_0 + p0_0).natAbs
    let dq0 := Int.ofNat (q2_0 - 2 * q1_0 + q0_0).natAbs
    let dp3 := Int.ofNat (tp2 - 2 * tp1 + tp0).natAbs
    let dq3 := Int.ofNat (tq2 - 2 * tq1 + tq0).natAbs
    let d0 := dp0 + dq0
    let d3 := dp3 + dq3
    let tc := if j == 0 then tcPair.1 else tcPair.2
    let noP := if j == 0 then noPPair.1 else noPPair.2
    let noQ := if j == 0 then noQPair.1 else noQPair.2
    if d0 + d3 >= beta || tc <= 0 then
      idx := idx + 4 * ystride
    else
      let beta3 := asrInt beta 3
      let beta2 := asrInt beta 2
      let tc25 := asrInt (tc * 5 + 1) 1
      let s1 := Int.ofNat (p3_0 - p0_0).natAbs + Int.ofNat (q3_0 - q0_0).natAbs < beta3
      let s2 := Int.ofNat (p0_0 - q0_0).natAbs < tc25
      let s3 := Int.ofNat (tp3 - tp0).natAbs + Int.ofNat (tq3 - tq0).natAbs < beta3
      let s4 := Int.ofNat (tp0 - tq0).natAbs < tc25
      if s1 && s2 && s3 && s4 && (2 * d0) < beta2 && (2 * d3) < beta2 then
        let tc2 := 2 * tc
        for _ in [:4] do
          let p3 := rdPxI plane (idx - 4 * xstride)
          let p2 := rdPxI plane (idx - 3 * xstride)
          let p1 := rdPxI plane (idx - 2 * xstride)
          let p0 := rdPxI plane (idx - 1 * xstride)
          let q0 := rdPxI plane idx
          let q1 := rdPxI plane (idx + 1 * xstride)
          let q2 := rdPxI plane (idx + 2 * xstride)
          let q3 := rdPxI plane (idx + 3 * xstride)
          if noP == 0 then
            let np0 := p0 + clipInt (asrInt (p2 + 2 * p1 + 2 * p0 + 2 * q0 + q1 + 4) 3 - p0) (-tc2) tc2
            let np1 := p1 + clipInt (asrInt (p2 + p1 + p0 + q0 + 2) 2 - p1) (-tc2) tc2
            let np2 := p2 + clipInt (asrInt (2 * p3 + 3 * p2 + p1 + p0 + q0 + 4) 3 - p2) (-tc2) tc2
            plane := plane.set! (idx - 1 * xstride) (clipU8Int np0)
            plane := plane.set! (idx - 2 * xstride) (clipU8Int np1)
            plane := plane.set! (idx - 3 * xstride) (clipU8Int np2)
          if noQ == 0 then
            let nq0 := q0 + clipInt (asrInt (p1 + 2 * p0 + 2 * q0 + 2 * q1 + q2 + 4) 3 - q0) (-tc2) tc2
            let nq1 := q1 + clipInt (asrInt (p0 + q0 + q1 + q2 + 2) 2 - q1) (-tc2) tc2
            let nq2 := q2 + clipInt (asrInt (2 * q3 + 3 * q2 + q1 + q0 + p0 + 4) 3 - q2) (-tc2) tc2
            plane := plane.set! idx (clipU8Int nq0)
            plane := plane.set! (idx + 1 * xstride) (clipU8Int nq1)
            plane := plane.set! (idx + 2 * xstride) (clipU8Int nq2)
          idx := idx + ystride
      else
        let thr := asrInt (beta + asrInt beta 1) 3
        let ndP := if dp0 + dp3 < thr then 2 else 1
        let ndQ := if dq0 + dq3 < thr then 2 else 1
        let tcHalf := asrInt tc 1
        for _ in [:4] do
          let p2 := rdPxI plane (idx - 3 * xstride)
          let p1 := rdPxI plane (idx - 2 * xstride)
          let p0 := rdPxI plane (idx - 1 * xstride)
          let q0 := rdPxI plane idx
          let q1 := rdPxI plane (idx + 1 * xstride)
          let q2 := rdPxI plane (idx + 2 * xstride)
          let delta0Raw := asrInt (9 * (q0 - p0) - 3 * (q1 - p1) + 8) 4
          if Int.ofNat delta0Raw.natAbs < 10 * tc then
            let delta0 := clipInt delta0Raw (-tc) tc
            if noP == 0 then
              plane := plane.set! (idx - 1 * xstride) (clipU8Int (p0 + delta0))
            if noQ == 0 then
              plane := plane.set! idx (clipU8Int (q0 - delta0))
            if noP == 0 && ndP > 1 then
              let dp1 := clipInt (asrInt (asrInt (p2 + p0 + 1) 1 - p1 + delta0) 1) (-tcHalf) tcHalf
              plane := plane.set! (idx - 2 * xstride) (clipU8Int (p1 + dp1))
            if noQ == 0 && ndQ > 1 then
              let dq1 := clipInt (asrInt (asrInt (q2 + q0 + 1) 1 - q1 - delta0) 1) (-tcHalf) tcHalf
              plane := plane.set! (idx + 1 * xstride) (clipU8Int (q1 + dq1))
          idx := idx + ystride
  return plane

def loopFilterChroma8 (plane0 : ByteArray) (baseIdx xstride ystride : Nat)
    (tcPair : Int × Int) (noPPair noQPair : Nat × Nat) : ByteArray := Id.run do
  let mut plane := plane0
  let mut idx := baseIdx
  for j in [:2] do
    let tc := if j == 0 then tcPair.1 else tcPair.2
    if tc <= 0 then
      idx := idx + 4 * ystride
    else
      let noP := if j == 0 then noPPair.1 else noPPair.2
      let noQ := if j == 0 then noQPair.1 else noQPair.2
      for _ in [:4] do
        let p1 := rdPxI plane (idx - 2 * xstride)
        let p0 := rdPxI plane (idx - 1 * xstride)
        let q0 := rdPxI plane idx
        let q1 := rdPxI plane (idx + 1 * xstride)
        let delta0 := clipInt (asrInt (4 * (q0 - p0) + p1 - q1 + 4) 3) (-tc) tc
        if noP == 0 then
          plane := plane.set! (idx - 1 * xstride) (clipU8Int (p0 + delta0))
        if noQ == 0 then
          plane := plane.set! idx (clipU8Int (q0 - delta0))
        idx := idx + ystride
  return plane

@[inline]
private def evenFloorInt (x : Int) : Int :=
  asrInt x 1 * 2

def deblockFrame8 (planes0 : Array ByteArray) (sps : HevcSps) (pps : HevcPps)
    (qpYTab : Array Int) (isPcm : Array Nat) (deblockCtb : Array HevcDeblockCtb)
    (verticalBs horizontalBs : Array Nat) (bsWidth : Nat) : Array ByteArray := Id.run do
  let picW := sps.width
  let picH := sps.height
  let cw := picW >>> 1
  let log2Ctb := sps.log2CtbSize
  let ctbW := sps.ctbWidth
  let log2MinCb := sps.log2MinCbSize
  let minCbW := sps.minCbWidth
  let log2MinPu := sps.log2MinPuSize
  let minPuW := sps.minPuWidth
  let minPuH := sps.minPuHeight
  let pcmLoopDis := match sps.pcm? with | some p => p.loopFilterDisableFlag | none => false
  let pcmf := (sps.pcmEnabledFlag && pcmLoopDis) || pps.transquantBypassEnableFlag
  let cbOffPps := pps.cbQpOffset
  let crOffPps := pps.crQpOffset
  let getQpY (px py : Nat) : Int :=
    qpYTab.getD ((py >>> log2MinCb) * minCbW + (px >>> log2MinCb)) 26
  let getPcmF (px py : Nat) : Nat :=
    if !pcmf then 0
    else
      let xPu := px >>> log2MinPu
      let yPu := py >>> log2MinPu
      if xPu >= minPuW || yPu >= minPuH then 2
      else isPcm.getD (yPu * minPuW + xPu) 0
  let chromaTc (qp : Int) (cIdx : Nat) (tcOff : Int) : Int :=
    let off := if cIdx == 1 then cbOffPps else crOffPps
    let qpI := clipInt (qp + off) 0 57
    let qpc := mapQpC qpI
    hevcTcTable.getD (clipInt (qpc + 2 + tcOff) 0 53).toNat 0
  let mut planes := planes0
  let mut yPlane := planes.getD 0 ByteArray.empty
  let mut y := 0
  while y < picH do
    let mut x := 8
    while x < picW do
      let bs0 := verticalBs.getD ((x + y * bsWidth) >>> 2) 0
      let bs1 := verticalBs.getD ((x + (y + 4) * bsWidth) >>> 2) 0
      if bs0 != 0 || bs1 != 0 then
        let ctbIdx := (y >>> log2Ctb) * ctbW + (x >>> log2Ctb)
        let db := deblockCtb.getD ctbIdx {}
        let qp := asrInt (getQpY (x - 1) y + getQpY x y + 1) 1
        let beta := hevcBetaTable.getD (clipInt (qp + db.betaOffset) 0 51).toNat 0
        let tcEven := evenFloorInt db.tcOffset
        let tc0 := if bs0 != 0 then hevcTcTable.getD (clipInt (qp + 2 * (Int.ofNat bs0 - 1) + tcEven) 0 53).toNat 0 else 0
        let tc1 := if bs1 != 0 then hevcTcTable.getD (clipInt (qp + 2 * (Int.ofNat bs1 - 1) + tcEven) 0 53).toNat 0 else 0
        let np := (if bs0 != 0 then getPcmF (x - 1) y else 0, if bs1 != 0 then getPcmF (x - 1) (y + 4) else 0)
        let nq := (if bs0 != 0 then getPcmF x y else 0, if bs1 != 0 then getPcmF x (y + 4) else 0)
        yPlane := loopFilterLuma8 yPlane (y * picW + x) 1 picW beta (tc0, tc1) np nq
      x := x + 8
    y := y + 8
  y := 8
  while y < picH do
    let mut x := 0
    while x < picW do
      let bs0 := horizontalBs.getD ((x + y * bsWidth) >>> 2) 0
      let bs1 := horizontalBs.getD (((x + 4) + y * bsWidth) >>> 2) 0
      if bs0 != 0 || bs1 != 0 then
        let ctbIdx := (y >>> log2Ctb) * ctbW + (x >>> log2Ctb)
        let db := deblockCtb.getD ctbIdx {}
        let qp := asrInt (getQpY x (y - 1) + getQpY x y + 1) 1
        let beta := hevcBetaTable.getD (clipInt (qp + db.betaOffset) 0 51).toNat 0
        let tcEven := evenFloorInt db.tcOffset
        let tc0 := if bs0 != 0 then hevcTcTable.getD (clipInt (qp + 2 * (Int.ofNat bs0 - 1) + tcEven) 0 53).toNat 0 else 0
        let tc1 := if bs1 != 0 then hevcTcTable.getD (clipInt (qp + 2 * (Int.ofNat bs1 - 1) + tcEven) 0 53).toNat 0 else 0
        let np := (if bs0 != 0 then getPcmF x (y - 1) else 0, if bs1 != 0 then getPcmF (x + 4) (y - 1) else 0)
        let nq := (if bs0 != 0 then getPcmF x y else 0, if bs1 != 0 then getPcmF (x + 4) y else 0)
        yPlane := loopFilterLuma8 yPlane (y * picW + x) picW 1 beta (tc0, tc1) np nq
      x := x + 8
    y := y + 8
  planes := planes.set! 0 yPlane
  let ctbMask := (1 <<< log2Ctb) - 1
  for cIdx in [1, 2] do
    let mut cPlane := planes.getD cIdx ByteArray.empty
    let mut yc := 0
    while yc < picH do
      let mut xc := 16
      while xc < picW do
        let bs0 := verticalBs.getD ((xc + yc * bsWidth) >>> 2) 0
        let bs1 := verticalBs.getD ((xc + (yc + 8) * bsWidth) >>> 2) 0
        if bs0 == 2 || bs1 == 2 then
          let ctbIdx := (yc >>> log2Ctb) * ctbW + (xc >>> log2Ctb)
          let tcOff := (deblockCtb.getD ctbIdx {}).tcOffset
          let qp0 := if bs0 == 2 then asrInt (getQpY (xc - 1) yc + getQpY xc yc + 1) 1 else 0
          let qp1 := if bs1 == 2 then asrInt (getQpY (xc - 1) (yc + 8) + getQpY xc (yc + 8) + 1) 1 else 0
          let ctc0 := if bs0 == 2 then chromaTc qp0 cIdx tcOff else 0
          let ctc1 := if bs1 == 2 then chromaTc qp1 cIdx tcOff else 0
          let np := (if bs0 == 2 then getPcmF (xc - 1) yc else 0, if bs1 == 2 then getPcmF (xc - 1) (yc + 8) else 0)
          let nq := (if bs0 == 2 then getPcmF xc yc else 0, if bs1 == 2 then getPcmF xc (yc + 8) else 0)
          cPlane := loopFilterChroma8 cPlane ((yc >>> 1) * cw + (xc >>> 1)) 1 cw (ctc0, ctc1) np nq
        xc := xc + 16
      yc := yc + 16
    yc := 16
    while yc < picH do
      let mut xc := 0
      while xc < picW do
        let bs0 := horizontalBs.getD ((xc + yc * bsWidth) >>> 2) 0
        let bs1 := horizontalBs.getD (((xc + 8) + yc * bsWidth) >>> 2) 0
        if bs0 == 2 || bs1 == 2 then
          let ctb0 := (yc >>> log2Ctb) * ctbW + (xc >>> log2Ctb)
          let ctb1 := if ((xc + 16) &&& ctbMask) == 0 && (xc + 16) < picW then ctb0 + 1 else ctb0
          let tcOff0 := (deblockCtb.getD ctb0 {}).tcOffset
          let tcOff1 := (deblockCtb.getD ctb1 {}).tcOffset
          let qp0 := if bs0 == 2 then asrInt (getQpY xc (yc - 1) + getQpY xc yc + 1) 1 else 0
          let qp1 := if bs1 == 2 then asrInt (getQpY (xc + 8) (yc - 1) + getQpY (xc + 8) yc + 1) 1 else 0
          let ctc0 := if bs0 == 2 then chromaTc qp0 cIdx tcOff0 else 0
          let ctc1 := if bs1 == 2 then chromaTc qp1 cIdx tcOff1 else 0
          let np := (if bs0 == 2 then getPcmF xc (yc - 1) else 0, if bs1 == 2 then getPcmF (xc + 8) (yc - 1) else 0)
          let nq := (if bs0 == 2 then getPcmF xc yc else 0, if bs1 == 2 then getPcmF (xc + 8) yc else 0)
          cPlane := loopFilterChroma8 cPlane ((yc >>> 1) * cw + (xc >>> 1)) cw 1 (ctc0, ctc1) np nq
        xc := xc + 16
      yc := yc + 16
    planes := planes.set! cIdx cPlane
  return planes

def saoFrame8 (planes0 : Array ByteArray) (sps : HevcSps) (pps : HevcPps)
    (saoCtb : Array HevcSaoCtb) (tabSliceAddr : Array Int) (filterSliceEdges : Array Bool)
    (isPcm : Array Nat) : Array ByteArray := Id.run do
  let picW := sps.width
  let picH := sps.height
  let log2Ctb := sps.log2CtbSize
  let ctbSize := 1 <<< log2Ctb
  let ctbW := sps.ctbWidth
  let ctbH := sps.ctbHeight
  let log2MinPu := sps.log2MinPuSize
  let minPuSize := 1 <<< log2MinPu
  let minPuW := sps.minPuWidth
  let pcmLoopDis := match sps.pcm? with | some p => p.loopFilterDisableFlag | none => false
  let restoreTqb := pps.transquantBypassEnableFlag || (sps.pcmEnabledFlag && pcmLoopDis)
  let noTileFilter := pps.tilesEnabledFlag && !pps.loopFilterAcrossTilesEnabledFlag
  let rsToTs := pps.ctbAddrRsToTs
  let tileId := pps.tileId
  let origPlanes := planes0
  let mut planes := planes0
  for yCtb in [:ctbH] do
    for xCtb in [:ctbW] do
      let ctbRs := yCtb * ctbW + xCtb
      let ctbTs := rsToTs.getD ctbRs 0
      let sao := saoCtb.getD ctbRs {}
      let x := xCtb <<< log2Ctb
      let y := yCtb <<< log2Ctb
      let e0 := xCtb == 0
      let e1 := yCtb == 0
      let e2 := xCtb + 1 == ctbW
      let e3 := yCtb + 1 == ctbH
      let lfase := filterSliceEdges.getD ctbRs true
      let restore := noTileFilter || !lfase
      let mut vertEdge0 := false
      let mut vertEdge1 := false
      let mut horizEdge0 := false
      let mut horizEdge1 := false
      let mut diag0 := false
      let mut diag1 := false
      let mut diag2 := false
      let mut diag3 := false
      if restore then
        let mut leftTe := false
        let mut rightTe := false
        let mut upTe := false
        let mut botTe := false
        let mySl := tabSliceAddr.getD ctbRs (-1)
        let myTl := tileId.getD ctbTs 0
        if !e0 then
          leftTe := noTileFilter && myTl != tileId.getD (rsToTs.getD (ctbRs - 1) 0) 0
          vertEdge0 := (!lfase && mySl != tabSliceAddr.getD (ctbRs - 1) (-1)) || leftTe
        if !e2 then
          rightTe := noTileFilter && myTl != tileId.getD (rsToTs.getD (ctbRs + 1) 0) 0
          vertEdge1 := (!lfase && mySl != tabSliceAddr.getD (ctbRs + 1) (-1)) || rightTe
        if !e1 then
          upTe := noTileFilter && myTl != tileId.getD (rsToTs.getD (ctbRs - ctbW) 0) 0
          horizEdge0 := (!lfase && mySl != tabSliceAddr.getD (ctbRs - ctbW) (-1)) || upTe
        if !e3 then
          botTe := noTileFilter && myTl != tileId.getD (rsToTs.getD (ctbRs + ctbW) 0) 0
          horizEdge1 := (!lfase && mySl != tabSliceAddr.getD (ctbRs + ctbW) (-1)) || botTe
        if !e0 && !e1 then
          diag0 := (!lfase && mySl != tabSliceAddr.getD (ctbRs - ctbW - 1) (-1)) || leftTe || upTe
        if !e1 && !e2 then
          diag1 := (!lfase && mySl != tabSliceAddr.getD (ctbRs - ctbW + 1) (-1)) || rightTe || upTe
        if !e2 && !e3 then
          diag2 := (!lfase && mySl != tabSliceAddr.getD (ctbRs + ctbW + 1) (-1)) || rightTe || botTe
        if !e0 && !e3 then
          diag3 := (!lfase && mySl != tabSliceAddr.getD (ctbRs + ctbW - 1) (-1)) || leftTe || botTe
      for cIdx in [:3] do
        let tIdx := sao.typeIdx.getD cIdx saoNone
        if tIdx != saoNone then
          let shC := if cIdx == 0 then 0 else 1
          let pw := picW >>> shC
          let ph := picH >>> shC
          let x0 := x >>> shC
          let y0 := y >>> shC
          let width := Nat.min (ctbSize >>> shC) (pw - x0)
          let height := Nat.min (ctbSize >>> shC) (ph - y0)
          let src := origPlanes.getD cIdx ByteArray.empty
          let mut dst := planes.getD cIdx ByteArray.empty
          let offVal := sao.offsetVal.getD cIdx #[0, 0, 0, 0, 0]
          if tIdx == saoBand then
            let mut bandTable : Array Int := Array.replicate 32 0
            let bp := sao.bandPosition.getD cIdx 0
            for k in [:4] do
              bandTable := bandTable.set! ((bp + k) &&& 31) (offVal.getD (k + 1) 0)
            for py in [:height] do
              let roff := (y0 + py) * pw + x0
              for px in [:width] do
                let v := (baGetD src (roff + px) 0).toNat
                dst := dst.set! (roff + px) (clipU8Int (Int.ofNat v + bandTable.getD (v >>> 3) 0))
          else if tIdx == saoEdge then
            let eo := sao.eoClass.getD cIdx 0
            let eoPair := hevcSaoEoPos.getD eo ((-1, 0), (1, 0))
            let ax := eoPair.1.1
            let ay := eoPair.1.2
            let bx := eoPair.2.1
            let byPos := eoPair.2.2
            let initX := if eo != 1 && e0 then 1 else 0
            let endX := width - (if eo != 1 && e2 then 1 else 0)
            let initY := if eo != 0 && e1 then 1 else 0
            let endY := height - (if eo != 0 && e3 then 1 else 0)
            let aOff : Int := ay * Int.ofNat pw + ax
            let bOff : Int := byPos * Int.ofNat pw + bx
            for py in [initY:endY] do
              let roff := (y0 + py) * pw + x0
              for px in [initX:endX] do
                let idxP := roff + px
                let cV := (baGetD src idxP 0).toNat
                let va := (baGetD src (Int.ofNat idxP + aOff).toNat 0).toNat
                let vb := (baGetD src (Int.ofNat idxP + bOff).toNat 0).toNat
                let d0 : Int := if cV > va then 1 else if cV < va then -1 else 0
                let d1 : Int := if cV > vb then 1 else if cV < vb then -1 else 0
                let eIdx := hevcSaoEdgeIdx.getD (2 + d0 + d1).toNat 0
                dst := dst.set! idxP (clipU8Int (Int.ofNat cV + offVal.getD eIdx 0))
            if restore then
              let wEff := endX
              let hEff := endY
              let saveUl := if !diag0 && eo == 2 && !e0 && !e1 then 1 else 0
              let saveUr := if !diag1 && eo == 3 && !e1 && !e2 then 1 else 0
              let saveLr := if !diag2 && eo == 2 && !e2 && !e3 then 1 else 0
              let saveLl := if !diag3 && eo == 3 && !e0 && !e3 then 1 else 0
              if vertEdge0 && eo != 1 then
                for py in [initY + saveUl : hEff - saveLl] do
                  let idxP := (y0 + py) * pw + x0
                  dst := dst.set! idxP (baGetD src idxP 0)
              if vertEdge1 && eo != 1 && wEff > 0 then
                for py in [initY + saveUr : hEff - saveLr] do
                  let idxP := (y0 + py) * pw + x0 + wEff - 1
                  dst := dst.set! idxP (baGetD src idxP 0)
              if horizEdge0 && eo != 0 then
                for px in [initX + saveUl : wEff - saveUr] do
                  let idxP := y0 * pw + x0 + px
                  dst := dst.set! idxP (baGetD src idxP 0)
              if horizEdge1 && eo != 0 && hEff > 0 then
                for px in [initX + saveLl : wEff - saveLr] do
                  let idxP := (y0 + hEff - 1) * pw + x0 + px
                  dst := dst.set! idxP (baGetD src idxP 0)
              if diag0 && eo == 2 then
                let idxP := y0 * pw + x0
                dst := dst.set! idxP (baGetD src idxP 0)
              if diag1 && eo == 3 && wEff > 0 then
                let idxP := y0 * pw + x0 + wEff - 1
                dst := dst.set! idxP (baGetD src idxP 0)
              if diag2 && eo == 2 && wEff > 0 && hEff > 0 then
                let idxP := (y0 + hEff - 1) * pw + x0 + wEff - 1
                dst := dst.set! idxP (baGetD src idxP 0)
              if diag3 && eo == 3 && hEff > 0 then
                let idxP := (y0 + hEff - 1) * pw + x0
                dst := dst.set! idxP (baGetD src idxP 0)
          if restoreTqb then
            let xMin := x >>> log2MinPu
            let yMin := y >>> log2MinPu
            let xMax := (x + (width <<< shC)) >>> log2MinPu
            let yMax := (y + (height <<< shC)) >>> log2MinPu
            let blkC := minPuSize >>> shC
            for yp in [yMin:yMax] do
              for xp in [xMin:xMax] do
                if isPcm.getD (yp * minPuW + xp) 0 != 0 then
                  let bx0 := (xp <<< log2MinPu) >>> shC
                  let by0 := (yp <<< log2MinPu) >>> shC
                  for ny in [:blkC] do
                    let roff := (by0 + ny) * pw + bx0
                    for nx in [:blkC] do
                      dst := dst.set! (roff + nx) (baGetD src (roff + nx) 0)
          planes := planes.set! cIdx dst
  return planes

def intraDc : Nat := 1

def hevcIntraChromaModes : Array Nat := #[0, 26, 10, 1]

def hevcL0L1CandIdx : Array (Nat × Nat) := #[
  (0, 1), (1, 0), (0, 2), (2, 0), (1, 2), (2, 1),
  (0, 3), (3, 0), (1, 3), (3, 1), (2, 3), (3, 2)
]

def mvScale (mv : Int × Int) (td0 tb0 : Int) : Int × Int :=
  let td := clipInt td0 (-128) 127
  let tb := clipInt tb0 (-128) 127
  if td == 0 then mv
  else
    let absHalf := Int.ofNat (td.natAbs >>> 1)
    let num := 16384 + absHalf
    let tx : Int :=
      if td > 0 then Int.ofNat (num.toNat / td.toNat)
      else -Int.ofNat (num.toNat / td.natAbs)
    let scale := clipInt (asrInt (tb * tx + 32) 6) (-4096) 4095
    let p0 := scale * mv.1
    let p1 := scale * mv.2
    let sx := clipInt (asrInt (p0 + 127 + (if p0 < 0 then 1 else 0)) 8) (-32768) 32767
    let sy := clipInt (asrInt (p1 + 127 + (if p1 < 0 then 1 else 0)) 8) (-32768) 32767
    (sx, sy)

def sameMvRef (a b : HevcMvf) : Bool :=
  if a.predFlag != b.predFlag then false
  else if a.predFlag == pfBi then
    a.refIdx0 == b.refIdx0 && a.refIdx1 == b.refIdx1 && a.mv0 == b.mv0 && a.mv1 == b.mv1
  else if a.predFlag == pfL0 then
    a.refIdx0 == b.refIdx0 && a.mv0 == b.mv0
  else if a.predFlag == pfL1 then
    a.refIdx1 == b.refIdx1 && a.mv1 == b.mv1
  else false

structure HevcDecodedFrame where
  poc        : Int := 0
  planes     : Array ByteArray := #[]
  tabMvf     : Array HevcMvf := #[]
  rpl        : Array HevcRpl := #[{}, {}]
  rplTab     : Array (Option (Array HevcRpl)) := #[]
  qpY        : Array Int := #[]
  isPcm      : Array Nat := #[]
  sao        : Array HevcSaoCtb := #[]
  deblock    : Array HevcDeblockCtb := #[]
  vbs        : Array Nat := #[]
  hbs        : Array Nat := #[]
  bsW        : Nat := 1
  sliceAddr  : Array Int := #[]
  lfase      : Array Bool := #[]
  cbfLuma    : Array Nat := #[]
  ipm        : Array Nat := #[]
  ctDepth    : Array Nat := #[]
  skipFlag   : Array Nat := #[]
  outputFlag : Bool := true
  outputted  : Bool := false
  referenced : Bool := true
  tid        : Nat := 0
  nalType    : Nat := 0
  spsId      : Nat := 0
  deriving Inhabited

def frameToRefPlanes (f : HevcDecodedFrame) : HevcRefPlanes :=
  let r0 := f.rpl.getD 0 {}
  let r1 := f.rpl.getD 1 {}
  let tabPoc := f.rplTab.map fun opt =>
    match opt with
    | none => none
    | some rs => some #[(rs.getD 0 {}).poc, (rs.getD 1 {}).poc]
  let tabLt := f.rplTab.map fun opt =>
    match opt with
    | none => none
    | some rs => some #[(rs.getD 0 {}).lt, (rs.getD 1 {}).lt]
  { planes := f.planes
    poc := f.poc
    tabMvf := f.tabMvf
    rplPoc := #[r0.poc, r1.poc]
    rplLt := #[r0.lt, r1.lt]
    rplTabPoc := tabPoc
    rplTabLt := tabLt }

def newDecodedFrame (sps : HevcSps) (sh : HevcSliceHeader) : HevcDecodedFrame :=
  let w := sps.width
  let h := sps.height
  let cw := w >>> 1
  let ch := h >>> 1
  let puN := sps.minPuWidth * sps.minPuHeight
  let cbN := sps.minCbWidth * sps.minCbHeight
  let bsW := (w >>> 2) + 1
  let bsN := ((w + bsW * h) >>> 2) + 4
  let yPlane := ByteArray.mk (Array.replicate (w * h) (128 : UInt8))
  let cPlane := ByteArray.mk (Array.replicate (cw * ch) (128 : UInt8))
  { poc := sh.poc
    planes := #[yPlane, cPlane, cPlane]
    tabMvf := Array.replicate puN mvfZero
    rpl := #[{}, {}]
    rplTab := Array.replicate sps.ctbSize none
    qpY := Array.replicate cbN sh.sliceQp
    isPcm := Array.replicate puN 0
    sao := Array.replicate sps.ctbSize {}
    deblock := Array.replicate sps.ctbSize { betaOffset := sh.betaOffset, tcOffset := sh.tcOffset }
    vbs := Array.replicate bsN 0
    hbs := Array.replicate bsN 0
    bsW := bsW
    sliceAddr := Array.replicate sps.ctbSize (-1)
    lfase := Array.replicate sps.ctbSize true
    cbfLuma := Array.replicate (sps.minTbWidth * sps.minTbHeight) 0
    ipm := Array.replicate puN intraDc
    ctDepth := Array.replicate cbN 0
    skipFlag := Array.replicate cbN 0
    outputFlag := sh.picOutputFlag
    outputted := false
    referenced := true
    tid := sh.tid
    nalType := sh.nalType
    spsId := sh.spsId }

structure HevcCtbCtx where
  ctbLeft            : Bool := false
  ctbUp              : Bool := false
  ctbUpRight         : Bool := false
  ctbUpLeft          : Bool := false
  endOfTilesX        : Nat := 0
  endOfTilesY        : Nat := 0
  boundaryLeftSlice  : Bool := false
  boundaryUpperSlice : Bool := false
  boundaryLeftTile   : Bool := false
  boundaryUpperTile  : Bool := false
  firstQpGroup       : Bool := true
  qpyPred            : Int := 26
  qpY                : Int := 26
  cuQpDeltaCoded     : Bool := false
  cuQpDelta          : Int := 0
  ctDepth            : Nat := 0
  mergeFlag          : Nat := 0
  cuX                : Nat := 0
  cuY                : Nat := 0
  chromaPredMode     : Nat := 0
  intraLumaModes     : Array Nat := #[1]
  tuLumaMode         : Nat := 1
  deriving Inhabited

def sortFramesByPoc (arr : Array HevcDecodedFrame) : Array HevcDecodedFrame := Id.run do
  let mut a := arr
  for i in [:a.size] do
    let mut j := i
    while j > 0 && (a[j]!).poc < (a[j - 1]!).poc do
      let tmp := a[j - 1]!
      a := a.set! (j - 1) (a[j]!)
      a := a.set! j tmp
      j := j - 1
  return a

def findDpbRefIdx (dpb : Array HevcDecodedFrame) (poc : Int) (lt msb : Bool) (sps : HevcSps) :
    Option Nat := Id.run do
  let modN := Int.ofNat (1 <<< sps.log2MaxPocLsb)
  let mut k := dpb.size
  while k > 0 do
    k := k - 1
    let f := dpb[k]!
    if msb || !lt then
      if f.poc == poc then return some k
    else
      if f.poc % modN == poc % modN then return some k
  return none

def markDpbRps (dpb0 : Array HevcDecodedFrame) (sps : HevcSps) (sh : HevcSliceHeader) :
    Array HevcDecodedFrame := Id.run do
  if isIdr sh.nalType || isBla sh.nalType then
    let mut out : Array HevcDecodedFrame := #[]
    for f in dpb0 do
      if f.outputFlag && !f.outputted then
        out := out.push { f with referenced := false }
    return out
  let mut dpb : Array HevcDecodedFrame := dpb0.map (fun f => { f with referenced := false })
  let st := sh.shortTermRps
  for d in st.deltaPoc do
    if let some idx := findDpbRefIdx dpb (sh.poc + d) false true sps then
      dpb := dpb.set! idx { dpb[idx]! with referenced := true }
  let lt := sh.ltRps
  for i in [:lt.poc.size] do
    let lp := lt.poc.getD i 0
    let msb := lt.pocMsbPresent.getD i 0 != 0
    if let some idx := findDpbRefIdx dpb lp true msb sps then
      dpb := dpb.set! idx { dpb[idx]! with referenced := true }
  let mut pruned : Array HevcDecodedFrame := #[]
  for f in dpb do
    if f.referenced || (f.outputFlag && !f.outputted) then
      pruned := pruned.push f
  return pruned

def buildSliceRpl (dpb : Array HevcDecodedFrame) (sps : HevcSps) (sh : HevcSliceHeader) :
    Array HevcRpl := Id.run do
  let poc := sh.poc
  let st := sh.shortTermRps
  let lt := sh.ltRps
  let mut bef : Array (Int × Bool × Bool) := #[]
  let mut aft : Array (Int × Bool × Bool) := #[]
  let mut ltc : Array (Int × Bool × Bool) := #[]
  for i in [:st.deltaPoc.size] do
    if st.used.getD i 0 != 0 then
      let entry := (poc + st.deltaPoc.getD i 0, false, true)
      if i < st.numNegativePics then bef := bef.push entry else aft := aft.push entry
  for i in [:lt.poc.size] do
    if lt.used.getD i 0 != 0 then
      ltc := ltc.push (lt.poc.getD i 0, true, lt.pocMsbPresent.getD i 0 != 0)
  let cands : Array (Array (Int × Bool × Bool)) := #[bef ++ aft ++ ltc, aft ++ bef ++ ltc]
  let mut outRpl : Array HevcRpl := #[{}, {}]
  for lx in [:2] do
    let nb := sh.nbRefs.getD lx 0
    let candLx := cands.getD lx #[]
    let mut tmp : Array (Int × Bool × Bool) := #[]
    let mut guard := 0
    while tmp.size < nb && !candLx.isEmpty && guard < 16 do
      tmp := tmp ++ candLx
      guard := guard + 1
    let mut refs : Array (Option HevcRefPlanes) := Array.mkEmpty nb
    let mut pocs : Array Int := Array.mkEmpty nb
    let mut isLt : Array Bool := Array.mkEmpty nb
    let modFlag := sh.rplModFlag.getD lx 0 != 0
    let entries := sh.listEntryLx.getD lx #[]
    for i in [:nb] do
      let idx := if modFlag then entries.getD i i else i
      if idx >= tmp.size then
        refs := refs.push none
        pocs := pocs.push 0
        isLt := isLt.push false
      else
        let c := tmp[idx]!
        let cPoc := c.1
        let cLt := c.2.1
        let cMsb := c.2.2
        match findDpbRefIdx dpb cPoc cLt cMsb sps with
        | some fIdx =>
          let rf := dpb[fIdx]!
          refs := refs.push (some (frameToRefPlanes rf))
          pocs := pocs.push rf.poc
          isLt := isLt.push cLt
        | none =>
          refs := refs.push none
          pocs := pocs.push cPoc
          isLt := isLt.push cLt
    outRpl := outRpl.set! lx { refs := refs, poc := pocs, lt := isLt }
  return outRpl

def ctDepthAt (pic : HevcDecodedFrame) (sps : HevcSps) (x y : Int) : Nat :=
  if x < 0 || y < 0 then 0
  else
    let cx := x.toNat >>> sps.log2MinCbSize
    let cy := y.toNat >>> sps.log2MinCbSize
    pic.ctDepth.getD (cy * sps.minCbWidth + cx) 0

def setCtDepthBlock (pic0 : HevcDecodedFrame) (sps : HevcSps) (x0 y0 log2Cb depth : Nat) :
    HevcDecodedFrame := Id.run do
  let step := 1 <<< sps.log2MinCbSize
  let yEnd := Nat.min (y0 + (1 <<< log2Cb)) sps.height
  let xEnd := Nat.min (x0 + (1 <<< log2Cb)) sps.width
  let mut tab := pic0.ctDepth
  let mut y := y0
  while y < yEnd do
    let mut x := x0
    while x < xEnd do
      let idx := (y >>> sps.log2MinCbSize) * sps.minCbWidth + (x >>> sps.log2MinCbSize)
      tab := tab.set! idx depth
      x := x + step
    y := y + step
  return { pic0 with ctDepth := tab }

def skipAt (pic : HevcDecodedFrame) (sps : HevcSps) (x y : Int) : Nat :=
  if x < 0 || y < 0 then 0
  else
    let cx := x.toNat >>> sps.log2MinCbSize
    let cy := y.toNat >>> sps.log2MinCbSize
    pic.skipFlag.getD (cy * sps.minCbWidth + cx) 0

def fillSkipBlock (pic0 : HevcDecodedFrame) (sps : HevcSps) (x0 y0 log2Cb skip : Nat) :
    HevcDecodedFrame := Id.run do
  let step := 1 <<< sps.log2MinCbSize
  let yEnd := Nat.min (y0 + (1 <<< log2Cb)) sps.height
  let xEnd := Nat.min (x0 + (1 <<< log2Cb)) sps.width
  let mut tab := pic0.skipFlag
  let mut y := y0
  while y < yEnd do
    let mut x := x0
    while x < xEnd do
      let idx := (y >>> sps.log2MinCbSize) * sps.minCbWidth + (x >>> sps.log2MinCbSize)
      tab := tab.set! idx skip
      x := x + step
    y := y + step
  return { pic0 with skipFlag := tab }

def setQpCbBlock (pic0 : HevcDecodedFrame) (sps : HevcSps) (x0 y0 log2Cb : Nat) (qp : Int) :
    HevcDecodedFrame := Id.run do
  let step := 1 <<< sps.log2MinCbSize
  let yEnd := Nat.min (y0 + (1 <<< log2Cb)) sps.height
  let xEnd := Nat.min (x0 + (1 <<< log2Cb)) sps.width
  let mut tab := pic0.qpY
  let mut y := y0
  while y < yEnd do
    let mut x := x0
    while x < xEnd do
      let idx := (y >>> sps.log2MinCbSize) * sps.minCbWidth + (x >>> sps.log2MinCbSize)
      tab := tab.set! idx qp
      x := x + step
    y := y + step
  return { pic0 with qpY := tab }

def fillPcmFlagBlock (pic0 : HevcDecodedFrame) (sps : HevcSps) (x0 y0 log2Cb v : Nat) :
    HevcDecodedFrame := Id.run do
  let step := 1 <<< sps.log2MinPuSize
  let yEnd := Nat.min (y0 + (1 <<< log2Cb)) sps.height
  let xEnd := Nat.min (x0 + (1 <<< log2Cb)) sps.width
  let mut tab := pic0.isPcm
  let mut y := y0
  while y < yEnd do
    let mut x := x0
    while x < xEnd do
      let idx := (y >>> sps.log2MinPuSize) * sps.minPuWidth + (x >>> sps.log2MinPuSize)
      tab := tab.set! idx v
      x := x + step
    y := y + step
  return { pic0 with isPcm := tab }

def ipmAt (pic : HevcDecodedFrame) (sps : HevcSps) (x y : Int) : Option Nat :=
  if x < 0 || y < 0 || x.toNat >= sps.width || y.toNat >= sps.height then none
  else
    let px := x.toNat >>> sps.log2MinPuSize
    let py := y.toNat >>> sps.log2MinPuSize
    some (pic.ipm.getD (py * sps.minPuWidth + px) intraDc)

def fillIpmBlock (pic0 : HevcDecodedFrame) (sps : HevcSps) (x0 y0 w h mode : Nat) (intra : Bool) :
    HevcDecodedFrame := Id.run do
  let step := 1 <<< sps.log2MinPuSize
  let yEnd := Nat.min (y0 + h) sps.height
  let xEnd := Nat.min (x0 + w) sps.width
  let mut ipm := pic0.ipm
  let mut tabMvf := pic0.tabMvf
  let mut y := y0
  while y < yEnd do
    let mut x := x0
    while x < xEnd do
      let idx := (y >>> sps.log2MinPuSize) * sps.minPuWidth + (x >>> sps.log2MinPuSize)
      ipm := ipm.set! idx mode
      if intra then tabMvf := tabMvf.set! idx mvfIntra
      x := x + step
    y := y + step
  return { pic0 with ipm := ipm, tabMvf := tabMvf }

def storeMvfBlock (pic0 : HevcDecodedFrame) (sps : HevcSps) (x0 y0 pw ph : Nat) (mvf : HevcMvf) :
    HevcDecodedFrame := Id.run do
  let step := 1 <<< sps.log2MinPuSize
  let yEnd := Nat.min (y0 + ph) sps.height
  let xEnd := Nat.min (x0 + pw) sps.width
  let mut tabMvf := pic0.tabMvf
  let mut y := y0
  while y < yEnd do
    let mut x := x0
    while x < xEnd do
      let idx := (y >>> sps.log2MinPuSize) * sps.minPuWidth + (x >>> sps.log2MinPuSize)
      tabMvf := tabMvf.set! idx mvf
      x := x + step
    y := y + step
  return { pic0 with tabMvf := tabMvf }

def mvfAt (pic : HevcDecodedFrame) (sps : HevcSps) (x y : Int) : Option HevcMvf :=
  if x < 0 || y < 0 || x.toNat >= sps.width || y.toNat >= sps.height then none
  else
    let px := x.toNat >>> sps.log2MinPuSize
    let py := y.toNat >>> sps.log2MinPuSize
    some (pic.tabMvf.getD (py * sps.minPuWidth + px) mvfZero)

def mvfAtRef (rf : HevcRefPlanes) (sps : HevcSps) (x y : Int) : Option HevcMvf :=
  if x < 0 || y < 0 || x.toNat >= sps.width || y.toNat >= sps.height then none
  else
    let px := x.toNat >>> sps.log2MinPuSize
    let py := y.toNat >>> sps.log2MinPuSize
    some (rf.tabMvf.getD (py * sps.minPuWidth + px) mvfZero)

def mvfInterAt (pic : HevcDecodedFrame) (sps : HevcSps) (x y : Int) : Option HevcMvf :=
  match mvfAt pic sps x y with
  | none => none
  | some m =>
    if m.predFlag == pfIntra || m.predFlag == 0 then none else some m

def computeNeighAvail (ctx : HevcCtbCtx) (sps : HevcSps) (x0 y0 w h : Nat) : HevcNeighAvail :=
  let log2Ctb := sps.log2CtbSize
  let ctbMask := (1 <<< log2Ctb) - 1
  let x0b := x0 &&& ctbMask
  let y0b := y0 &&& ctbMask
  let candUp := ctx.ctbUp || y0b != 0
  let candLeft := ctx.ctbLeft || x0b != 0
  let candUpLeft := if x0b != 0 || y0b != 0 then candLeft && candUp else ctx.ctbUpLeft
  let candUpRightSap :=
    if x0b + w == (1 <<< log2Ctb) then ctx.ctbUpRight && y0b == 0 else candUp
  let candUpRight := candUpRightSap && (x0 + w) < ctx.endOfTilesX
  let candBottomLeft := if (y0 + h) >= ctx.endOfTilesY then false else candLeft
  { candUp := candUp
    candLeft := candLeft
    candUpLeft := candUpLeft
    candUpRightSap := candUpRightSap
    candUpRight := candUpRight
    candBottomLeft := candBottomLeft }

def zscanAvail (sps : HevcSps) (pps : HevcPps) (xCurr yCurr : Nat) (xN yN : Int) : Bool :=
  if xN < 0 || yN < 0 then false
  else
    let log2Ctb := sps.log2CtbSize
    let xn := xN.toNat
    let yn := yN.toNat
    if (yn >>> log2Ctb) < (yCurr >>> log2Ctb) || (xn >>> log2Ctb) < (xCurr >>> log2Ctb) then true
    else
      let mask := sps.tbMask
      let log2Tb := sps.log2MinTbSize
      let curr := minTbAddrZs pps (Int.ofNat ((xCurr >>> log2Tb) &&& mask)) (Int.ofNat ((yCurr >>> log2Tb) &&& mask))
      let naddr := minTbAddrZs pps (Int.ofNat ((xn >>> log2Tb) &&& mask)) (Int.ofNat ((yn >>> log2Tb) &&& mask))
      naddr <= curr

def diffMer (pps : HevcPps) (xN yN : Int) (xP yP : Nat) : Bool :=
  let p := pps.log2ParallelMergeLevel
  asrInt xN p == Int.ofNat (xP >>> p) && asrInt yN p == Int.ofNat (yP >>> p)

def deriveLumaIntraMode (ctx : HevcCtbCtx) (pic : HevcDecodedFrame) (sps : HevcSps)
    (x0 y0 : Nat) (prevFlag : Bool) (mpmIdx rem0 : Nat) : Nat := Id.run do
  let ctbMask := (1 <<< sps.log2CtbSize) - 1
  let leftOpt :=
    if ctx.ctbLeft || (x0 &&& ctbMask) != 0 then ipmAt pic sps (Int.ofNat x0 - 1) (Int.ofNat y0)
    else none
  let upOpt :=
    if ctx.ctbUp || (y0 &&& ctbMask) != 0 then ipmAt pic sps (Int.ofNat x0) (Int.ofNat y0 - 1)
    else none
  let c0 := leftOpt.getD intraDc
  let mut c1 := upOpt.getD intraDc
  if (y0 &&& ctbMask) == 0 then c1 := intraDc
  let mpm : Array Nat :=
    if c0 == c1 then
      if c0 < 2 then #[0, intraDc, 26]
      else #[c0, 2 + ((c0 + 29) &&& 31), 2 + ((c0 - 1) &&& 31)]
    else
      let c2 := if c0 != 0 && c1 != 0 then 0 else if c0 != intraDc && c1 != intraDc then intraDc else 26
      #[c0, c1, c2]
  if prevFlag then return mpm.getD mpmIdx intraDc
  let mut a := mpm.getD 0 0
  let mut b := mpm.getD 1 0
  let mut c := mpm.getD 2 0
  if a > b then let t := a; a := b; b := t
  if b > c then let t := b; b := c; c := t
  if a > b then let t := a; a := b; b := t
  let mut rem := rem0
  if rem >= a then rem := rem + 1
  if rem >= b then rem := rem + 1
  if rem >= c then rem := rem + 1
  return rem

def rplAt (pic : HevcDecodedFrame) (sps : HevcSps) (x y : Int) : Array HevcRpl :=
  if x < 0 || y < 0 then pic.rpl
  else
    let rs := (y.toNat >>> sps.log2CtbSize) * sps.ctbWidth + (x.toNat >>> sps.log2CtbSize)
    match pic.rplTab.getD rs none with
    | some r => r
    | none => pic.rpl

def refPocOpt (rpl : Array HevcRpl) (lx : Nat) (refIdx : Int) : Option Int :=
  let pocs := (rpl.getD lx {}).poc
  if refIdx < 0 || refIdx.toNat >= pocs.size then none
  else some (pocs[refIdx.toNat]!)

def calcBoundaryStrength (curr neigh : HevcMvf) (rplCurr rplNeigh : Array HevcRpl) : Nat :=
  if curr.predFlag == pfBi && neigh.predFlag == pfBi then
    let c0 := refPocOpt rplCurr 0 curr.refIdx0
    let c1 := refPocOpt rplCurr 1 curr.refIdx1
    let n0 := refPocOpt rplNeigh 0 neigh.refIdx0
    let n1 := refPocOpt rplNeigh 1 neigh.refIdx1
    if c0 == n0 && c0 == c1 && n0 == n1 then
      let dSame :=
        (neigh.mv0.1 - curr.mv0.1).natAbs >= 4 || (neigh.mv0.2 - curr.mv0.2).natAbs >= 4 ||
        (neigh.mv1.1 - curr.mv1.1).natAbs >= 4 || (neigh.mv1.2 - curr.mv1.2).natAbs >= 4
      let dSwap :=
        (neigh.mv1.1 - curr.mv0.1).natAbs >= 4 || (neigh.mv1.2 - curr.mv0.2).natAbs >= 4 ||
        (neigh.mv0.1 - curr.mv1.1).natAbs >= 4 || (neigh.mv0.2 - curr.mv1.2).natAbs >= 4
      if dSame && dSwap then 1 else 0
    else if n0 == c0 && n1 == c1 then
      if (neigh.mv0.1 - curr.mv0.1).natAbs >= 4 || (neigh.mv0.2 - curr.mv0.2).natAbs >= 4 ||
          (neigh.mv1.1 - curr.mv1.1).natAbs >= 4 || (neigh.mv1.2 - curr.mv1.2).natAbs >= 4 then 1
      else 0
    else if n1 == c0 && n0 == c1 then
      if (neigh.mv1.1 - curr.mv0.1).natAbs >= 4 || (neigh.mv1.2 - curr.mv0.2).natAbs >= 4 ||
          (neigh.mv0.1 - curr.mv1.1).natAbs >= 4 || (neigh.mv0.2 - curr.mv1.2).natAbs >= 4 then 1
      else 0
    else 1
  else if curr.predFlag != pfBi && neigh.predFlag != pfBi then
    let (aMv, aPoc) :=
      if (curr.predFlag &&& pfL0) != 0 then (curr.mv0, refPocOpt rplCurr 0 curr.refIdx0)
      else (curr.mv1, refPocOpt rplCurr 1 curr.refIdx1)
    let (bMv, bPoc) :=
      if (neigh.predFlag &&& pfL0) != 0 then (neigh.mv0, refPocOpt rplNeigh 0 neigh.refIdx0)
      else (neigh.mv1, refPocOpt rplNeigh 1 neigh.refIdx1)
    if aPoc == bPoc then
      if (aMv.1 - bMv.1).natAbs >= 4 || (aMv.2 - bMv.2).natAbs >= 4 then 1 else 0
    else 1
  else 1

def updateDeblockBs (ctx : HevcCtbCtx) (pic0 : HevcDecodedFrame) (sps : HevcSps)
    (pps : HevcPps) (sh : HevcSliceHeader) (x0 y0 log2Size : Nat) : HevcDecodedFrame := Id.run do
  let size := 1 <<< log2Size
  let bsW := pic0.bsW
  let log2Pu := sps.log2MinPuSize
  let log2Tu := sps.log2MinTbSize
  let minPuW := sps.minPuWidth
  let minTuW := sps.minTbWidth
  let ctb := 1 <<< sps.log2CtbSize
  let isIntra := ((mvfAt pic0 sps (Int.ofNat x0) (Int.ofNat y0)).getD mvfZero).predFlag == pfIntra
  let mut vbs := pic0.vbs
  let mut hbs := pic0.hbs
  let mut boundaryUpper := y0 > 0 && (y0 &&& 7) == 0
  if boundaryUpper && y0 % ctb == 0 then
    if (!sh.sliceLoopFilterAcrossSlicesEnabledFlag && ctx.boundaryUpperSlice) ||
        (!pps.loopFilterAcrossTilesEnabledFlag && ctx.boundaryUpperTile) then
      boundaryUpper := false
  if boundaryUpper then
    let rplTop := if ctx.boundaryUpperSlice then rplAt pic0 sps (Int.ofNat x0) (Int.ofNat y0 - 1) else pic0.rpl
    let mut i := 0
    while i < size do
      let xPu := (x0 + i) >>> log2Pu
      let xTu := (x0 + i) >>> log2Tu
      let top := pic0.tabMvf.getD (((y0 - 1) >>> log2Pu) * minPuW + xPu) mvfZero
      let curr := pic0.tabMvf.getD ((y0 >>> log2Pu) * minPuW + xPu) mvfZero
      let topCbf := pic0.cbfLuma.getD (((y0 - 1) >>> log2Tu) * minTuW + xTu) 0
      let currCbf := pic0.cbfLuma.getD ((y0 >>> log2Tu) * minTuW + xTu) 0
      let bs :=
        if curr.predFlag == pfIntra || top.predFlag == pfIntra then 2
        else if currCbf != 0 || topCbf != 0 then 1
        else calcBoundaryStrength curr top pic0.rpl rplTop
      hbs := hbs.set! (((x0 + i) + y0 * bsW) >>> 2) bs
      i := i + 4
  let mut boundaryLeft := x0 > 0 && (x0 &&& 7) == 0
  if boundaryLeft && x0 % ctb == 0 then
    if (!sh.sliceLoopFilterAcrossSlicesEnabledFlag && ctx.boundaryLeftSlice) ||
        (!pps.loopFilterAcrossTilesEnabledFlag && ctx.boundaryLeftTile) then
      boundaryLeft := false
  if boundaryLeft then
    let rplLeft := if ctx.boundaryLeftSlice then rplAt pic0 sps (Int.ofNat x0 - 1) (Int.ofNat y0) else pic0.rpl
    let mut i := 0
    while i < size do
      let yPu := (y0 + i) >>> log2Pu
      let yTu := (y0 + i) >>> log2Tu
      let left := pic0.tabMvf.getD (yPu * minPuW + ((x0 - 1) >>> log2Pu)) mvfZero
      let curr := pic0.tabMvf.getD (yPu * minPuW + (x0 >>> log2Pu)) mvfZero
      let leftCbf := pic0.cbfLuma.getD (yTu * minTuW + ((x0 - 1) >>> log2Tu)) 0
      let currCbf := pic0.cbfLuma.getD (yTu * minTuW + (x0 >>> log2Tu)) 0
      let bs :=
        if curr.predFlag == pfIntra || left.predFlag == pfIntra then 2
        else if currCbf != 0 || leftCbf != 0 then 1
        else calcBoundaryStrength curr left pic0.rpl rplLeft
      vbs := vbs.set! ((x0 + (y0 + i) * bsW) >>> 2) bs
      i := i + 4
  if log2Size > log2Pu && !isIntra then
    let mut j := 8
    while j < size do
      let mut i := 0
      while i < size do
        let xPu := (x0 + i) >>> log2Pu
        let top := pic0.tabMvf.getD (((y0 + j - 1) >>> log2Pu) * minPuW + xPu) mvfZero
        let curr := pic0.tabMvf.getD (((y0 + j) >>> log2Pu) * minPuW + xPu) mvfZero
        hbs := hbs.set! (((x0 + i) + (y0 + j) * bsW) >>> 2)
          (calcBoundaryStrength curr top pic0.rpl pic0.rpl)
        i := i + 4
      j := j + 8
    let mut j2 := 0
    while j2 < size do
      let yPu := (y0 + j2) >>> log2Pu
      let mut i2 := 8
      while i2 < size do
        let left := pic0.tabMvf.getD (yPu * minPuW + ((x0 + i2 - 1) >>> log2Pu)) mvfZero
        let curr := pic0.tabMvf.getD (yPu * minPuW + ((x0 + i2) >>> log2Pu)) mvfZero
        vbs := vbs.set! (((x0 + i2) + (y0 + j2) * bsW) >>> 2)
          (calcBoundaryStrength curr left pic0.rpl pic0.rpl)
        i2 := i2 + 8
      j2 := j2 + 4
  return { pic0 with vbs := vbs, hbs := hbs }

def align16Down (n : Nat) : Nat :=
  (n >>> 4) <<< 4

def rplTabAtRef (rf : HevcRefPlanes) (sps : HevcSps) (cx cy : Nat) :
    Array (Array Int) × Array (Array Bool) :=
  let rs := (cy >>> sps.log2CtbSize) * sps.ctbWidth + (cx >>> sps.log2CtbSize)
  match rf.rplTabPoc.getD rs none with
  | none => (rf.rplPoc, rf.rplLt)
  | some tabPoc =>
    match rf.rplTabLt.getD rs none with
    | none => (rf.rplPoc, rf.rplLt)
    | some tabLt => (tabPoc, tabLt)

def tmvpOne (pic : HevcDecodedFrame) (sps : HevcSps) (sh : HevcSliceHeader)
    (colPic : HevcRefPlanes) (colPoc : Int) (cx cy lxTarget refIdx : Nat) : Option (Int × Int) :=
  match mvfAtRef colPic sps (Int.ofNat cx) (Int.ofNat cy) with
  | none => none
  | some col =>
    if col.predFlag == pfIntra || col.predFlag == 0 then none
    else
      let (tabPoc, tabLt) := rplTabAtRef colPic sps cx cy
      let listCol :=
        if (col.predFlag &&& pfL0) == 0 then 1
        else if col.predFlag == pfL0 then 0
        else
          let future :=
            ((pic.rpl.getD 0 {}).poc.any (fun p => p > pic.poc)) ||
            ((pic.rpl.getD 1 {}).poc.any (fun p => p > pic.poc))
          if !future then lxTarget else if sh.collocatedList == 1 then 0 else 1
      let ri := mvfRefIdx col listCol
      let pocs := tabPoc.getD listCol #[]
      if ri < 0 || ri.toNat >= pocs.size then none
      else
        let curLtArr := (pic.rpl.getD lxTarget {}).lt
        let colLtArr := tabLt.getD listCol #[]
        let curLt := curLtArr.getD refIdx false
        let colLt := colLtArr.getD ri.toNat false
        if curLt != colLt then some (0, 0)
        else
          let colPocDiff := colPoc - pocs[ri.toNat]!
          let curPocDiff := pic.poc - ((pic.rpl.getD lxTarget {}).poc.getD refIdx 0)
          let mv := mvfMv col listCol
          if curLt || colPocDiff == curPocDiff || colPocDiff == 0 then some mv
          else some (mvScale mv colPocDiff curPocDiff)

def tmvpLx (pic : HevcDecodedFrame) (sps : HevcSps) (sh : HevcSliceHeader)
    (x0 y0 pw ph refIdx lxTarget : Nat) : Option (Int × Int) :=
  let cl := sh.collocatedList
  let cr := sh.collocatedRefIdx
  let rplCl := pic.rpl.getD cl {}
  if cr >= rplCl.refs.size then none
  else
    match rplCl.refs[cr]! with
    | none => none
    | some colPic =>
      let colPoc := rplCl.poc.getD cr 0
      let xBr := x0 + pw
      let yBr := y0 + ph
      let brOk := (y0 >>> sps.log2CtbSize) == (yBr >>> sps.log2CtbSize) &&
        xBr < sps.width && yBr < sps.height
      if brOk then
        match tmvpOne pic sps sh colPic colPoc (align16Down xBr) (align16Down yBr) lxTarget refIdx with
        | some mv => some mv
        | none => tmvpOne pic sps sh colPic colPoc (align16Down (x0 + (pw >>> 1))) (align16Down (y0 + (ph >>> 1))) lxTarget refIdx
      else
        tmvpOne pic sps sh colPic colPoc (align16Down (x0 + (pw >>> 1))) (align16Down (y0 + (ph >>> 1))) lxTarget refIdx

def tmvpMerge (pic : HevcDecodedFrame) (sps : HevcSps) (sh : HevcSliceHeader)
    (x0 y0 pw ph : Nat) : Option HevcMvf :=
  let l0? := tmvpLx pic sps sh x0 y0 pw ph 0 0
  let l1? := if sh.sliceType == sliceB then tmvpLx pic sps sh x0 y0 pw ph 0 1 else none
  if l0?.isNone && l1?.isNone then none
  else
    let pf := (if l0?.isSome then pfL0 else 0) + (if l1?.isSome then pfL1 else 0)
    some { predFlag := pf, refIdx0 := 0, refIdx1 := 0, mv0 := l0?.getD (0, 0), mv1 := l1?.getD (0, 0) }

def mergeCandidates (ctx : HevcCtbCtx) (pic : HevcDecodedFrame) (sps : HevcSps) (pps : HevcPps)
    (sh : HevcSliceHeader) (x0 y0 pw ph log2Cb part partIdx : Nat) : Array HevcMvf := Id.run do
  let pw2 := pw
  let ph2 := ph
  let mut x0 := x0
  let mut y0 := y0
  let mut pw := pw
  let mut ph := ph
  let mut partIdx := partIdx
  let single := pps.log2ParallelMergeLevel > 2 && (1 <<< log2Cb) == 8
  if single then
    x0 := ctx.cuX
    y0 := ctx.cuY
    pw := 1 <<< log2Cb
    ph := 1 <<< log2Cb
    partIdx := 0
  let na := computeNeighAvail ctx sps x0 y0 pw ph
  let xA1 : Int := Int.ofNat x0 - 1
  let yA1 : Int := Int.ofNat (y0 + ph) - 1
  let xB1 : Int := Int.ofNat (x0 + pw) - 1
  let yB1 : Int := Int.ofNat y0 - 1
  let xB0 : Int := Int.ofNat (x0 + pw)
  let yB0 : Int := Int.ofNat y0 - 1
  let xA0 : Int := Int.ofNat x0 - 1
  let yA0 : Int := Int.ofNat (y0 + ph)
  let xB2 : Int := Int.ofNat x0 - 1
  let yB2 : Int := Int.ofNat y0 - 1
  let mut cands : Array HevcMvf := #[]
  let mut availA1 := false
  let mut availB1 := false
  let a1Blocked := (!single && partIdx == 1 && (part == partNx2N || part == partNLx2N || part == partNRx2N)) ||
    diffMer pps xA1 yA1 x0 y0
  if !a1Blocked && na.candLeft then
    match mvfInterAt pic sps xA1 yA1 with
    | some m =>
      availA1 := true
      cands := cands.push m
    | none => pure ()
  let b1Blocked := (!single && partIdx == 1 && (part == part2NxN || part == part2NxnU || part == part2NxnD)) ||
    diffMer pps xB1 yB1 x0 y0
  if !b1Blocked && na.candUp then
    match mvfInterAt pic sps xB1 yB1 with
    | some m =>
      availB1 := true
      let dup := availA1 && sameMvRef m ((mvfAt pic sps xA1 yA1).getD mvfZero)
      if !dup then cands := cands.push m
    | none => pure ()
  let b0Ok := na.candUpRightSap && xB0.toNat < sps.width &&
    zscanAvail sps pps x0 y0 xB0 yB0 &&
    !diffMer pps xB0 yB0 x0 y0
  if b0Ok then
    match mvfInterAt pic sps xB0 yB0 with
    | some m =>
      let dup := availB1 && sameMvRef m ((mvfAt pic sps xB1 yB1).getD mvfZero)
      if !dup then cands := cands.push m
    | none => pure ()
  let a0Ok := na.candBottomLeft && yA0.toNat < sps.height &&
    zscanAvail sps pps x0 y0 xA0 yA0 &&
    !diffMer pps xA0 yA0 x0 y0
  if a0Ok then
    match mvfInterAt pic sps xA0 yA0 with
    | some m =>
      let dup := availA1 && sameMvRef m ((mvfAt pic sps xA1 yA1).getD mvfZero)
      if !dup then cands := cands.push m
    | none => pure ()
  let b2Ok := na.candUpLeft && !diffMer pps xB2 yB2 x0 y0
  if b2Ok && cands.size != 4 then
    match mvfInterAt pic sps xB2 yB2 with
    | some m =>
      let dupA := availA1 && sameMvRef m ((mvfAt pic sps xA1 yA1).getD mvfZero)
      let dupB := availB1 && sameMvRef m ((mvfAt pic sps xB1 yB1).getD mvfZero)
      if !dupA && !dupB then cands := cands.push m
    | none => pure ()
  if sh.sliceTemporalMvpEnabledFlag && cands.size < sh.maxNumMergeCand then
    if let some col := tmvpMerge pic sps sh x0 y0 pw ph then
      cands := cands.push col
  let nbOrig := cands.size
  if sh.sliceType == sliceB && 1 < nbOrig && nbOrig < sh.maxNumMergeCand then
    let mut comb := 0
    let lim := nbOrig * (nbOrig - 1)
    while cands.size < sh.maxNumMergeCand && comb < lim && comb < hevcL0L1CandIdx.size do
      let (i0, i1) := hevcL0L1CandIdx[comb]!
      comb := comb + 1
      let l0 := cands.getD i0 mvfZero
      let l1 := cands.getD i1 mvfZero
      if (l0.predFlag &&& pfL0) != 0 && (l1.predFlag &&& pfL1) != 0 then
        let p0 := refPocOpt pic.rpl 0 l0.refIdx0
        let p1 := refPocOpt pic.rpl 1 l1.refIdx1
        if !(p0 == p1 && l0.mv0 == l1.mv1) then
          cands := cands.push { predFlag := pfBi, refIdx0 := l0.refIdx0, refIdx1 := l1.refIdx1, mv0 := l0.mv0, mv1 := l1.mv1 }
  let nbRefs := if sh.sliceType == sliceP then sh.nbRefs.getD 0 0
    else Nat.min (sh.nbRefs.getD 0 0) (sh.nbRefs.getD 1 0)
  let mut zeroIdx := 0
  while cands.size < sh.maxNumMergeCand do
    let r := if zeroIdx < nbRefs then zeroIdx else 0
    let pfZ := if sh.sliceType == sliceB then pfBi else pfL0
    cands := cands.push { predFlag := pfZ, refIdx0 := Int.ofNat r, refIdx1 := Int.ofNat r, mv0 := (0, 0), mv1 := (0, 0) }
    zeroIdx := zeroIdx + 1
  if pw2 + ph2 == 12 then
    for i in [:cands.size] do
      let c := cands[i]!
      if c.predFlag == pfBi then cands := cands.set! i { c with predFlag := pfL0 }
  return cands

def mvpList (ctx : HevcCtbCtx) (pic : HevcDecodedFrame) (sps : HevcSps) (pps : HevcPps)
    (sh : HevcSliceHeader) (x0 y0 pw ph lx ridx mvpFlag : Nat) : Int × Int := Id.run do
  let na := computeNeighAvail ctx sps x0 y0 pw ph
  let targetPoc := (pic.rpl.getD lx {}).poc.getD ridx 0
  let targetLt := (pic.rpl.getD lx {}).lt.getD ridx false
  let pocOf (m : HevcMvf) (ll : Nat) : Option (Int × Bool) :=
    let ri := mvfRefIdx m ll
    let pocs := (pic.rpl.getD ll {}).poc
    if ri < 0 || ri.toNat >= pocs.size then none
    else some (pocs[ri.toNat]!, (pic.rpl.getD ll {}).lt.getD ri.toNat false)
  let matchUnscaled (m : HevcMvf) (ll : Nat) : Option (Int × Int) :=
    let bit := if ll == 0 then pfL0 else pfL1
    if (m.predFlag &&& bit) == 0 then none
    else
      match pocOf m ll with
      | some (poc, _) => if poc == targetPoc then some (mvfMv m ll) else none
      | none => none
  let matchScaled (m : HevcMvf) (ll : Nat) : Option (Int × Int) :=
    let bit := if ll == 0 then pfL0 else pfL1
    if (m.predFlag &&& bit) == 0 then none
    else
      match pocOf m ll with
      | none => none
      | some (poc, lt) =>
        if lt != targetLt then none
        else
          let mv := mvfMv m ll
          if !targetLt && poc != targetPoc then
            let td0 := pic.poc - poc
            let td := if td0 == 0 then 1 else td0
            some (mvScale mv td (pic.poc - targetPoc))
          else some mv
  let firstMatch (candsXy : Array (Int × Int × Bool))
      (fn : HevcMvf → Nat → Option (Int × Int)) : Option (Int × Int) := Id.run do
    for (px, py, ok) in candsXy do
      if ok then
        if let some m := mvfInterAt pic sps px py then
          for ll in [lx, 1 - lx] do
            if let some got := fn m ll then return some got
    return none
  let xA0 : Int := Int.ofNat x0 - 1
  let yA0 : Int := Int.ofNat (y0 + ph)
  let xA1 : Int := Int.ofNat x0 - 1
  let yA1 : Int := Int.ofNat (y0 + ph) - 1
  let a0Ok := na.candBottomLeft && yA0.toNat < sps.height &&
    zscanAvail sps pps x0 y0 xA0 yA0
  let left : Array (Int × Int × Bool) := #[(xA0, yA0, a0Ok), (xA1, yA1, na.candLeft)]
  let mut scaledFromLeft := false
  for (px, py, ok) in left do
    if ok && (mvfInterAt pic sps px py).isSome then scaledFromLeft := true
  let mxA0? := firstMatch left matchUnscaled
  let (mxA?, aOk) :=
    match mxA0? with
    | some v => (some v, true)
    | none =>
      match firstMatch left matchScaled with
      | some v => (some v, true)
      | none => (none, false)
  let xB0 : Int := Int.ofNat (x0 + pw)
  let yB0 : Int := Int.ofNat y0 - 1
  let xB1 : Int := Int.ofNat (x0 + pw) - 1
  let yB1 : Int := Int.ofNat y0 - 1
  let xB2 : Int := Int.ofNat x0 - 1
  let yB2 : Int := Int.ofNat y0 - 1
  let b0Ok := na.candUpRightSap && xB0.toNat < sps.width &&
    zscanAvail sps pps x0 y0 xB0 yB0
  let above : Array (Int × Int × Bool) :=
    #[(xB0, yB0, b0Ok), (xB1, yB1, na.candUp), (xB2, yB2, na.candUpLeft)]
  let mut mxA? := mxA?
  let mut aOk := aOk
  let mut mxB? := firstMatch above matchUnscaled
  let mut bOk := mxB?.isSome
  if !scaledFromLeft then
    if bOk then
      mxA? := mxB?
      aOk := true
    mxB? := firstMatch above matchScaled
    bOk := mxB?.isSome
  let mut cands : Array (Int × Int) := #[]
  if aOk then if let some v := mxA? then cands := cands.push v
  if bOk then
    if let some vb := mxB? then
      if !aOk || vb != mxA?.getD (0, 0) then cands := cands.push vb
  if cands.size < 2 && sh.sliceTemporalMvpEnabledFlag && mvpFlag == cands.size then
    if let some col := tmvpLx pic sps sh x0 y0 pw ph ridx lx then
      cands := cands.push col
  while cands.size < 2 do
    cands := cands.push (0, 0)
  return cands[Nat.min mvpFlag (cands.size - 1)]!

def decodeAmvp (ctx : HevcCtbCtx) (pic : HevcDecodedFrame) (sps : HevcSps) (pps : HevcPps)
    (sh : HevcSliceHeader) (c0 : HevcCabacReader) (st0 : Array Nat)
    (x0 y0 pw ph log2Cb : Nat) : Option (HevcMvf × HevcCabacReader × Array Nat) := do
  let ctDepth := sps.log2CtbSize - log2Cb
  let (inter0, c1, st1) :=
    if sh.sliceType == sliceB then decInterPredIdc c0 st0 pw ph ctDepth else (predL0, c0, st0)
  let inter := if pw + ph == 12 && inter0 == predBi then predL0 else inter0
  let pf := if inter == predL1 then pfL1 else if inter == predBi then pfBi else pfL0
  let mut mvf : HevcMvf := { predFlag := pf }
  let mut c := c1
  let mut st := st1
  let lxs : Array Nat := if inter == predL1 then #[1] else if inter == predL0 then #[0] else #[0, 1]
  for lx in lxs do
    let nb := sh.nbRefs.getD lx 0
    let (ridx, c', st') := if nb > 1 then decRefIdx c st nb else (0, c, st)
    c := c'
    st := st'
    mvf := mvfSet mvf lx (Int.ofNat ridx) (0, 0)
    let (mvd, c2, st2) ←
      if lx == 1 && sh.mvdL1ZeroFlag && inter == predBi then some ((0, 0), c, st)
      else
        match decMvd c st with
        | some (mx, my, c2, st2) => some ((mx, my), c2, st2)
        | none => none
    c := c2
    st := st2
    let (mvpFlag, c3, st3) := decMvpLxFlag c st
    c := c3
    st := st3
    let mvp := mvpList ctx pic sps pps sh x0 y0 pw ph lx ridx mvpFlag
    mvf := mvfSet mvf lx (Int.ofNat ridx) (mvp.1 + mvd.1, mvp.2 + mvd.2)
  some (mvf, c, st)

def decodePredictionUnit (ctx0 : HevcCtbCtx) (pic0 : HevcDecodedFrame) (sps : HevcSps)
    (pps : HevcPps) (sh : HevcSliceHeader) (c0 : HevcCabacReader) (st0 : Array Nat)
    (x0 y0 pw ph log2Cb predMode part partIdx : Nat) :
    Option (HevcCtbCtx × HevcDecodedFrame × Array ByteArray × HevcCabacReader × Array Nat) := do
  let (ctx, mvf, c, st) ←
    if predMode == modeSkip then
      let (idx, c1, st1) := decMergeIdx c0 st0 sh.maxNumMergeCand
      let mvf := (mergeCandidates ctx0 pic0 sps pps sh x0 y0 pw ph log2Cb part partIdx).getD idx mvfZero
      some (ctx0, mvf, c1, st1)
    else
      let (mf, c1, st1) := decMergeFlag c0 st0
      if mf != 0 then
        let (idx, c2, st2) := decMergeIdx c1 st1 sh.maxNumMergeCand
        let mvf := (mergeCandidates ctx0 pic0 sps pps sh x0 y0 pw ph log2Cb part partIdx).getD idx mvfZero
        some ({ ctx0 with mergeFlag := 1 }, mvf, c2, st2)
      else
        let (mvf, c2, st2) ← decodeAmvp ctx0 pic0 sps pps sh c1 st1 x0 y0 pw ph log2Cb
        some ({ ctx0 with mergeFlag := 0 }, mvf, c2, st2)
  let pic1 := storeMvfBlock pic0 sps x0 y0 pw ph mvf
  let planes := mcPu8 pic1.planes sps pps sh mvf pic1.rpl x0 y0 pw ph
  some (ctx, { pic1 with planes := planes }, planes, c, st)

def decodeInterPus (ctx0 : HevcCtbCtx) (pic0 : HevcDecodedFrame) (sps : HevcSps) (pps : HevcPps)
    (sh : HevcSliceHeader) (c0 : HevcCabacReader) (st0 : Array Nat)
    (x0 y0 log2Cb part : Nat) :
    Option (HevcCtbCtx × HevcDecodedFrame × HevcCabacReader × Array Nat) := do
  let cb := 1 <<< log2Cb
  let parts : Array (Nat × Nat × Nat × Nat) :=
    if part == part2Nx2N then #[(0, 0, cb, cb)]
    else if part == part2NxN then #[(0, 0, cb, cb >>> 1), (0, cb >>> 1, cb, cb >>> 1)]
    else if part == partNx2N then #[(0, 0, cb >>> 1, cb), (cb >>> 1, 0, cb >>> 1, cb)]
    else if part == partNxN then
      #[(0, 0, cb >>> 1, cb >>> 1), (cb >>> 1, 0, cb >>> 1, cb >>> 1),
        (0, cb >>> 1, cb >>> 1, cb >>> 1), (cb >>> 1, cb >>> 1, cb >>> 1, cb >>> 1)]
    else if part == part2NxnU then #[(0, 0, cb, cb >>> 2), (0, cb >>> 2, cb, (cb * 3) >>> 2)]
    else if part == part2NxnD then #[(0, 0, cb, (cb * 3) >>> 2), (0, (cb * 3) >>> 2, cb, cb >>> 2)]
    else if part == partNLx2N then #[(0, 0, cb >>> 2, cb), (cb >>> 2, 0, (cb * 3) >>> 2, cb)]
    else #[(0, 0, (cb * 3) >>> 2, cb), ((cb * 3) >>> 2, 0, cb >>> 2, cb)]
  let mut ctx := { ctx0 with mergeFlag := 0, cuX := x0, cuY := y0 }
  let mut pic := pic0
  let mut c := c0
  let mut st := st0
  for partIdx in [:parts.size] do
    let (ox, oy, pw, ph) := parts[partIdx]!
    let (ctx', pic', _, c', st') ←
      decodePredictionUnit ctx pic sps pps sh c st (x0 + ox) (y0 + oy) pw ph log2Cb modeInter part partIdx
    ctx := ctx'
    pic := pic'
    c := c'
    st := st'
  some (ctx, pic, c, st)

def decodePcmSamples (ctx : HevcCtbCtx) (pic0 : HevcDecodedFrame) (sps : HevcSps) (pps : HevcPps)
    (sh : HevcSliceHeader) (c0 : HevcCabacReader) (x0 y0 log2Cb : Nat) :
    Option (HevcDecodedFrame × HevcCabacReader) := do
  let cb := 1 <<< log2Cb
  let pcmInfo ← sps.pcm?
  let nbytes := (cb * cb * pcmInfo.bitDepth + 2 * ((cb >>> 1) * (cb >>> 1)) * pcmInfo.bitDepthChroma + 7) >>> 3
  let (pcm, c1) ← c0.readPcmAndReinit nbytes
  let mut pic := fillIpmBlock pic0 sps x0 y0 cb cb intraDc true
  if !sh.disableDeblockingFilterFlag then
    pic := updateDeblockBs ctx pic sps pps sh x0 y0 log2Cb
  if pcmInfo.loopFilterDisableFlag then
    pic := fillPcmFlagBlock pic sps x0 y0 log2Cb 1
  let mut gb := HevcBitReader.ofBytes pcm
  let bd := pcmInfo.bitDepth
  let bdc := pcmInfo.bitDepthChroma
  let mut yPlane := pic.planes.getD 0 ByteArray.empty
  for yy in [:cb] do
    let row := (y0 + yy) * sps.width + x0
    for xx in [:cb] do
      let (v, gb') ← gb.getBits bd
      gb := gb'
      yPlane := yPlane.set! (row + xx) (v <<< (8 - bd)).toUInt8
  let mut planes := pic.planes.set! 0 yPlane
  for cIdx in [1, 2] do
    let mut p := planes.getD cIdx ByteArray.empty
    for yy in [:(cb >>> 1)] do
      let row := ((y0 >>> 1) + yy) * (sps.width >>> 1) + (x0 >>> 1)
      for xx in [:(cb >>> 1)] do
        let (v, gb') ← gb.getBits bdc
        gb := gb'
        p := p.set! (row + xx) (v <<< (8 - bdc)).toUInt8
    planes := planes.set! cIdx p
  some ({ pic with planes := planes }, c1)

def decodeIntraModes (ctx0 : HevcCtbCtx) (pic0 : HevcDecodedFrame) (sps : HevcSps)
    (c0 : HevcCabacReader) (st0 : Array Nat) (x0 y0 log2Cb part : Nat) :
    HevcCtbCtx × HevcDecodedFrame × HevcCabacReader × Array Nat := Id.run do
  let split := part == partNxN
  let pb := (1 <<< log2Cb) >>> (if split then 1 else 0)
  let side := if split then 2 else 1
  let n := side * side
  let mut flags : Array Nat := Array.mkEmpty n
  let mut c := c0
  let mut st := st0
  for _ in [:n] do
    let (f, c', st') := decPrevIntraLumaPredFlag c st
    c := c'
    st := st'
    flags := flags.push f
  let mut modes : Array Nat := Array.mkEmpty n
  let mut pic := pic0
  for i in [:side] do
    for j in [:side] do
      let px := x0 + pb * j
      let py := y0 + pb * i
      let idx := modes.size
      let (m, c', st') :=
        if flags.getD idx 0 != 0 then
          let (mpmIdx, c') := decMpmIdx c
          (deriveLumaIntraMode ctx0 pic sps px py true mpmIdx 0, c', st)
        else
          let (rem, c') := decRemIntraLumaPredMode c
          (deriveLumaIntraMode ctx0 pic sps px py false 0 rem, c', st)
      c := c'
      st := st'
      modes := modes.push m
      pic := fillIpmBlock pic sps px py pb pb m true
  let (chromaMode, c2, st2) := decIntraChromaPredMode c st
  let luma0 := modes.getD 0 intraDc
  let chromaPred :=
    if chromaMode == 4 then luma0
    else
      let mapped := hevcIntraChromaModes.getD chromaMode 0
      if luma0 == mapped then 34 else mapped
  return ({ ctx0 with chromaPredMode := chromaPred, intraLumaModes := modes }, pic, c2, st2)

def qpyPredAt (ctx : HevcCtbCtx) (pic : HevcDecodedFrame) (sps : HevcSps) (pps : HevcPps)
    (sh : HevcSliceHeader) (x0 y0 : Nat) : Int × Bool :=
  let ctbMask := (1 <<< sps.log2CtbSize) - 1
  let qgMask := (1 <<< (sps.log2CtbSize - pps.diffCuQpDeltaDepth)) - 1
  let xQg := x0 - (x0 &&& qgMask)
  let yQg := y0 - (y0 &&& qgMask)
  let pred0 := if ctx.firstQpGroup || (xQg == 0 && yQg == 0) then sh.sliceQp else ctx.qpyPred
  let firstNext := if ctx.firstQpGroup || (xQg == 0 && yQg == 0) then !ctx.cuQpDeltaCoded else ctx.firstQpGroup
  let availA := (x0 &&& ctbMask) != 0 && (xQg &&& ctbMask) != 0
  let availB := (y0 &&& ctbMask) != 0 && (yQg &&& ctbMask) != 0
  let qa :=
    if availA then
      pic.qpY.getD ((yQg >>> sps.log2MinCbSize) * sps.minCbWidth + ((xQg >>> sps.log2MinCbSize) - 1)) pred0
    else pred0
  let qb :=
    if availB then
      pic.qpY.getD (((yQg >>> sps.log2MinCbSize) - 1) * sps.minCbWidth + (xQg >>> sps.log2MinCbSize)) pred0
    else pred0
  (asrInt (qa + qb + 1) 1, firstNext)

def setCbfLumaBlock (pic0 : HevcDecodedFrame) (sps : HevcSps) (x0 y0 log2Size : Nat) :
    HevcDecodedFrame := Id.run do
  let step := 1 <<< sps.log2MinTbSize
  let mut tab := pic0.cbfLuma
  let mut yy := y0
  while yy < y0 + (1 <<< log2Size) do
    let mut xx := x0
    while xx < x0 + (1 <<< log2Size) do
      tab := tab.set! ((yy >>> sps.log2MinTbSize) * sps.minTbWidth + (xx >>> sps.log2MinTbSize)) 1
      xx := xx + step
    yy := yy + step
  return { pic0 with cbfLuma := tab }

def applyResidualBlock (pic0 : HevcDecodedFrame) (sps : HevcSps) (pps : HevcPps)
    (c0 : HevcCabacReader) (st0 : Array Nat) (x0 y0 log2Size scanIdx cIdx predMode tqb : Nat)
    (qpY qpCb qpCr : Int) (isIntra : Bool) :
    Option (HevcDecodedFrame × HevcCabacReader × Array Nat) := do
  let (res, c1, st1) ← decodeResidualCoding c0 st0 sps pps log2Size scanIdx cIdx predMode tqb qpY qpCb qpCr
  let planeIdx := cIdx
  let (stride, dstX, dstY, lg) :=
    if cIdx == 0 then (sps.width, x0, y0, log2Size)
    else (sps.width >>> 1, x0 >>> 1, y0 >>> 1, log2Size)
  let plane := pic0.planes.getD planeIdx ByteArray.empty
  let plane' := inverseTransformAndAdd plane stride dstX dstY res.coeffs lg cIdx isIntra
    res.transformSkipFlag tqb (if res.dcOnly then 0 else res.colLimit)
  some ({ pic0 with planes := pic0.planes.set! planeIdx plane' }, c1, st1)

def decodeTransformUnit (ctx : HevcCtbCtx) (pic0 : HevcDecodedFrame) (sps : HevcSps) (pps : HevcPps)
    (sh : HevcSliceHeader) (c0 : HevcCabacReader) (st0 : Array Nat)
    (x0 y0 xBase yBase cbX cbY _log2Cb log2Size blkIdx cbfLuma0 : Nat)
    (cbfCb cbfCr : Array Nat) (predMode tqb : Nat) :
    Option (HevcCtbCtx × HevcDecodedFrame × HevcCabacReader × Array Nat) := do
  let mode := if predMode == modeIntra then ctx.tuLumaMode else intraDc
  let mut pic := pic0
  if predMode == modeIntra then
    let na := computeNeighAvail ctx sps x0 y0 (1 <<< log2Size) (1 <<< log2Size)
    let plane := intraPred8 (pic.planes.getD 0 ByteArray.empty) sps.width sps pps pic.tabMvf na
      x0 y0 log2Size 0 mode
    pic := { pic with planes := pic.planes.set! 0 plane }
  let cbfChroma := cbfCb.getD 0 0 != 0 || cbfCr.getD 0 0 != 0
  let mut ctx := ctx
  let mut c := c0
  let mut st := st0
  if cbfLuma0 != 0 || cbfChroma then
    if pps.cuQpDeltaEnabledFlag && !ctx.cuQpDeltaCoded then
      let (delta, c', st') ← decCuQpDelta c st
      c := c'
      st := st'
      let (qpPred, firstNext) := qpyPredAt ctx pic sps pps sh cbX cbY
      let qpY := if delta != 0 then (qpPred + delta + 52) % 52 else qpPred
      ctx := { ctx with cuQpDelta := delta, cuQpDeltaCoded := true, qpY := qpY, firstQpGroup := firstNext }
  let (scan, scanC) :=
    if predMode == modeIntra && log2Size < 4 then
      let s := if 6 <= mode && mode <= 14 then scanVert else if 22 <= mode && mode <= 30 then scanHoriz else scanDiag
      let cm := ctx.chromaPredMode
      let sc := if 6 <= cm && cm <= 14 then scanVert else if 22 <= cm && cm <= 30 then scanHoriz else scanDiag
      (s, sc)
    else (scanDiag, scanDiag)
  let qpCb := mapQpC (clipInt (ctx.qpY + pps.cbQpOffset + sh.cbQpOffset) 0 57)
  let qpCr := mapQpC (clipInt (ctx.qpY + pps.crQpOffset + sh.crQpOffset) 0 57)
  if cbfLuma0 != 0 then
    let (pic', c', st') ← applyResidualBlock pic sps pps c st x0 y0 log2Size scan 0 predMode tqb
      ctx.qpY qpCb qpCr (predMode == modeIntra)
    pic := pic'
    c := c'
    st := st'
  if log2Size > 2 then
    if predMode == modeIntra then
      let na := computeNeighAvail ctx sps x0 y0 (1 <<< log2Size) (1 <<< log2Size)
      for cIdx in [1, 2] do
        let plane := intraPred8 (pic.planes.getD cIdx ByteArray.empty) (sps.width >>> 1) sps pps pic.tabMvf na
          x0 y0 (log2Size - 1) cIdx ctx.chromaPredMode
        pic := { pic with planes := pic.planes.set! cIdx plane }
    for (cIdx, cbf) in [1, 2].zip [cbfCb.getD 0 0, cbfCr.getD 0 0] do
      if cbf != 0 then
        let (pic', c', st') ← applyResidualBlock pic sps pps c st x0 y0 (log2Size - 1) scanC cIdx predMode tqb
          ctx.qpY qpCb qpCr (predMode == modeIntra)
        pic := pic'
        c := c'
        st := st'
  else if blkIdx == 3 then
    if predMode == modeIntra then
      let na := computeNeighAvail ctx sps xBase yBase 8 8
      for cIdx in [1, 2] do
        let plane := intraPred8 (pic.planes.getD cIdx ByteArray.empty) (sps.width >>> 1) sps pps pic.tabMvf na
          xBase yBase 2 cIdx ctx.chromaPredMode
        pic := { pic with planes := pic.planes.set! cIdx plane }
    for (cIdx, cbf) in [1, 2].zip [cbfCb.getD 0 0, cbfCr.getD 0 0] do
      if cbf != 0 then
        let (pic', c', st') ← applyResidualBlock pic sps pps c st xBase yBase 2 scanC cIdx predMode tqb
          ctx.qpY qpCb qpCr (predMode == modeIntra)
        pic := pic'
        c := c'
        st := st'
  some (ctx, pic, c, st)

def decodeTransformTree (ctx0 : HevcCtbCtx) (pic0 : HevcDecodedFrame) (sps : HevcSps) (pps : HevcPps)
    (sh : HevcSliceHeader) (c0 : HevcCabacReader) (st0 : Array Nat)
    (x0 y0 xBase yBase cbX cbY log2Cb log2Size trafoDepth blkIdx predMode part tqb : Nat)
    (cbfCb0 cbfCr0 : Array Nat) (maxDepth : Nat) :
    Nat → Option (HevcCtbCtx × HevcDecodedFrame × HevcCabacReader × Array Nat)
  | 0 => none
  | fuel + 1 => do
    let tuMode :=
      if predMode == modeIntra && part == partNxN && trafoDepth == 1 then
        ctx0.intraLumaModes.getD blkIdx intraDc
      else if trafoDepth == 0 && predMode == modeIntra then
        ctx0.intraLumaModes.getD 0 intraDc
      else ctx0.tuLumaMode
    let ctx1 := { ctx0 with tuLumaMode := tuMode }
    let intraSplit := predMode == modeIntra && part == partNxN
    let mut c := c0
    let mut st := st0
    let mut split := false
    if log2Size <= sps.log2MaxTrafoSize && log2Size > sps.log2MinTbSize &&
        trafoDepth < maxDepth && !(intraSplit && trafoDepth == 0) then
      let (sp, c', st') := decSplitTransformFlag c st log2Size
      c := c'
      st := st'
      split := sp != 0
    else
      let interSplit := sps.maxTrafoDepthInter == 0 && predMode != modeIntra &&
        part != part2Nx2N && trafoDepth == 0
      split := log2Size > sps.log2MaxTrafoSize || (intraSplit && trafoDepth == 0) || interSplit
    let mut cbfCb := cbfCb0
    let mut cbfCr := cbfCr0
    if log2Size > 2 then
      if trafoDepth == 0 || cbfCb.getD 0 0 != 0 then
        let (v, c', st') := decCbfCbCr c st trafoDepth
        c := c'
        st := st'
        cbfCb := #[v, 0]
      if trafoDepth == 0 || cbfCr.getD 0 0 != 0 then
        let (v, c', st') := decCbfCbCr c st trafoDepth
        c := c'
        st := st'
        cbfCr := #[v, 0]
    if split then
      let off := 1 <<< (log2Size - 1)
      let offs : Array (Nat × Nat) := #[(0, 0), (off, 0), (0, off), (off, off)]
      let mut ctx := ctx1
      let mut pic := pic0
      for i in [:4] do
        let (ox, oy) := offs[i]!
        let (ctx', pic', c', st') ← decodeTransformTree ctx pic sps pps sh c st
          (x0 + ox) (y0 + oy) x0 y0 cbX cbY log2Cb (log2Size - 1) (trafoDepth + 1) i
          predMode part tqb cbfCb cbfCr maxDepth fuel
        ctx := ctx'
        pic := pic'
        c := c'
        st := st'
      some (ctx, pic, c, st)
    else
      let mut cbfLuma := 1
      if predMode == modeIntra || trafoDepth != 0 || cbfCb.getD 0 0 != 0 || cbfCr.getD 0 0 != 0 then
        let (v, c', st') := decCbfLuma c st trafoDepth
        c := c'
        st := st'
        cbfLuma := v
      let (ctx2, pic1, c2, st2) ← decodeTransformUnit ctx1 pic0 sps pps sh c st
        x0 y0 xBase yBase cbX cbY log2Cb log2Size blkIdx cbfLuma cbfCb cbfCr predMode tqb
      let mut pic2 := if cbfLuma != 0 then setCbfLumaBlock pic1 sps x0 y0 log2Size else pic1
      if !sh.disableDeblockingFilterFlag then
        pic2 := updateDeblockBs ctx2 pic2 sps pps sh x0 y0 log2Size
        if tqb != 0 then pic2 := fillPcmFlagBlock pic2 sps x0 y0 log2Size 2
      some (ctx2, pic2, c2, st2)

def updateQpyPredAtEdge (ctx : HevcCtbCtx) (sps : HevcSps) (pps : HevcPps)
    (x0 y0 log2Cb : Nat) : HevcCtbCtx :=
  let qpMask := (1 <<< (sps.log2CtbSize - pps.diffCuQpDeltaDepth)) - 1
  let cb := 1 <<< log2Cb
  if ((x0 + cb) &&& qpMask) == 0 && ((y0 + cb) &&& qpMask) == 0 then
    { ctx with qpyPred := ctx.qpY }
  else ctx

def decodeCodingUnit (ctx0 : HevcCtbCtx) (pic0 : HevcDecodedFrame) (sps : HevcSps) (pps : HevcPps)
    (sh : HevcSliceHeader) (c0 : HevcCabacReader) (st0 : Array Nat)
    (x0 y0 log2Cb depth : Nat) :
    Option (HevcCtbCtx × HevcDecodedFrame × HevcCabacReader × Array Nat) := do
  let cb := 1 <<< log2Cb
  let ctbMask := (1 <<< sps.log2CtbSize) - 1
  let mut ctx := { ctx0 with ctDepth := depth }
  if !pps.cuQpDeltaEnabledFlag then ctx := { ctx with qpY := sh.sliceQp }
  let mut pic := setCtDepthBlock pic0 sps x0 y0 log2Cb depth
  let mut c := c0
  let mut st := st0
  let mut tqb := 0
  if pps.transquantBypassEnableFlag then
    let (v, c', st') := decCuTransquantBypass c st
    c := c'
    st := st'
    tqb := v
    if tqb != 0 then pic := fillPcmFlagBlock pic sps x0 y0 log2Cb 2
  let mut skip := 0
  if sh.sliceType != sliceI then
    let sl := if ctx.ctbLeft || (x0 &&& ctbMask) != 0 then skipAt pic sps (Int.ofNat x0 - 1) (Int.ofNat y0) else 0
    let su := if ctx.ctbUp || (y0 &&& ctbMask) != 0 then skipAt pic sps (Int.ofNat x0) (Int.ofNat y0 - 1) else 0
    let (sk, c', st') := decSkipFlag c st sl su
    c := c'
    st := st'
    skip := sk
  pic := fillSkipBlock pic sps x0 y0 log2Cb skip
  if skip != 0 then
    let (ctx1, pic1, _, c1, st1) ← decodePredictionUnit ctx pic sps pps sh c st
      x0 y0 cb cb log2Cb modeSkip part2Nx2N 0
    ctx := ctx1
    pic := fillIpmBlock pic1 sps x0 y0 cb cb intraDc false
    if !sh.disableDeblockingFilterFlag then
      pic := updateDeblockBs ctx pic sps pps sh x0 y0 log2Cb
    if pps.cuQpDeltaEnabledFlag && !ctx.cuQpDeltaCoded then
      let (qpPred, firstNext) := qpyPredAt ctx pic sps pps sh x0 y0
      ctx := { ctx with qpY := qpPred, firstQpGroup := firstNext }
    pic := setQpCbBlock pic sps x0 y0 log2Cb ctx.qpY
    ctx := updateQpyPredAtEdge ctx sps pps x0 y0 log2Cb
    some (ctx, pic, c1, st1)
  else
    let mut predMode := modeIntra
    if sh.sliceType != sliceI then
      let (pm, c', st') := decPredMode c st
      c := c'
      st := st'
      predMode := pm
    let mut part := part2Nx2N
    if predMode != modeIntra || log2Cb == sps.log2MinCbSize then
      let (pt, c', st') := decPartMode c st log2Cb sps.log2MinCbSize predMode (if sps.ampEnabledFlag then 1 else 0)
      c := c'
      st := st'
      part := pt
    let mut pcm := false
    if predMode == modeIntra then
      if part == part2Nx2N && sps.pcmEnabledFlag then
        if let some pcmInfo := sps.pcm? then
          if pcmInfo.log2MinPcmCbSize <= log2Cb && log2Cb <= pcmInfo.log2MaxPcmCbSize then
            let (pf, c') := decPcmFlag c
            c := c'
            pcm := pf != 0
      if pcm then
        let (picPcm, cPcm) ← decodePcmSamples ctx pic sps pps sh c x0 y0 log2Cb
        pic := picPcm
        c := cPcm
      else
        let (ctxI, picI, cI, stI) := decodeIntraModes ctx pic sps c st x0 y0 log2Cb part
        ctx := ctxI
        pic := picI
        c := cI
        st := stI
    else
      pic := fillIpmBlock pic sps x0 y0 cb cb intraDc false
      let (ctxP, picP, cP, stP) ← decodeInterPus ctx pic sps pps sh c st x0 y0 log2Cb part
      ctx := ctxP
      pic := picP
      c := cP
      st := stP
    if !pcm then
      let mut rqtRootCbf := 1
      if predMode != modeIntra && !(part == part2Nx2N && ctx.mergeFlag != 0) then
        let (rc, c', st') := decNoResidualDataFlag c st
        c := c'
        st := st'
        rqtRootCbf := rc
      if rqtRootCbf != 0 then
        let intraSplit := predMode == modeIntra && part == partNxN
        let maxDepth :=
          if predMode == modeIntra then sps.maxTrafoDepthIntra + (if intraSplit then 1 else 0)
          else sps.maxTrafoDepthInter
        let (ctxT, picT, cT, stT) ← decodeTransformTree ctx pic sps pps sh c st
          x0 y0 x0 y0 x0 y0 log2Cb log2Cb 0 0 predMode part tqb #[0, 0] #[0, 0] maxDepth 8
        ctx := ctxT
        pic := picT
        c := cT
        st := stT
      else if !sh.disableDeblockingFilterFlag then
        pic := updateDeblockBs ctx pic sps pps sh x0 y0 log2Cb
    if pps.cuQpDeltaEnabledFlag && !ctx.cuQpDeltaCoded then
      let (qpPred, firstNext) := qpyPredAt ctx pic sps pps sh x0 y0
      ctx := { ctx with qpY := qpPred, firstQpGroup := firstNext }
    pic := setQpCbBlock pic sps x0 y0 log2Cb ctx.qpY
    ctx := updateQpyPredAtEdge ctx sps pps x0 y0 log2Cb
    some (ctx, pic, c, st)

def decodeCodingTree (ctx0 : HevcCtbCtx) (pic0 : HevcDecodedFrame) (sps : HevcSps) (pps : HevcPps)
    (sh : HevcSliceHeader) (c0 : HevcCabacReader) (st0 : Array Nat)
    (x0 y0 log2Cb depth : Nat) :
    Nat → Option (Bool × HevcCtbCtx × HevcDecodedFrame × HevcCabacReader × Array Nat)
  | 0 => none
  | fuel + 1 => do
    let w := sps.width
    let h := sps.height
    let cb := 1 <<< log2Cb
    let ctbMask := (1 <<< sps.log2CtbSize) - 1
    let mut ctx := { ctx0 with ctDepth := depth }
    let mut c := c0
    let mut st := st0
    let mut split := false
    if x0 + cb <= w && y0 + cb <= h && log2Cb > sps.log2MinCbSize then
      let dl := if ctx.ctbLeft || (x0 &&& ctbMask) != 0 then ctDepthAt pic0 sps (Int.ofNat x0 - 1) (Int.ofNat y0) else 0
      let dt := if ctx.ctbUp || (y0 &&& ctbMask) != 0 then ctDepthAt pic0 sps (Int.ofNat x0) (Int.ofNat y0 - 1) else 0
      let (sp, c', st') := decSplitCuFlag c st dl dt depth
      c := c'
      st := st'
      split := sp != 0
    else
      split := log2Cb > sps.log2MinCbSize
    if pps.cuQpDeltaEnabledFlag && log2Cb >= sps.log2CtbSize - pps.diffCuQpDeltaDepth then
      ctx := { ctx with cuQpDeltaCoded := false, cuQpDelta := 0 }
    if split then
      let half := log2Cb - 1
      let off := 1 <<< half
      let offs : Array (Nat × Nat) := #[(0, 0), (off, 0), (0, off), (off, off)]
      let mut more := true
      let mut pic := pic0
      for i in [:4] do
        let (ox, oy) := offs[i]!
        if more && x0 + ox < w && y0 + oy < h then
          let (m', ctx', pic', c', st') ← decodeCodingTree ctx pic sps pps sh c st
            (x0 + ox) (y0 + oy) half (depth + 1) fuel
          more := m'
          ctx := ctx'
          pic := pic'
          c := c'
          st := st'
      ctx := updateQpyPredAtEdge ctx sps pps x0 y0 log2Cb
      some (more, ctx, pic, c, st)
    else
      let (ctx1, pic1, c1, st1) ← decodeCodingUnit ctx pic0 sps pps sh c st x0 y0 log2Cb depth
      let atCtbEdge := (((x0 + cb) &&& ctbMask) == 0 || x0 + cb >= w) &&
        (((y0 + cb) &&& ctbMask) == 0 || y0 + cb >= h)
      if atCtbEdge then
        let (term, c2) := c1.decodeTerminate
        some (term == 0, ctx1, pic1, c2, st1)
      else some (true, ctx1, pic1, c1, st1)

def decodeSaoCtb (ctx : HevcCtbCtx) (pic0 : HevcDecodedFrame) (sps : HevcSps)
    (sh : HevcSliceHeader) (c0 : HevcCabacReader) (st0 : Array Nat) (rs : Nat) :
    HevcDecodedFrame × HevcCabacReader × Array Nat := Id.run do
  if !sps.saoEnabled || (!sh.saoLumaFlag && !sh.saoChromaFlag) then
    return (pic0, c0, st0)
  let mut c := c0
  let mut st := st0
  let mut mergeLeft := false
  if ctx.ctbLeft then
    let (f, c', st') := decSaoMergeFlag c st
    c := c'
    st := st'
    mergeLeft := f != 0
  if mergeLeft then
    let prev := pic0.sao.getD (rs - 1) {}
    return ({ pic0 with sao := pic0.sao.set! rs prev }, c, st)
  let mut mergeUp := false
  if ctx.ctbUp then
    let (f, c', st') := decSaoMergeFlag c st
    c := c'
    st := st'
    mergeUp := f != 0
  if mergeUp then
    let prev := pic0.sao.getD (rs - sps.ctbWidth) {}
    return ({ pic0 with sao := pic0.sao.set! rs prev }, c, st)
  let mut sao := pic0.sao.getD rs {}
  for cIdx in [:3] do
    let active := if cIdx == 0 then sh.saoLumaFlag else sh.saoChromaFlag
    if active then
      if cIdx == 2 then
        sao := { sao with
          typeIdx := sao.typeIdx.set! 2 (sao.typeIdx.getD 1 0)
          eoClass := sao.eoClass.set! 2 (sao.eoClass.getD 1 0) }
      else
        let (ti, c', st') := decSaoTypeIdx c st
        c := c'
        st := st'
        sao := { sao with typeIdx := sao.typeIdx.set! cIdx ti }
      let ti := sao.typeIdx.getD cIdx 0
      if ti != 0 then
        let mut offs : Array Int := Array.mkEmpty 4
        for _ in [:4] do
          let (ov, c') := decSaoOffsetAbs c 8
          c := c'
          offs := offs.push (Int.ofNat ov)
        let mut row := sao.offsetVal.getD cIdx #[0, 0, 0, 0, 0]
        if ti == saoBand then
          for i in [:4] do
            let mut v := offs[i]!
            if v != 0 then
              let (sg, c') := c.decodeBypass
              c := c'
              if sg != 0 then v := -v
            row := row.set! (i + 1) v
          let (bp, c') := decSaoBandPosition c
          c := c'
          sao := { sao with
            offsetVal := sao.offsetVal.set! cIdx row
            bandPosition := sao.bandPosition.set! cIdx bp }
        else
          if cIdx != 2 then
            let (eo, c') := decSaoEoClass c
            c := c'
            sao := { sao with eoClass := sao.eoClass.set! cIdx eo }
          row := (((row.set! 1 (offs[0]!)).set! 2 (offs[1]!)).set! 3 (-offs[2]!)).set! 4 (-offs[3]!)
          sao := { sao with offsetVal := sao.offsetVal.set! cIdx row }
  return ({ pic0 with sao := pic0.sao.set! rs sao }, c, st)

def decodeCtb (ctx0 : HevcCtbCtx) (pic0 : HevcDecodedFrame) (sps : HevcSps) (pps : HevcPps)
    (sh : HevcSliceHeader) (c0 : HevcCabacReader) (st0 : Array Nat)
    (rs xCtb yCtb : Nat) :
    Option (Bool × HevcCtbCtx × HevcDecodedFrame × HevcCabacReader × Array Nat) := do
  let x0 := xCtb <<< sps.log2CtbSize
  let y0 := yCtb <<< sps.log2CtbSize
  let ctbSize := 1 <<< sps.log2CtbSize
  let inSlice : Int := Int.ofNat rs - Int.ofNat sh.sliceAddrRs
  let ts := pps.ctbAddrRsToTs.getD rs 0
  let leftTile := xCtb > 0 && pps.tilesEnabledFlag &&
    pps.tileId.getD ts 0 != pps.tileId.getD (pps.ctbAddrRsToTs.getD (rs - 1) 0) 0
  let upTile := yCtb > 0 && pps.tilesEnabledFlag &&
    pps.tileId.getD ts 0 != pps.tileId.getD (pps.ctbAddrRsToTs.getD (rs - sps.ctbWidth) 0) 0
  let ctbLeft := xCtb > 0 && inSlice > 0 && !leftTile
  let ctbUp := yCtb > 0 && inSlice >= Int.ofNat sps.ctbWidth && !upTile
  let ctbUpRight := yCtb > 0 && inSlice + 1 >= Int.ofNat sps.ctbWidth && xCtb + 1 < sps.ctbWidth &&
    pps.tileId.getD ts 0 == pps.tileId.getD (pps.ctbAddrRsToTs.getD (rs + 1 - sps.ctbWidth) 0) 0
  let ctbUpLeft := xCtb > 0 && yCtb > 0 && inSlice - 1 >= Int.ofNat sps.ctbWidth &&
    pps.tileId.getD ts 0 == pps.tileId.getD (pps.ctbAddrRsToTs.getD (rs - 1 - sps.ctbWidth) 0) 0
  let endY := Nat.min (yCtb * ctbSize + ctbSize) sps.height
  let bndLeftSlice :=
    if !pps.tilesEnabledFlag then inSlice <= 0
    else xCtb > 0 && pic0.sliceAddr.getD (rs - 1) (-1) != Int.ofNat sh.sliceAddrRs
  let bndUpperSlice :=
    if !pps.tilesEnabledFlag then inSlice < Int.ofNat sps.ctbWidth
    else yCtb > 0 && pic0.sliceAddr.getD (rs - sps.ctbWidth) (-1) != Int.ofNat sh.sliceAddrRs
  let ctx1 : HevcCtbCtx := { ctx0 with
    ctbLeft := ctbLeft
    ctbUp := ctbUp
    ctbUpRight := ctbUpRight
    ctbUpLeft := ctbUpLeft
    endOfTilesY := endY
    boundaryLeftSlice := bndLeftSlice
    boundaryUpperSlice := bndUpperSlice
    boundaryLeftTile := leftTile
    boundaryUpperTile := upTile }
  let (pic1, c1, st1) := decodeSaoCtb ctx1 pic0 sps sh c0 st0 rs
  decodeCodingTree ctx1 pic1 sps pps sh c1 st1 x0 y0 sps.log2CtbSize 0 8

def decodeSlices (dpb : Array HevcDecodedFrame) (pic0 : HevcDecodedFrame)
    (sps : HevcSps) (pps : HevcPps) (headers : Array HevcSliceHeader) :
    Option HevcDecodedFrame := do
  let mut pic := pic0
  let mut ctx : HevcCtbCtx := {}
  let mut sliceRpl : Array HevcRpl := #[{}, {}]
  let mut wppSaved? : Option (Array Nat) := none
  for sh in headers do
    if !sh.dependentSliceSegmentFlag then
      let rpl := buildSliceRpl dpb sps sh
      pic := { pic with rpl := rpl }
      sliceRpl := rpl
      ctx := { ctx with firstQpGroup := true, qpyPred := sh.sliceQp, qpY := sh.sliceQp }
    let cabacInit := if sh.cabacInitFlag then 1 else 0
    let mut cabacState := initCabacStates sh.sliceType cabacInit sh.sliceQp
    let mut subIdx := 0
    if sh.substreams.isEmpty then none
    let mut cabac ← HevcCabacReader.init? (sh.substreams.getD 0 ByteArray.empty) 0
    let addr0 := sh.sliceCtbAddrRs
    if addr0 >= pps.ctbAddrRsToTs.size then none
    let ts0 := pps.ctbAddrRsToTs[addr0]!
    let mut endTilesX := sps.width
    if pps.tilesEnabledFlag && !pps.entropyCodingSyncEnabledFlag then
      let xCtb0 := addr0 % sps.ctbWidth
      let idxX := pps.colIdxX.getD xCtb0 0
      endTilesX := (xCtb0 + pps.columnWidth.getD idxX 1) <<< sps.log2CtbSize
    ctx := { ctx with endOfTilesX := endTilesX }
    let mut ts := ts0
    let mut keepGoing := true
    while ts < sps.ctbSize && keepGoing do
      let rs := pps.ctbAddrTsToRs.getD ts 0
      let xCtb := rs % sps.ctbWidth
      let yCtb := rs / sps.ctbWidth
      let newTile := pps.tilesEnabledFlag && ts > ts0 &&
        pps.tileId.getD ts 0 != pps.tileId.getD (ts - 1) 0
      let newRow := pps.entropyCodingSyncEnabledFlag && xCtb == 0 && ts > ts0
      if newTile && !pps.entropyCodingSyncEnabledFlag then
        let idxX := pps.colIdxX.getD xCtb 0
        ctx := { ctx with endOfTilesX := (xCtb + pps.columnWidth.getD idxX 1) <<< sps.log2CtbSize }
      if newTile || newRow then
        if sh.numEntryPointOffsets > 0 then
          subIdx := subIdx + 1
          if subIdx >= sh.substreams.size then none
          let cNext ← HevcCabacReader.init? (sh.substreams[subIdx]!) 0
          cabac := cNext
        else
          let (_, cTerm) := cabac.decodeTerminate
          let cRe ← cTerm.reinit
          cabac := cRe
        cabacState :=
          if newTile || sps.ctbWidth == 1 then initCabacStates sh.sliceType cabacInit sh.sliceQp
          else
            match wppSaved? with
            | some saved => saved
            | none => initCabacStates sh.sliceType cabacInit sh.sliceQp
        ctx := { ctx with qpyPred := sh.sliceQp, firstQpGroup := true }
      pic := { pic with
        sliceAddr := pic.sliceAddr.set! rs (Int.ofNat sh.sliceAddrRs)
        lfase := pic.lfase.set! rs sh.sliceLoopFilterAcrossSlicesEnabledFlag
        deblock := pic.deblock.set! rs { betaOffset := sh.betaOffset, tcOffset := sh.tcOffset }
        rplTab := pic.rplTab.set! rs (some sliceRpl) }
      let (more, ctx', pic', cabac', st') ← decodeCtb ctx pic sps pps sh cabac cabacState rs xCtb yCtb
      ctx := ctx'
      pic := pic'
      cabac := cabac'
      cabacState := st'
      if !more then
        keepGoing := false
      else
        if pps.entropyCodingSyncEnabledFlag && (xCtb == 1 || (sps.ctbWidth == 1 && xCtb == 0)) then
          wppSaved? := some cabacState
      ts := ts + 1
  some pic

structure HevcDecoderState where
  vpsMap       : Array (Option HevcVps) := Array.replicate 16 none
  spsMap       : Array (Option HevcSps) := Array.replicate 16 none
  ppsMap       : Array (Option HevcPps) := Array.replicate 64 none
  dpb          : Array HevcDecodedFrame := #[]
  pocTid0      : Int := 0
  prevIndepSh? : Option HevcSliceHeader := none
  output       : Array HevcDecodedFrame := #[]
  deriving Inhabited

def bumpDpb (dpb0 output0 : Array HevcDecodedFrame) (sps : HevcSps) (pic : HevcDecodedFrame)
    (sh : HevcSliceHeader) (pocTid0 : Int) :
    Array HevcDecodedFrame × Array HevcDecodedFrame × Int := Id.run do
  let mut dpb := sortFramesByPoc (dpb0.push pic)
  let mut output := output0
  let maxSub := if sps.maxDecPicBuffering.isEmpty then 0 else sps.maxDecPicBuffering.size - 1
  let maxBuf := sps.maxDecPicBuffering.getD maxSub 1
  let reorder := sps.numReorderPics.getD maxSub 0
  let mut fuel := dpb.size + 2
  while fuel > 0 do
    fuel := fuel - 1
    let mut pendingCnt := 0
    let mut oldestIdx? : Option Nat := none
    for idx in [:dpb.size] do
      let f := dpb[idx]!
      if f.outputFlag && !f.outputted then
        pendingCnt := pendingCnt + 1
        match oldestIdx? with
        | none => oldestIdx? := some idx
        | some oi => if f.poc < (dpb[oi]!).poc then oldestIdx? := some idx
    match oldestIdx? with
    | none => fuel := 0
    | some oi =>
      if pendingCnt > reorder || dpb.size > maxBuf then
        let f := { dpb[oi]! with outputted := true }
        output := output.push f
        dpb := dpb.set! oi f
        let mut nextDpb : Array HevcDecodedFrame := #[]
        for g in dpb do
          if g.referenced || (g.outputFlag && !g.outputted) then nextDpb := nextDpb.push g
        dpb := nextDpb
      else
        fuel := 0
  let nextPocTid0 :=
    if sh.tid == 0 && sh.nalType != 0 && sh.nalType != 2 && sh.nalType != 4 &&
        sh.nalType != 6 && sh.nalType != 7 && sh.nalType != 8 && sh.nalType != 9 then
      sh.poc
    else pocTid0
  return (dpb, output, nextPocTid0)

def flushDpb (st : HevcDecoderState) : HevcDecoderState := Id.run do
  let sorted := sortFramesByPoc st.dpb
  let mut out := st.output
  let mut dpbNext : Array HevcDecodedFrame := #[]
  for f in sorted do
    if f.outputFlag && !f.outputted then
      let f' := { f with outputted := true }
      out := out.push f'
      dpbNext := dpbNext.push f'
    else
      dpbNext := dpbNext.push f
  return { st with dpb := dpbNext, output := out }

def decodePictureSlices (st0 : HevcDecoderState) (slices : Array (Nat × Nat × ByteArray)) :
    Option HevcDecoderState := do
  if slices.isEmpty then some st0
  else
    let mut prevSh? := st0.prevIndepSh?
    let mut headers : Array HevcSliceHeader := Array.mkEmpty slices.size
    for (nalType, tid, payload) in slices do
      let sh ← parseSliceHeader payload nalType tid st0.spsMap st0.ppsMap prevSh? st0.pocTid0
      if !sh.dependentSliceSegmentFlag then prevSh? := some sh
      headers := headers.push sh
    let sh0 := headers[0]!
    if sh0.spsId >= st0.spsMap.size || sh0.ppsId >= st0.ppsMap.size then none
    let sps ← st0.spsMap[sh0.spsId]!
    let pps ← st0.ppsMap[sh0.ppsId]!
    let mut dpb := st0.dpb
    if isIrap sh0.nalType && sh0.noOutputOfPriorPicsFlag then
      if isBla sh0.nalType || isIdr sh0.nalType then dpb := #[]
    dpb := markDpbRps dpb sps sh0
    let pic0 := newDecodedFrame sps sh0
    let mut pic ← decodeSlices dpb pic0 sps pps headers
    if !sh0.disableDeblockingFilterFlag then
      let planes := deblockFrame8 pic.planes sps pps pic.qpY pic.isPcm pic.deblock
        pic.vbs pic.hbs pic.bsW
      pic := { pic with planes := planes }
    if sps.saoEnabled then
      let planes := saoFrame8 pic.planes sps pps pic.sao pic.sliceAddr pic.lfase pic.isPcm
      pic := { pic with planes := planes }
    let (dpbNext, outNext, pocTid0Next) := bumpDpb dpb st0.output sps pic sh0 st0.pocTid0
    some { st0 with dpb := dpbNext, output := outNext, pocTid0 := pocTid0Next, prevIndepSh? := prevSh? }

def decodeHevcStreamState (data : ByteArray) : Option (HevcDecoderState × String) := do
  let (nals, container) ← extractHevcNals data
  if nals.isEmpty then none
  let mut st : HevcDecoderState := {}
  let mut picSlices : Array (Nat × Nat × ByteArray) := #[]
  let mut sawVcl := false
  for nal in nals do
    let (nalType, _, tid) ← parseNalHeader nal
    let payload := nal.extract 2 nal.size
    if nalType == nalVps then
      let rm ← stripRbspWithMap payload
      let v ← parseVps rm.rbsp
      if v.vpsId >= st.vpsMap.size then none
      st := { st with vpsMap := st.vpsMap.set! v.vpsId (some v) }
    else if nalType == nalSps then
      let rm ← stripRbspWithMap payload
      let s ← parseSps rm.rbsp
      if s.spsId >= st.spsMap.size then none
      st := { st with spsMap := st.spsMap.set! s.spsId (some s) }
    else if nalType == nalPps then
      let rm ← stripRbspWithMap payload
      let p ← parsePps rm.rbsp st.spsMap
      if p.ppsId >= st.ppsMap.size then none
      st := { st with ppsMap := st.ppsMap.set! p.ppsId (some p) }
    else if nalType <= 21 then
      sawVcl := true
      if picSlices.isEmpty then
        picSlices := #[(nalType, tid, payload)]
      else
        let shProbe ← parseSliceHeader payload nalType tid st.spsMap st.ppsMap st.prevIndepSh? st.pocTid0
        if shProbe.firstSliceInPicFlag then
          st ← decodePictureSlices st picSlices
          picSlices := #[(nalType, tid, payload)]
        else
          picSlices := picSlices.push (nalType, tid, payload)
  if !sawVcl then none
  if !picSlices.isEmpty then
    st ← decodePictureSlices st picSlices
  some (flushDpb st, container)

def cropFrameYuv420p (f : HevcDecodedFrame) (sps : HevcSps) : ByteArray := Id.run do
  let cl := sps.confLeft
  let cr := sps.confRight
  let ct := sps.confTop
  let cb := sps.confBottom
  let w := sps.width
  let h := sps.height
  let cw := w >>> 1
  let yPlane := f.planes.getD 0 ByteArray.empty
  let mut out := ByteArray.empty
  for row in [ct:(h - cb)] do
    out := out ++ yPlane.extract (row * w + cl) (row * w + (w - cr))
  for cIdx in [1, 2] do
    let p := f.planes.getD cIdx ByteArray.empty
    for row in [(ct >>> 1):((h - cb) >>> 1)] do
      out := out ++ p.extract (row * cw + (cl >>> 1)) (row * cw + ((w - cr) >>> 1))
  return out

def decodeHevcToYuv420p (data : ByteArray) : Option (Nat × Nat × Nat × ByteArray) := do
  let (st, _) ← decodeHevcStreamState data
  if st.output.isEmpty then none
  let f0 := st.output[0]!
  let sps0 ← st.spsMap.getD f0.spsId none
  let mut out := ByteArray.empty
  for f in st.output do
    let sps ← st.spsMap.getD f.spsId none
    out := out ++ cropFrameYuv420p f sps
  some (sps0.croppedWidth, sps0.croppedHeight, st.output.size, out)

def probeHevcStreamJson (data : ByteArray) : Option String := do
  let (nals, container) ← extractHevcNals data
  if nals.isEmpty then none
  let mut vpsMap : Array (Option HevcVps) := Array.replicate 16 none
  let mut spsMap : Array (Option HevcSps) := Array.replicate 16 none
  let mut ppsMap : Array (Option HevcPps) := Array.replicate 64 none
  let mut firstSps? : Option HevcSps := none
  let mut firstPps? : Option HevcPps := none
  let mut prevSh? : Option HevcSliceHeader := none
  let mut pocTid0 : Int := 0
  let mut frameCount := 0
  let mut sliceJsons : Array String := #[]
  for nal in nals do
    let (nalType, _, tid) ← parseNalHeader nal
    let payload := nal.extract 2 nal.size
    if nalType == nalVps then
      let rm ← stripRbspWithMap payload
      let v ← parseVps rm.rbsp
      if v.vpsId >= vpsMap.size then none
      vpsMap := vpsMap.set! v.vpsId (some v)
    else if nalType == nalSps then
      let rm ← stripRbspWithMap payload
      let s ← parseSps rm.rbsp
      if s.spsId >= spsMap.size then none
      spsMap := spsMap.set! s.spsId (some s)
      if firstSps?.isNone then firstSps? := some s
    else if nalType == nalPps then
      let rm ← stripRbspWithMap payload
      let p ← parsePps rm.rbsp spsMap
      if p.ppsId >= ppsMap.size then none
      ppsMap := ppsMap.set! p.ppsId (some p)
      if firstPps?.isNone then firstPps? := some p
    else if nalType <= 21 then
      let sh ← parseSliceHeader payload nalType tid spsMap ppsMap prevSh? pocTid0
      if !sh.dependentSliceSegmentFlag then prevSh? := some sh
      if sh.firstSliceInPicFlag then
        frameCount := frameCount + 1
        if sh.tid == 0 && sh.nalType != 0 && sh.nalType != 2 && sh.nalType != 4 &&
            sh.nalType != 6 && sh.nalType != 7 && sh.nalType != 8 && sh.nalType != 9 then
          pocTid0 := sh.poc
        let stName := if sh.sliceType == sliceI then "I" else if sh.sliceType == sliceP then "P" else "B"
        sliceJsons := sliceJsons.push
          s!"\{\"nal_type\":{sh.nalType},\"slice_type\":\"{stName}\",\"poc\":{sh.poc},\"qp\":{sh.sliceQp}}"
  let sps ← firstSps?
  let pps ← firstPps?
  if frameCount == 0 then none
  let slicesStr := String.intercalate "," sliceJsons.toList
  let p0 := s!"\{\"ok\":true,\"codec\":\"hevc\",\"container\":\"{container}\","
  let p1 := s!"\"profile_idc\":{sps.ptl.profileIdc},\"level_idc\":{sps.ptl.levelIdc},"
  let p2 := s!"\"width\":{sps.croppedWidth},\"height\":{sps.croppedHeight},"
  let p3 := s!"\"coded_width\":{sps.width},\"coded_height\":{sps.height},"
  let p4 := s!"\"bit_depth_luma\":{sps.bitDepth},\"bit_depth_chroma\":{sps.bitDepthChroma},"
  let p5 := s!"\"chroma_format_idc\":{sps.chromaFormatIdc},\"ctb_size\":{1 <<< sps.log2CtbSize},"
  let p6 := s!"\"tiles\":{pps.tilesEnabledFlag},\"wpp\":{pps.entropyCodingSyncEnabledFlag},"
  let p7 := s!"\"sao\":{sps.saoEnabled},\"weighted_pred\":{pps.weightedPredFlag || pps.weightedBipredFlag},"
  let p8 := s!"\"frames\":{frameCount},\"slices\":[{slicesStr}]}"
  some (p0 ++ p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6 ++ p7 ++ p8)

def intraPlanar : Nat := 0
def intraHoriz : Nat := 10
def intraVert : Nat := 26

structure HevcEncoderCfg where
  width    : Nat
  height   : Nat
  qp       : Int := 28
  qpC      : Int := 28
  log2Ctb  : Nat := 6
  tilesCol : Nat := 1
  tilesRow : Nat := 1
  conf     : Nat × Nat × Nat × Nat := (0, 0, 0, 0)
  ew       : Nat
  eh       : Nat
  cw       : Nat
  ch       : Nat
  ctb      : Nat
  ctbW     : Nat
  ctbH     : Nat
  sps      : HevcSps
  pps      : HevcPps
  deriving Inhabited

def padPlane8 (src : ByteArray) (sw sh dw dh : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (dw * dh)
  for y in [:dh] do
    let sy := if sh == 0 then 0 else Nat.min y (sh - 1)
    let rOff := sy * sw
    for x in [:sw] do
      out := out.push (baGetD src (rOff + x) 128)
    let lastPix := if sw == 0 then (128 : UInt8) else baGetD src (rOff + sw - 1) 128
    for _ in [sw:dw] do
      out := out.push lastPix
  return out

def extractPaddedPlanes (cfg : HevcEncoderCfg) (yuv : ByteArray) (frameIdx : Nat) : Array ByteArray :=
  let sw := cfg.width
  let sh := cfg.height
  let lumaBytes := sw * sh
  let chromaBytes := (sw >>> 1) * (sh >>> 1)
  let frameSize := lumaBytes + 2 * chromaBytes
  let base := frameIdx * frameSize
  let ySrc := yuv.extract base (base + lumaBytes)
  let uSrc := yuv.extract (base + lumaBytes) (base + lumaBytes + chromaBytes)
  let vSrc := yuv.extract (base + lumaBytes + chromaBytes) (base + lumaBytes + 2 * chromaBytes)
  #[padPlane8 ySrc sw sh cfg.ew cfg.eh,
    padPlane8 uSrc (sw >>> 1) (sh >>> 1) cfg.cw cfg.ch,
    padPlane8 vSrc (sw >>> 1) (sh >>> 1) cfg.cw cfg.ch]

def encBlockVar (cfg : HevcEncoderCfg) (srcY : ByteArray) (x0 y0 cb : Nat) : Nat := Id.run do
  let mut acc : Int := 0
  let mut n : Nat := 0
  let mut y := y0
  while y < y0 + cb do
    let row := y * cfg.ew
    let mut x := x0
    while x < x0 + cb do
      acc := acc + Int.ofNat (baGetD srcY (row + x) 0).toNat
      n := n + 1
      x := x + 2
    y := y + 2
  let denom := Int.ofNat (Nat.max n 1)
  let mean := acc / denom
  let mut vAcc : Nat := 0
  let mut y2 := y0
  while y2 < y0 + cb do
    let row := y2 * cfg.ew
    let mut x2 := x0
    while x2 < x0 + cb do
      let d := Int.ofNat (baGetD srcY (row + x2) 0).toNat - mean
      vAcc := vAcc + (d * d).toNat
      x2 := x2 + 2
    y2 := y2 + 2
  return vAcc / Nat.max n 1

def encSadMv (cfg : HevcEncoderCfg) (srcY refY : ByteArray) (x0 y0 cb : Nat) (mv : Int × Int) : Nat := Id.run do
  let dx := asrInt mv.1 2
  let dy := asrInt mv.2 2
  let maxX := Int.ofNat cfg.ew - 1
  let maxY := Int.ofNat cfg.eh - 1
  let mut acc : Nat := 0
  let mut y := 0
  while y < cb do
    let sy := (clipInt (Int.ofNat (y0 + y) + dy) 0 maxY).toNat
    let srow := (y0 + y) * cfg.ew + x0
    let rrow := sy * cfg.ew
    let mut x := 0
    while x < cb do
      let sx := (clipInt (Int.ofNat (x0 + x) + dx) 0 maxX).toNat
      let sv := Int.ofNat (baGetD srcY (srow + x) 0).toNat
      let rv := Int.ofNat (baGetD refY (rrow + sx) 0).toNat
      acc := acc + (sv - rv).natAbs
      x := x + 2
    y := y + 2
  return acc * 4

def encSadQpel (cfg : HevcEncoderCfg) (srcY refY : ByteArray) (x0 y0 cb : Nat) (mv : Int × Int) : Nat := Id.run do
  let pred14 := mcLuma14Bit refY cfg.ew cfg.eh
    (Int.ofNat x0 + asrInt mv.1 2) (Int.ofNat y0 + asrInt mv.2 2)
    (mv.1 % 4).toNat (mv.2 % 4).toNat cb cb
  let mut acc : Nat := 0
  for y in [:cb] do
    let row := (y0 + y) * cfg.ew + x0
    let prow := y * cb
    for x in [:cb] do
      let p := (clipInt (asrInt (pred14.getD (prow + x) 0 + 32) 6) 0 255).toNat
      let s := (baGetD srcY (row + x) 0).toNat
      acc := acc + (Int.ofNat s - Int.ofNat p).natAbs
  return acc

def encShouldSplit (cfg : HevcEncoderCfg) (srcY : ByteArray) (refY? : Option ByteArray)
    (x0 y0 cb : Nat) (forceIntra : Bool) : Bool :=
  if cb > 32 then true
  else if cb <= 8 then false
  else if forceIntra then
    encBlockVar cfg srcY x0 y0 cb > (if cb == 32 then 500 else 900)
  else
    match refY? with
    | none => encBlockVar cfg srcY x0 y0 cb > (if cb == 32 then 500 else 900)
    | some refY =>
      let sad0 := encSadMv cfg srcY refY x0 y0 cb (0, 0)
      if sad0 <= cb * cb * 2 then false
      else sad0 > cb * cb * (if cb == 32 then 10 else 18)

def encMotionSearch (cfg : HevcEncoderCfg) (srcY refY : ByteArray) (x0 y0 cb : Nat)
    (seedMv : Int × Int) : (Int × Int) × Nat := Id.run do
  let mut best : Int × Int := (asrInt seedMv.1 2 * 4, asrInt seedMv.2 2 * 4)
  let mut bestSad := encSadMv cfg srcY refY x0 y0 cb best
  let zSad := encSadMv cfg srcY refY x0 y0 cb (0, 0)
  if zSad < bestSad then
    best := (0, 0)
    bestSad := zSad
  for step in #[ (8 : Int), 4, 2, 1 ] do
    let (cx, cy) := best
    for dy in #[-step, 0, step] do
      for dx in #[-step, 0, step] do
        if !(dx == 0 && dy == 0) then
          let cand := (clipInt (cx + dx * 4) (-256) 256, clipInt (cy + dy * 4) (-256) 256)
          let s := encSadMv cfg srcY refY x0 y0 cb cand
          if s < bestSad then
            bestSad := s
            best := cand
  for stepQ in #[ (2 : Int), 1 ] do
    let (cx, cy) := best
    for dy in #[-stepQ, 0, stepQ] do
      for dx in #[-stepQ, 0, stepQ] do
        if !(dx == 0 && dy == 0) then
          let cand := (clipInt (cx + dx) (-256) 256, clipInt (cy + dy) (-256) 256)
          let s := encSadQpel cfg srcY refY x0 y0 cb cand
          if s < bestSad then
            bestSad := s
            best := cand
  return (best, bestSad)

def encMpmList (ctx : HevcCtbCtx) (pic : HevcDecodedFrame) (sps : HevcSps) (x0 y0 : Nat) : Array Nat :=
  let ctbMask := (1 <<< sps.log2CtbSize) - 1
  let leftOpt := if ctx.ctbLeft || (x0 &&& ctbMask) != 0 then ipmAt pic sps (Int.ofNat x0 - 1) (Int.ofNat y0) else none
  let upOpt := if ctx.ctbUp || (y0 &&& ctbMask) != 0 then ipmAt pic sps (Int.ofNat x0) (Int.ofNat y0 - 1) else none
  let c0 := leftOpt.getD intraDc
  let c1 := if (y0 &&& ctbMask) == 0 then intraDc else upOpt.getD intraDc
  if c0 == c1 then
    if c0 < 2 then #[0, intraDc, 26]
    else #[c0, 2 + ((c0 + 29) &&& 31), 2 + ((c0 - 1) &&& 31)]
  else
    let c2 := if c0 != 0 && c1 != 0 then 0 else if c0 != intraDc && c1 != intraDc then intraDc else 26
    #[c0, c1, c2]

def encPickIntraMode (cfg : HevcEncoderCfg) (ctx : HevcCtbCtx) (pic : HevcDecodedFrame)
    (srcY : ByteArray) (x0 y0 log2Cb : Nat) : Nat := Id.run do
  let cb := 1 <<< log2Cb
  let na := computeNeighAvail ctx cfg.sps x0 y0 cb cb
  let mut bestMode := intraDc
  let mut bestSad : Nat := 1 <<< 30
  let basePlane := pic.planes.getD 0 ByteArray.empty
  for m in #[intraPlanar, intraDc, intraHoriz, intraVert] do
    let predPlane := intraPred8 basePlane cfg.ew cfg.sps cfg.pps pic.tabMvf na x0 y0 log2Cb 0 m
    let mut sad : Nat := 0
    for yy in [:cb] do
      let row := (y0 + yy) * cfg.ew + x0
      for xx in [:cb] do
        let s := (baGetD srcY (row + xx) 0).toNat
        let p := (baGetD predPlane (row + xx) 0).toNat
        sad := sad + (Int.ofNat s - Int.ofNat p).natAbs
    if sad < bestSad then
      bestSad := sad
      bestMode := m
  return bestMode

def encScanForIntra (log2Size mode : Nat) : Nat :=
  if log2Size < 4 then
    if 6 <= mode && mode <= 14 then scanVert
    else if 22 <= mode && mode <= 30 then scanHoriz
    else scanDiag
  else scanDiag

def encColLimitAndDcOnly (levels : Array Int) (side : Nat) : Nat := Id.run do
  let mut maxXy := 0
  let mut dcOnly := true
  for i in [:levels.size] do
    if levels.getD i 0 != 0 then
      if i != 0 then dcOnly := false
      let rx := i % side
      let ry := i / side
      let m := Nat.max rx ry
      if m > maxXy then maxXy := m
  return if dcOnly then 0 else maxXy

def encExtractRes (src pred : ByteArray) (stride x0 y0 side : Nat) : Array Int := Id.run do
  let mut res : Array Int := Array.mkEmpty (side * side)
  for yy in [:side] do
    let row := (y0 + yy) * stride + x0
    for xx in [:side] do
      let s := Int.ofNat (baGetD src (row + xx) 0).toNat
      let p := Int.ofNat (baGetD pred (row + xx) 0).toNat
      res := res.push (s - p)
  return res

def encodeIntraTu (cfg : HevcEncoderCfg) (ctx : HevcCtbCtx) (pic0 : HevcDecodedFrame)
    (srcPlanes : Array ByteArray) (w0 : HevcCabacWriter) (st0 : Array Nat)
    (x0 y0 log2Size mode : Nat) : HevcDecodedFrame × HevcCabacWriter × Array Nat := Id.run do
  let sps := cfg.sps
  let pps := cfg.pps
  let side := 1 <<< log2Size
  let mut w := w0
  let mut st := st0
  let mut pic := pic0
  if log2Size > 2 then
    let splitCtx := hevcCabacElemOffset.getD elemSplitTransformFlag 0 + 5 - log2Size
    let (w', st') := w.encodeDecision st splitCtx 0
    w := w'
    st := st'
  let na := computeNeighAvail ctx sps x0 y0 side side
  let predY := intraPred8 (pic.planes.getD 0 ByteArray.empty) cfg.ew sps pps pic.tabMvf na x0 y0 log2Size 0 mode
  pic := { pic with planes := pic.planes.set! 0 predY }
  let resY := encExtractRes (srcPlanes.getD 0 ByteArray.empty) predY cfg.ew x0 y0 side
  let isDst := log2Size == 2
  let lvY := quantizeCoeffs (forwardTransform resY log2Size isDst) log2Size cfg.qp true
  let cbfY := if lvY.any (· != 0) then 1 else 0
  let mut lvCb : Array Int := #[]
  let mut lvCr : Array Int := #[]
  let mut cbfCb := 0
  let mut cbfCr := 0
  if log2Size > 2 then
    let cs := side >>> 1
    let predU := intraPred8 (pic.planes.getD 1 ByteArray.empty) cfg.cw sps pps pic.tabMvf na x0 y0 (log2Size - 1) 1 mode
    let predV := intraPred8 (pic.planes.getD 2 ByteArray.empty) cfg.cw sps pps pic.tabMvf na x0 y0 (log2Size - 1) 2 mode
    pic := { pic with planes := (pic.planes.set! 1 predU).set! 2 predV }
    let resU := encExtractRes (srcPlanes.getD 1 ByteArray.empty) predU cfg.cw (x0 >>> 1) (y0 >>> 1) cs
    let resV := encExtractRes (srcPlanes.getD 2 ByteArray.empty) predV cfg.cw (x0 >>> 1) (y0 >>> 1) cs
    lvCb := quantizeCoeffs (forwardTransform resU (log2Size - 1) false) (log2Size - 1) cfg.qpC true
    lvCr := quantizeCoeffs (forwardTransform resV (log2Size - 1) false) (log2Size - 1) cfg.qpC true
    cbfCb := if lvCb.any (· != 0) then 1 else 0
    cbfCr := if lvCr.any (· != 0) then 1 else 0
    let cbfCtx := hevcCabacElemOffset.getD elemCbfCbCr 0
    let (w1, st1) := w.encodeDecision st cbfCtx cbfCb
    let (w2, st2) := w1.encodeDecision st1 cbfCtx cbfCr
    w := w2
    st := st2
  let (wL, stL) := w.encodeDecision st (hevcCabacElemOffset.getD elemCbfLuma 0 + 1) cbfY
  w := wL
  st := stL
  let scan := encScanForIntra log2Size mode
  if cbfY != 0 then
    let (w', st') := encResidual w st lvY log2Size scan 0
    w := w'
    st := st'
    let dq := dequantLevels lvY log2Size cfg.qp
    let maxXY := encColLimitAndDcOnly lvY side
    let recY := inverseTransformAndAdd (pic.planes.getD 0 ByteArray.empty) cfg.ew x0 y0 dq log2Size 0 true 0 0 maxXY
    pic := { pic with planes := pic.planes.set! 0 recY }
  if log2Size > 2 then
    let cs := side >>> 1
    if cbfCb != 0 then
      let (w', st') := encResidual w st lvCb (log2Size - 1) scan 1
      w := w'
      st := st'
      let dqU := dequantLevels lvCb (log2Size - 1) cfg.qpC
      let maxU := encColLimitAndDcOnly lvCb cs
      let recU := inverseTransformAndAdd (pic.planes.getD 1 ByteArray.empty) cfg.cw (x0 >>> 1) (y0 >>> 1) dqU (log2Size - 1) 1 true 0 0 maxU
      pic := { pic with planes := pic.planes.set! 1 recU }
    if cbfCr != 0 then
      let (w', st') := encResidual w st lvCr (log2Size - 1) scan 2
      w := w'
      st := st'
      let dqV := dequantLevels lvCr (log2Size - 1) cfg.qpC
      let maxV := encColLimitAndDcOnly lvCr cs
      let recV := inverseTransformAndAdd (pic.planes.getD 2 ByteArray.empty) cfg.cw (x0 >>> 1) (y0 >>> 1) dqV (log2Size - 1) 2 true 0 0 maxV
      pic := { pic with planes := pic.planes.set! 2 recV }
  return (pic, w, st)

def encodeInterTu (cfg : HevcEncoderCfg) (pic0 : HevcDecodedFrame) (srcPlanes : Array ByteArray)
    (w0 : HevcCabacWriter) (st0 : Array Nat) (x0 y0 log2Size : Nat) (isMerge2Nx2N : Bool) :
    HevcDecodedFrame × HevcCabacWriter × Array Nat := Id.run do
  let side := 1 <<< log2Size
  let cs := side >>> 1
  let mut w := w0
  let mut st := st0
  let mut pic := pic0
  let resY := encExtractRes (srcPlanes.getD 0 ByteArray.empty) (pic.planes.getD 0 ByteArray.empty) cfg.ew x0 y0 side
  let mut lvY := quantizeCoeffs (forwardTransform resY log2Size false) log2Size cfg.qp false
  let mut cbfY := if lvY.any (· != 0) then 1 else 0
  let resU := encExtractRes (srcPlanes.getD 1 ByteArray.empty) (pic.planes.getD 1 ByteArray.empty) cfg.cw (x0 >>> 1) (y0 >>> 1) cs
  let resV := encExtractRes (srcPlanes.getD 2 ByteArray.empty) (pic.planes.getD 2 ByteArray.empty) cfg.cw (x0 >>> 1) (y0 >>> 1) cs
  let lvCb := quantizeCoeffs (forwardTransform resU (log2Size - 1) false) (log2Size - 1) cfg.qpC false
  let lvCr := quantizeCoeffs (forwardTransform resV (log2Size - 1) false) (log2Size - 1) cfg.qpC false
  let cbfCb := if lvCb.any (· != 0) then 1 else 0
  let cbfCr := if lvCr.any (· != 0) then 1 else 0
  let hasAny := cbfY != 0 || cbfCb != 0 || cbfCr != 0
  if !isMerge2Nx2N then
    let rqtCtx := hevcCabacElemOffset.getD elemNoResidualDataFlag 0
    let (w', st') := w.encodeDecision st rqtCtx (if hasAny then 1 else 0)
    w := w'
    st := st'
    if !hasAny then return (pic, w, st)
  else if !hasAny then
    let dcSign : Int := if resY.getD 0 0 >= 0 then 1 else -1
    lvY := lvY.set! 0 dcSign
    cbfY := 1
  let splitCtx := hevcCabacElemOffset.getD elemSplitTransformFlag 0 + 5 - log2Size
  let cbfCtx := hevcCabacElemOffset.getD elemCbfCbCr 0
  let (w1, st1) := w.encodeDecision st splitCtx 0
  let (w2, st2) := w1.encodeDecision st1 cbfCtx cbfCb
  let (w3, st3) := w2.encodeDecision st2 cbfCtx cbfCr
  w := w3
  st := st3
  if cbfCb != 0 || cbfCr != 0 then
    let (wL, stL) := w.encodeDecision st (hevcCabacElemOffset.getD elemCbfLuma 0 + 1) cbfY
    w := wL
    st := stL
  if cbfY != 0 then
    let (w', st') := encResidual w st lvY log2Size scanDiag 0
    w := w'
    st := st'
    let dq := dequantLevels lvY log2Size cfg.qp
    let maxXY := encColLimitAndDcOnly lvY side
    let recY := inverseTransformAndAdd (pic.planes.getD 0 ByteArray.empty) cfg.ew x0 y0 dq log2Size 0 false 0 0 maxXY
    pic := { pic with planes := pic.planes.set! 0 recY }
  if cbfCb != 0 then
    let (w', st') := encResidual w st lvCb (log2Size - 1) scanDiag 1
    w := w'
    st := st'
    let dqU := dequantLevels lvCb (log2Size - 1) cfg.qpC
    let maxU := encColLimitAndDcOnly lvCb cs
    let recU := inverseTransformAndAdd (pic.planes.getD 1 ByteArray.empty) cfg.cw (x0 >>> 1) (y0 >>> 1) dqU (log2Size - 1) 1 false 0 0 maxU
    pic := { pic with planes := pic.planes.set! 1 recU }
  if cbfCr != 0 then
    let (w', st') := encResidual w st lvCr (log2Size - 1) scanDiag 2
    w := w'
    st := st'
    let dqV := dequantLevels lvCr (log2Size - 1) cfg.qpC
    let maxV := encColLimitAndDcOnly lvCr cs
    let recV := inverseTransformAndAdd (pic.planes.getD 2 ByteArray.empty) cfg.cw (x0 >>> 1) (y0 >>> 1) dqV (log2Size - 1) 2 false 0 0 maxV
    pic := { pic with planes := pic.planes.set! 2 recV }
  return (pic, w, st)

def encodeCu (cfg : HevcEncoderCfg) (ctx0 : HevcCtbCtx) (pic0 : HevcDecodedFrame)
    (sh : HevcSliceHeader) (srcPlanes : Array ByteArray) (refPic? : Option HevcRefPlanes)
    (w0 : HevcCabacWriter) (st0 : Array Nat) (x0 y0 log2Cb depth : Nat) (forceIntra : Bool) :
    HevcCtbCtx × HevcDecodedFrame × HevcCabacWriter × Array Nat := Id.run do
  let sps := cfg.sps
  let pps := cfg.pps
  let cb := 1 <<< log2Cb
  let ctbMask := (1 <<< sps.log2CtbSize) - 1
  let ctx := { ctx0 with cuX := x0, cuY := y0 }
  let mut pic := setCtDepthBlock pic0 sps x0 y0 log2Cb depth
  let mut w := w0
  let mut st := st0
  let srcY := srcPlanes.getD 0 ByteArray.empty
  if !forceIntra then
    if let some refPic := refPic? then
      let refY := refPic.planes.getD 0 ByteArray.empty
      let sl := if ctx.ctbLeft || (x0 &&& ctbMask) != 0 then skipAt pic sps (Int.ofNat x0 - 1) (Int.ofNat y0) else 0
      let su := if ctx.ctbUp || (y0 &&& ctbMask) != 0 then skipAt pic sps (Int.ofNat x0) (Int.ofNat y0 - 1) else 0
      let skipInc := (if sl != 0 then 1 else 0) + (if su != 0 then 1 else 0)
      let skipCtx := hevcCabacElemOffset.getD elemSkipFlag 0 + skipInc
      let mergeCands := mergeCandidates ctx pic sps pps sh x0 y0 cb cb log2Cb part2Nx2N 0
      let mut bestMIdx := 0
      let mut bestMSad : Nat := 1 <<< 30
      for idx in [:mergeCands.size] do
        let mc := mergeCands[idx]!
        let s := encSadQpel cfg srcY refY x0 y0 cb mc.mv0
        if s < bestMSad then
          bestMSad := s
          bestMIdx := idx
      if bestMSad <= cb * cb then
        let bestMvf := mergeCands.getD bestMIdx mvfZero
        let tmpPlanes := mcPu8 pic.planes sps pps sh bestMvf pic.rpl x0 y0 cb cb
        let mut maxErrC : Nat := 0
        for cIdx in [1, 2] do
          let sPlane := srcPlanes.getD cIdx ByteArray.empty
          let pPlane := tmpPlanes.getD cIdx ByteArray.empty
          for yy in [:cb >>> 1] do
            let rOff := ((y0 >>> 1) + yy) * cfg.cw + (x0 >>> 1)
            for xx in [:cb >>> 1] do
              let e := (Int.ofNat (baGetD sPlane (rOff + xx) 0).toNat - Int.ofNat (baGetD pPlane (rOff + xx) 0).toNat).natAbs
              if e > maxErrC then maxErrC := e
        if maxErrC <= 2 && bestMSad <= (cb * cb * 3) / 4 then
          let (w1, st1) := w.encodeDecision st skipCtx 1
          let (w2, st2) := encMergeIdx w1 st1 bestMIdx sh.maxNumMergeCand
          pic := fillSkipBlock pic sps x0 y0 log2Cb 1
          pic := storeMvfBlock pic sps x0 y0 cb cb bestMvf
          pic := { pic with planes := tmpPlanes }
          pic := fillIpmBlock pic sps x0 y0 cb cb intraDc false
          return (ctx, pic, w2, st2)
      let mvp0 := mvpList ctx pic sps pps sh x0 y0 cb cb 0 0 0
      let mvp1 := mvpList ctx pic sps pps sh x0 y0 cb cb 0 0 1
      let (bestMv, bestInterSad) := encMotionSearch cfg srcY refY x0 y0 cb mvp0
      let d0 := (bestMv.1 - mvp0.1).natAbs + (bestMv.2 - mvp0.2).natAbs
      let d1 := (bestMv.1 - mvp1.1).natAbs + (bestMv.2 - mvp1.2).natAbs
      let mvpFlag := if d1 < d0 then 1 else 0
      let mvp := if mvpFlag != 0 then mvp1 else mvp0
      let intraCost := encBlockVar cfg srcY x0 y0 cb * 8 + 120
      if bestInterSad <= intraCost then
        let (w1, st1) := w.encodeDecision st skipCtx 0
        let (w2, st2) := w1.encodeDecision st1 (hevcCabacElemOffset.getD elemPredModeFlag 0) 0
        let (w3, st3) := w2.encodeDecision st2 (hevcCabacElemOffset.getD elemPartMode 0) 1
        w := w3
        st := st3
        pic := fillSkipBlock pic sps x0 y0 log2Cb 0
        pic := fillIpmBlock pic sps x0 y0 cb cb intraDc false
        let useMerge := bestMSad <= bestInterSad + cb
        let mut chosenMvf := mvfZero
        if useMerge then
          let (w4, st4) := w.encodeDecision st (hevcCabacElemOffset.getD elemMergeFlag 0) 1
          let (w5, st5) := encMergeIdx w4 st4 bestMIdx sh.maxNumMergeCand
          w := w5
          st := st5
          chosenMvf := mergeCands.getD bestMIdx mvfZero
        else
          let (w4, st4) := w.encodeDecision st (hevcCabacElemOffset.getD elemMergeFlag 0) 0
          let (w5, st5) := encMvd w4 st4 (bestMv.1 - mvp.1) (bestMv.2 - mvp.2)
          let (w6, st6) := w5.encodeDecision st5 (hevcCabacElemOffset.getD elemMvpLxFlag 0) mvpFlag
          w := w6
          st := st6
          chosenMvf := { predFlag := pfL0, refIdx0 := 0, refIdx1 := -1, mv0 := bestMv, mv1 := (0, 0) }
        pic := storeMvfBlock pic sps x0 y0 cb cb chosenMvf
        pic := { pic with planes := mcPu8 pic.planes sps pps sh chosenMvf pic.rpl x0 y0 cb cb }
        let (pic', w', st') := encodeInterTu cfg pic srcPlanes w st x0 y0 log2Cb useMerge
        return (ctx, pic', w', st')
      let (w1, st1) := w.encodeDecision st skipCtx 0
      let (w2, st2) := w1.encodeDecision st1 (hevcCabacElemOffset.getD elemPredModeFlag 0) 1
      w := w2
      st := st2
      pic := fillSkipBlock pic sps x0 y0 log2Cb 0
  if log2Cb == sps.log2MinCbSize then
    let (w', st') := w.encodeDecision st (hevcCabacElemOffset.getD elemPartMode 0) 1
    w := w'
    st := st'
  pic := storeMvfBlock pic sps x0 y0 cb cb mvfIntra
  let mode := encPickIntraMode cfg ctx pic srcY x0 y0 log2Cb
  let mpm := encMpmList ctx pic sps x0 y0
  let mIdx? := mpm.findIdx? (· == mode)
  match mIdx? with
  | some mIdx =>
    let (w1, st1) := w.encodeDecision st (hevcCabacElemOffset.getD elemPrevIntraLumaPredFlag 0) 1
    w := w1
    st := st1
    for _ in [:mIdx] do
      w := w.encodeBypass 1
    if mIdx < 2 then
      w := w.encodeBypass 0
  | none =>
    let (w1, st1) := w.encodeDecision st (hevcCabacElemOffset.getD elemPrevIntraLumaPredFlag 0) 0
    w := w1
    st := st1
    let mut rem := mode
    for m in mpm do
      if m < mode then rem := rem - 1
    w := w.encodeBypassBits rem 5
  pic := fillIpmBlock pic sps x0 y0 cb cb mode true
  let (wC, stC) := w.encodeDecision st (hevcCabacElemOffset.getD elemIntraChromaPredMode 0) 0
  let (pic', w', st') := encodeIntraTu cfg ctx pic srcPlanes wC stC x0 y0 log2Cb mode
  return (ctx, pic', w', st')

def encodeCodingTree (cfg : HevcEncoderCfg) (ctx0 : HevcCtbCtx) (pic0 : HevcDecodedFrame)
    (sh : HevcSliceHeader) (srcPlanes : Array ByteArray) (refPic? : Option HevcRefPlanes)
    (w0 : HevcCabacWriter) (st0 : Array Nat) (x0 y0 log2Cb depth : Nat)
    (forceIntra : Bool) : Nat → HevcCtbCtx × HevcDecodedFrame × HevcCabacWriter × Array Nat
  | 0 => (ctx0, pic0, w0, st0)
  | fuel + 1 => Id.run do
    let sps := cfg.sps
    let cb := 1 <<< log2Cb
    let ctbMask := (1 <<< sps.log2CtbSize) - 1
    let srcY := srcPlanes.getD 0 ByteArray.empty
    let refY? := refPic?.map (fun rp => rp.planes.getD 0 ByteArray.empty)
    let mut w := w0
    let mut st := st0
    let mut split := 0
    if x0 + cb <= sps.width && y0 + cb <= sps.height && log2Cb > sps.log2MinCbSize then
      let dl := if ctx0.ctbLeft || (x0 &&& ctbMask) != 0 then ctDepthAt pic0 sps (Int.ofNat x0 - 1) (Int.ofNat y0) else 0
      let dt := if ctx0.ctbUp || (y0 &&& ctbMask) != 0 then ctDepthAt pic0 sps (Int.ofNat x0) (Int.ofNat y0 - 1) else 0
      let inc := (if dl > depth then 1 else 0) + (if dt > depth then 1 else 0)
      split := if encShouldSplit cfg srcY refY? x0 y0 cb forceIntra then 1 else 0
      let (w', st') := w.encodeDecision st (hevcCabacElemOffset.getD elemSplitCuFlag 0 + inc) split
      w := w'
      st := st'
    else
      split := if log2Cb > sps.log2MinCbSize then 1 else 0
    if split != 0 then
      let half := log2Cb - 1
      let off := 1 <<< half
      let mut ctx := ctx0
      let mut pic := pic0
      for (ox, oy) in #[(0, 0), (off, 0), (0, off), (off, off)] do
        if x0 + ox < sps.width && y0 + oy < sps.height then
          let (ctx', pic', w', st') := encodeCodingTree cfg ctx pic sh srcPlanes refPic? w st
            (x0 + ox) (y0 + oy) half (depth + 1) forceIntra fuel
          ctx := ctx'
          pic := pic'
          w := w'
          st := st'
      return (ctx, pic, w, st)
    return encodeCu cfg ctx0 pic0 sh srcPlanes refPic? w st x0 y0 log2Cb depth forceIntra

def newEncPicAndHeader (cfg : HevcEncoderCfg) (poc : Int) (sliceType : Nat)
    (refPic? : Option HevcRefPlanes) : HevcDecodedFrame × HevcSliceHeader :=
  let sps := cfg.sps
  let rpl0 : HevcRpl :=
    match refPic? with
    | some rp => { refs := #[some rp], poc := #[rp.poc], lt := #[false] }
    | none => {}
  let rpl1 : HevcRpl := {}
  let sh : HevcSliceHeader := {
    nalType := if sliceType == sliceI then nalIdrWRadl else nalTrailR
    sliceType := sliceType
    sliceAddrRs := 0
    poc := poc
    sliceTemporalMvpEnabledFlag := sliceType != sliceI
    collocatedList := 0
    collocatedRefIdx := 0
    nbRefs := #[if sliceType == sliceP then 1 else 0, 0]
    maxNumMergeCand := 5
    pwt? := none
    sliceQp := cfg.qp
    cbQpOffset := 0
    crQpOffset := 0
    betaOffset := 0
    tcOffset := 0
    disableDeblockingFilterFlag := false
    sliceLoopFilterAcrossSlicesEnabledFlag := true
    saoLumaFlag := true
    saoChromaFlag := false
  }
  let basePic := newDecodedFrame sps sh
  let rplPair : Array HevcRpl := #[rpl0, rpl1]
  let pic := { basePic with
    rpl := rplPair
    rplTab := Array.replicate sps.ctbSize (some rplPair)
    sliceAddr := Array.replicate sps.ctbSize 0
  }
  (pic, sh)

def encodeHevcFrame (cfg : HevcEncoderCfg) (srcPlanes : Array ByteArray)
    (refPic? : Option HevcRefPlanes) (frameIdx : Nat) : Option ByteArray := do
  let intra := refPic?.isNone
  let sliceType := if intra then sliceI else sliceP
  let nalType := if intra then nalIdrWRadl else nalTrailR
  let (pic0, sh) := newEncPicAndHeader cfg (Int.ofNat frameIdx) sliceType refPic?
  let sps := cfg.sps
  let pps := cfg.pps
  let mut pic := pic0
  let mut groups : Array ByteArray := #[]
  let mut subW? : Option HevcCabacWriter := none
  let mut subSt : Array Nat := #[]
  let mut firstInTile := true
  let mut endOfTilesX := sps.width
  for ts in [:sps.ctbSize] do
    let rs := pps.ctbAddrTsToRs.getD ts 0
    let xCtb := rs % sps.ctbWidth
    let yCtb := rs / sps.ctbWidth
    let newTile := ts == 0 ||
      (pps.tilesEnabledFlag && pps.tileId.getD ts 0 != pps.tileId.getD (ts - 1) 0)
    if newTile then
      if let some prevW := subW? then
        let finW := (prevW.encodeTerminate 0).encodeTerminate 1
        let grpBytes ← finW.toBytes
        groups := groups.push grpBytes
      subW? := some HevcCabacWriter.fresh
      subSt := initCabacStates sliceType 0 cfg.qp
      firstInTile := true
      if pps.tilesEnabledFlag then
        let idxX := pps.colIdxX.getD xCtb 0
        endOfTilesX := (xCtb + pps.columnWidth.getD idxX 1) <<< sps.log2CtbSize
      else
        endOfTilesX := sps.width
    let mut subW := subW?.getD HevcCabacWriter.fresh
    if !firstInTile then
      subW := subW.encodeTerminate 0
    firstInTile := false
    let leftTile := xCtb > 0 && pps.tilesEnabledFlag &&
      pps.tileId.getD ts 0 != pps.tileId.getD (pps.ctbAddrRsToTs.getD (rs - 1) 0) 0
    let upTile := yCtb > 0 && pps.tilesEnabledFlag &&
      pps.tileId.getD ts 0 != pps.tileId.getD (pps.ctbAddrRsToTs.getD (rs - sps.ctbWidth) 0) 0
    let ctbLeft := xCtb > 0 && rs > 0 && !leftTile
    let ctbUp := yCtb > 0 && rs >= sps.ctbWidth && !upTile
    let ctbUpRight := yCtb > 0 && rs + 1 >= sps.ctbWidth && xCtb + 1 < sps.ctbWidth &&
      (!pps.tilesEnabledFlag ||
        pps.tileId.getD ts 0 == pps.tileId.getD (pps.ctbAddrRsToTs.getD (rs + 1 - sps.ctbWidth) 0) 0)
    let ctbUpLeft := xCtb > 0 && yCtb > 0 && rs - 1 >= sps.ctbWidth &&
      (!pps.tilesEnabledFlag ||
        pps.tileId.getD ts 0 == pps.tileId.getD (pps.ctbAddrRsToTs.getD (rs - 1 - sps.ctbWidth) 0) 0)
    let ctbSize := 1 <<< sps.log2CtbSize
    let ctx : HevcCtbCtx := {
      endOfTilesX := endOfTilesX
      endOfTilesY := Nat.min (yCtb * ctbSize + ctbSize) sps.height
      ctbLeft := ctbLeft
      ctbUp := ctbUp
      ctbUpRight := ctbUpRight
      ctbUpLeft := ctbUpLeft
      boundaryLeftSlice := false
      boundaryUpperSlice := false
      boundaryLeftTile := leftTile
      boundaryUpperTile := upTile
    }
    if ctbLeft then
      let (w', st') := subW.encodeDecision subSt (hevcCabacElemOffset.getD elemSaoMergeFlag 0) 0
      subW := w'
      subSt := st'
    if ctbUp then
      let (w', st') := subW.encodeDecision subSt (hevcCabacElemOffset.getD elemSaoMergeFlag 0) 0
      subW := w'
      subSt := st'
    let (wSao, stSao) := subW.encodeDecision subSt (hevcCabacElemOffset.getD elemSaoTypeIdx 0) 0
    let (_, pic', wTree, stTree) := encodeCodingTree cfg ctx pic sh srcPlanes refPic? wSao stSao
      (xCtb <<< sps.log2CtbSize) (yCtb <<< sps.log2CtbSize) sps.log2CtbSize 0 intra 8
    pic := pic'
    subW? := some wTree
    subSt := stTree
  let lastW ← subW?
  let lastBytes ← (lastW.encodeTerminate 1).toBytes
  groups := groups.push lastBytes
  let mut entryLens : Array Nat := #[]
  if groups.size > 1 then
    for i in [:groups.size - 1] do
      entryLens := entryLens.push (insertRbspEpb groups[i]!).size
  let hdr ← sliceHeaderBits nalType sliceType (frameIdx &&& 0xFF) true false entryLens cfg.qp
  let mut body := hdr
  for g in groups do
    body := ByteArray.append body g
  some (packHevcNal nalType 0 1 body)

def muxAnnexB (nals : Array ByteArray) : ByteArray := Id.run do
  let startCode : ByteArray := ByteArray.mk #[0, 0, 0, 1]
  let mut out := ByteArray.empty
  for nal in nals do
    out := ByteArray.append out startCode
    out := ByteArray.append out nal
  return out

def initHevcEncoder (width height : Nat) (qp : Int := 28) (log2Ctb : Nat := 6)
    (tilesCol : Nat := 1) (tilesRow : Nat := 1) :
    Option (HevcEncoderCfg × ByteArray × ByteArray × ByteArray × HevcDecoderState) := do
  if width == 0 || height == 0 || (width &&& 1) != 0 || (height &&& 1) != 0 then none
  if log2Ctb < 4 || log2Ctb > 6 || tilesCol == 0 || tilesRow == 0 then none
  let qpClamped := clipInt qp 0 51
  let qpC := mapQpC qpClamped
  let padW := (8 - (width &&& 7)) &&& 7
  let padH := (8 - (height &&& 7)) &&& 7
  let conf := (0, padW, 0, padH)
  let ew := width + padW
  let eh := height + padH
  let ctb := 1 <<< log2Ctb
  let ctbW := (ew + ctb - 1) >>> log2Ctb
  let ctbH := (eh + ctb - 1) >>> log2Ctb
  if tilesCol > ctbW || tilesRow > ctbH then none
  let vpsNal ← writeVps
  let spsNal ← writeSps ew eh log2Ctb conf
  let ppsNal ← writePps tilesCol tilesRow ctbW ctbH
  let vpsRm ← stripRbspWithMap (vpsNal.extract 2 vpsNal.size)
  let spsRm ← stripRbspWithMap (spsNal.extract 2 spsNal.size)
  let ppsRm ← stripRbspWithMap (ppsNal.extract 2 ppsNal.size)
  let vps ← parseVps vpsRm.rbsp
  let sps ← parseSps spsRm.rbsp
  let mut decSt : HevcDecoderState := {}
  decSt := { decSt with
    vpsMap := decSt.vpsMap.set! vps.vpsId (some vps)
    spsMap := decSt.spsMap.set! sps.spsId (some sps) }
  let pps ← parsePps ppsRm.rbsp decSt.spsMap
  decSt := { decSt with ppsMap := decSt.ppsMap.set! pps.ppsId (some pps) }
  let cfg : HevcEncoderCfg := {
    width := width
    height := height
    qp := qpClamped
    qpC := qpC
    log2Ctb := log2Ctb
    tilesCol := tilesCol
    tilesRow := tilesRow
    conf := conf
    ew := ew
    eh := eh
    cw := ew >>> 1
    ch := eh >>> 1
    ctb := ctb
    ctbW := ctbW
    ctbH := ctbH
    sps := sps
    pps := pps
  }
  some (cfg, vpsNal, spsNal, ppsNal, decSt)

def encodeHevcNals (width height : Nat) (yuv : ByteArray) (qp : Int := 28)
    (log2Ctb : Nat := 6) (tilesCol : Nat := 1) (tilesRow : Nat := 1) :
    Option (ByteArray × ByteArray × ByteArray × Array ByteArray) := do
  let frameBytes := (width * height * 3) / 2
  if frameBytes == 0 || yuv.size == 0 || yuv.size % frameBytes != 0 then none
  let nFrames := yuv.size / frameBytes
  let (cfg, vpsNal, spsNal, ppsNal, decSt0) ← initHevcEncoder width height qp log2Ctb tilesCol tilesRow
  let mut decSt := decSt0
  let mut sliceNals : Array ByteArray := Array.mkEmpty nFrames
  let mut refPic? : Option HevcRefPlanes := none
  for f in [:nFrames] do
    let srcPlanes := extractPaddedPlanes cfg yuv f
    let nal ← encodeHevcFrame cfg srcPlanes refPic? f
    sliceNals := sliceNals.push nal
    let nalType := if f == 0 then nalIdrWRadl else nalTrailR
    decSt ← decodePictureSlices decSt #[(nalType, 0, nal.extract 2 nal.size)]
    let mut chosen? : Option HevcDecodedFrame := decSt.dpb.back?
    for pf in decSt.dpb do
      if pf.poc == Int.ofNat f then
        chosen? := some pf
    let chosen ← chosen?
    refPic? := some (frameToRefPlanes chosen)
  some (vpsNal, spsNal, ppsNal, sliceNals)

def packLenPrefixed4 (nal : ByteArray) : ByteArray :=
  let n := nal.size
  let hdr := ByteArray.mk #[
    ((n >>> 24) &&& 0xFF).toUInt8,
    ((n >>> 16) &&& 0xFF).toUInt8,
    ((n >>> 8) &&& 0xFF).toUInt8,
    (n &&& 0xFF).toUInt8]
  ByteArray.append hdr nal

def encodeHevcFromYuv420p (width height : Nat) (yuv : ByteArray) (qp : Int := 28)
    (mp4 : Bool := false) (log2Ctb : Nat := 6)
    (tilesCol : Nat := 1) (tilesRow : Nat := 1) : Option ByteArray := do
  let (vpsNal, spsNal, ppsNal, sliceNals) ←
    encodeHevcNals width height yuv qp log2Ctb tilesCol tilesRow
  if !mp4 then
    let mut all : Array ByteArray := #[vpsNal, spsNal, ppsNal]
    for s in sliceNals do
      all := all.push s
    some (muxAnnexB all)
  else
    let hvcc := buildHvccRecord vpsNal spsNal ppsNal
    let samples := sliceNals.map packLenPrefixed4
    some (buildHevcMp4 samples width height hvcc)

end LeanAV.HevcMain
