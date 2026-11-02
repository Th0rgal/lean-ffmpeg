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
import LeanAV.Bitstream
import LeanAV.Video
import LeanAV.H264Entropy
import LeanAV.Format

namespace LeanAV.HevcMain

open LeanSys.Posix
open LeanAV.Spec
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

def stripRbspWithMap (ebsp : ByteArray) : Option RbspMap := Id.run do
  let mut out : ByteArray := ByteArray.empty
  let mut rbspToEbsp : Array Nat := #[0]
  let mut zeros : Nat := 0
  let mut i : Nat := 0
  let n := ebsp.size
  while i < n do
    let b := baGetD ebsp i 0
    if zeros >= 2 && b == 3 then
      if i + 1 < n && (baGetD ebsp (i + 1) 0).toNat > 3 then return none
      if i + 1 == n then return none
      zeros := 0
      i := i + 1
      continue
    out := out.push b
    if b == 0 then zeros := zeros + 1 else zeros := 0
    i := i + 1
    rbspToEbsp := rbspToEbsp.push i
  return some { rbsp := out, map := rbspToEbsp }

def insertRbspEpb (rbsp : ByteArray) : ByteArray := Id.run do
  let mut out : ByteArray := ByteArray.empty
  let mut zeros : Nat := 0
  for b in rbsp do
    if zeros >= 2 && b.toNat <= 3 then
      out := out.push 3
      zeros := 0
    out := out.push b
    if b == 0 then zeros := zeros + 1 else zeros := 0
  return out

def packHevcNal (nalType layerId tidPlus1 : Nat) (rbspBody : ByteArray) : ByteArray := Id.run do
  let b0 : UInt8 := (((nalType &&& 0x3F) <<< 1) ||| ((layerId >>> 5) &&& 1)).toUInt8
  let b1 : UInt8 := (((layerId &&& 0x1F) <<< 3) ||| (tidPlus1 &&& 0x7)).toUInt8
  let body := insertRbspEpb rbspBody
  let mut out := ByteArray.empty
  out := out.push b0
  out := out.push b1
  return ByteArray.append out body

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

def writeProfileTierLevel (w : HevcBitWriter) : HevcBitWriter := Id.run do
  let mut cur := ((w.putBits 0 2).putBit 0).putBits 1 5
  for i in [:32] do
    cur := cur.putBit (if i == 1 then 1 else 0)
  cur := ((((cur.putBit 1).putBit 0).putBit 1).putBit 1).putBits 0 44
  return cur.putBits 93 8

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

end LeanAV.HevcMain
