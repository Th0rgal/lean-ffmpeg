import base64
import hashlib
import json
import math
import os
import shlex
import shutil
import struct
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

REFMV_COMPOUND_UNCAP_M11_IVF_B64 = (
    "REtJRgAAIABBVjAxIAAgABkAAAABAAAABQAAAAAAAADmAQAAAAAAAAAAAAASAAoKAAAAAif+bXyAIDLVAxAAnQAA"
    "AgAAgM8MBG7Dij4myyXeK9qrIvQMxT3Ps8SQMzuAtbEr1PwXIuhniyZKyOAU+aTBtcnZdSgR94zx4vujT97sr8VW"
    "Fo4kutFctn30F/7WyoWExsOk//+EFs6ZprbCzAhCwd/xTEOcH0i4ikhS+QMFnvBDmKsEZd2Z0uNI3rkxTl+01GQm"
    "KGF0XN8k/x9OnqjuxcMGioOED1cEgDg45NXiI7LqHxFCv4Z+SI8MStuIwgUw8O9YGsvVJ05W5O6s2pjVfh7UfRv8"
    "ruosmeJWMmN4f3Gu/Ez28CrrfAGXBiErZkBmCCRrat51Rx22pyvFLrbH8Q28NGxSFmWPEiUSjnzZ17Aw1q8QGV2m"
    "MD1tiiLox2rYUHBFHZZHlVnRTJHvE2hrLNHTuFnsk7tmgfKcED6xOY1woFr+RWte6JZcmZQUQePDs8f033D7NpPv"
    "QmN5VndXISf8Kbkxe87OExJasA8rnfMWDvYLKawL7Nyj9eyLkbaYoBxExJLD8ZDTJkTsCBY8M14lBL4ig2SuM/Ab"
    "r56H06f9Q/YKkuw1h60O+JyJbeOnA3hFYO0dRXClNpqRrXUlngq6ZYk1l54ElOJUVcWMcGpIKFmgrx2DgC0GHP9v"
    "QWBrAgAAAQAAAAAAAAASADKnAygE4EAAACNZAAABJZdQAM8RuAZ11yU+eBMM5t0iZb4WquTF1MtdO/JHyGyM8F0O"
    "TKAT1RPFiBWlEFHPpY2aeCY2AIIES4yX5gykte1P9LkUqPK+Ze4tAzlbwzqWlaFNiv6pfn5zdNBn74B6nLxkkkqs"
    "UFwM/os+VwiX+IpMFU5t8Swc11Ml39V/Tz4ZbAmFoeoZjt5M3zetWw0JGsWSSprs5nhAK9873FlLpUMUadBBgTsz"
    "hFUjg61/XFtXICglLHkFfOY9P0KCBZnPOC98Q6LpKEsciPQjue2D3GqLAfCOINDQ3u0tjdX0aBUuY6S7nyZIjILV"
    "CILQcnIVWLpJwrKpUnk8K+UKuedbFnJv1qwGjZuMyGNFb11qz4U6ybvhoMdEM0I2bWqSbjQwTZux1QCk3FvczJWn"
    "UtG/mrvkBcImaWhhJAbT1uiBnmJAS7gFpljDADqQXFqjEjZpC6PYPMPlipmhQV34AxBOMKI3SMu1GCFVaxF4MngH"
    "HKc4qPGLRw4IdOxUEXwNqMpQyKnaHJEUu1ySZG1QTA+ITiDDSWAme+7rydRVQDJaKALggAAAo16AAAEgAVAAz0ma"
    "u8m4P+0AzHvltwspQrwnHrLOfIt7Ne1BcdOgpMjSUzQHJbmoOYZ/Gc5RLd1YZLCWK5aU6cj2JTVkcWJbj+tnLlsR"
    "S5fUS9aXMmEwA8IAAIEGyAAAAoss0ADPovSwnXG6NQLEYADgfhFUIjmulqH9mwIh6Ep2sUyEOXh/NknNLuXdciZM"
    "Mx5fn1Rb9bTbr5rpelOCH4efH2Y9QCZhCH+HkGO45TSX9rMTHCetBQAAAAIAAAAAAAAAEgAaAahiAAAAAwAAAAAA"
    "AAASADJeMAZECYABBsgAAAKALtAAwEYLZ4hJj61ISKJAWAwnfzOY4KQAY+MFD8YKzuF887uH2JTG5E1fs3Gf7fcd"
    "jG2uLgNyQMgBCtu+2Yw+B43T8AmjZzBT8nvQBpz8l2RUOhUAAAAEAAAAAAAAABIAMhEwCAgRABk7IAAACgAAgACH"
    "CQ=="
)
REFMV_COMPOUND_UNCAP_M11_YUV_SHA256 = (
    "79ec3fde567bce380b89bf6d9d321f66a64ca114024e3b17b0acb0aac1067365"
)
UNI_COMPOUND_CPU2_96X80_IVF_B64 = (
    "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"
    "J82tFfr2EwR1fz4QIVwWuKzKL5o/RiNw"
)
UNI_COMPOUND_CPU2_96X80_YUV_SHA256 = (
    "39baeb07af079ac0eba1602f878d94a5b686663fba86f59b8aa833991c849d34"
)

SR_KF_D12_IVF_B64 = (
    "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"
)
SR_KF_D16_IVF_B64 = (
    "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"
    "YA=="
)
SR_KF_D14_INTER_LR_IVF_B64 = (
    "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"
)
SCALED_INTER_SUPERRES_IVF_B64 = (
    "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"
)
RAV1E_4BYTE_AV1C_MP4_B64 = (
    "AAAAIGZ0eXBpc29tAAACAGlzb21hdjAxaXNvMm1wNDEAAAAIZnJlZQAACdhtZGF0Cg0AAAD5m/3x"
    "CFZAgICFMsIQEAIpSGJ+ezifwAfkA/sBBYCEQEJgAAAFmEkgggiqgOIufXWYzL9yPHafOmd3wRAY"
    "+Rr64RfxUjg6Rq2zbZMoqmH+HpD0piuKOuYzYtbiz6/GBOVV4fIEfzbeF9bD+Nquap1uXW/5VG9d"
    "3qSEIBjfkt2PCnU2DPAjBPumSOy4sCWDxT9mS0TXhPgOOoABe2gaxOp8UzpXiLP5LvAMkrW468uS"
    "jEz5O/ejSRe3BW7zCegvrYLN+AGIu0mweBby5I2uiv8tSkZov0yT1rQKVvbk+PHHgkiN0Yy6p8C8"
    "guaXsLIFMKO42Dm8xXvRtSMLVYb1ysdQleBJSLFDyyIS7KVDniqmuNni6pdeJv7Ic+w4B+8mKPCu"
    "h748k6pfphYqKCeMGL/UCNJUkxs99vHnVIB/Ed2ohWtnZmh4rCYBhBUsRcRlJcgn2lmWILBhGtfq"
    "d7UDMMteZz2UPC6Eq108RvbnX3/El0/uxtoTTOvzIAxi2no0Cl0TlmNX7o7cNko4wCL1AjQz7edh"
    "lHyHs9iu5kfsLmt7sGscpTST/svn2SDJL6Zm22IpatzmAhnC9g/CZAZw9P4Weg3I88X8FxzsdEYO"
    "SZ6VoCxhz3hgmWx83ZZdEw3xIfOilOk8+mkPubZJGfrtCrq5ia/0MZRDl8FnKay4jvDDfrou/8+K"
    "ezhYUesE8hLLqBOpsL5cJcRPVfTxH0xiUgUKmIicncHRjBL9Qbnx9WfB5hb4wzAdUYbHtWKvmWIb"
    "vXt44NqHffie/w+1FK/x6L/UBFEs7KkQ+wk+UCLnPoasCUU7m47xaD/lKc8/JBvOCipoUICTh94B"
    "wF/6yrLDW38Q4HIttLwmjgGbwCJptNVAJvU9INNdMRc14zWy0WF6jmaOfCY4+nHE9flO3R5fjEqv"
    "asN2U/N7PTcVDPj9iBO0NZLRCyVQVoVQj4SRP2hOCRoGthM6V1zGC4YP0haj2MxHzniGUTqHJ64Q"
    "U73FPN9N7tSSR+yO97EWnnkaTGTvJHgufu1aiGxdYj1EvZhvw66wfYAJ5PdfQ0b+oCIdyFkYzOGn"
    "VpHN0O1lhSeI23oXmXYIUxPMc+iNogAjcHktLrFytXf1lH/uvO9wT/4IIys5AhsAS1B/DBEyUR32"
    "GaEosaAqd8qEtXncZlC9ARU8zmKgUgmag8IqVyZM6f8ovrwICk9tpPPbAYrv1W817TRVQZdLjMes"
    "Q5tT+4z9W1ZT2/z760m/3xifZsTv3teq2wTRL+hdkY7agfNJqYWojH+zIhD2Z5BpDq6Cqxj/Xc2P"
    "a1/hGIttiQUal+ZXsuZ1PRzASh4UcYjfL3jnrRoBz9/TP06TqBo7kwih5xdQieKnEJQfXa7chN/P"
    "rC521mHFLlD28copVJmYOTD5v3RYbhx6CUlTO8rN8tM/F6B6ISH1u42Sx3a6ICgu9iW/bgwGKME5"
    "zDmm98yvGiV0XRNysnTbgqQyhIYvDE3aqNleTJg4+bkAahL429I9kIyDnG0rXGham3VzqvUyXq6T"
    "c2Ms9O29WpVXD4qKW14W7yz40eGExpaLN09eLnrpi7HjZlKlWLdPxza/S2TEqCPrkLFwExIQP4az"
    "KQegrMx1aNCFlkwJ0uAc92wRgE8iro65EkHEWWhS2HueqPAGpK8deqdnJzyeqcDe4ygGb0vN58vw"
    "bf+RhoWSmMK+MLjto3FNesI3YOh8Tuu6rxuEzQRiejI07YlQHyMeJehCrehdOpu0EkJoXZSS31W7"
    "RHfwVSGNehIfYkrILefykwnZUfzG3DsEj1jKI7KYHIeaKbktAqWqHqNhRq4U8A5hhBqqrmnymL2C"
    "YdRNlCnTpHgBnisuUmJLKqM05EKo9dSsgynyNR73QMmTpFApYJEbQ90bfDmhAXd3g7tnz1GkAWjo"
    "5Kjnaj+wzljcs5HcRhqJfN6hAPClytZ3bb6fEKZEzITqUfxNepjdsnhUJBWD3gB+Z/Y0jJgoWflL"
    "V5BRTRrV+pIoSS5CAK0fFTQ4SI7pe6bPusFzp8edLfRElp2/kbyn9CFWESPx0XYjaNwbUJdtpldK"
    "FdzIaIwQTcOhRW0l7LMqVEdbGlAxmC3Qz2Xjl9xKFE+hMMfQAydq0eybwr2OWogQCiG6aWXBLm1G"
    "55FZ6oxyHXoBMHDzYYc1ABGvFaALF3v2io77v6oOck4cWvprCOJlImA2Vacs5H0OPlGeveoZErdv"
    "67iz9IbP2SNvUnBUnHoc/00qHMZF0YxMs/C8gAo3lgnIjywVx+OhF8khGHTQklG3lNAT/Poi0brS"
    "u4IACPvpbIc+KKjG41jHqdDT6h02e0FVs4K8yNDhs53lMr5CU7i9d2rloGVxSu1TgUfxwWKOPW3x"
    "y6tDEu/6sP//8DWu6/9XcGOy1TkKwzihXRjorPOpFP+6Ds8ZERA3O+5JRjk4n932DoLXII+n1xz8"
    "CxOYWpNznnk0qvDqlExVZzn96oQcPUgIbJtbDNqY98DV4fWJj3kFOsryO6e9xIaDt07aBSJmyKux"
    "MakWhzYClVXrV2Sdmp63Y/r/qdOSjfq/MYOC+ZaNlGXGkKyA/VgW8QpUHu5JxNsePBqad9cmNVNZ"
    "KN6lDgBHrJbwm+qhmByU7tdos8NSbWi7UIwIG/vVXFfd1y8RPUfeLdqufTCE2NYvnRT8FfwpbWRZ"
    "N35sz5Pv9se+tc6HMR45/OmAx0D8VCuegoHpiTuFXl7j+LsxnENb1/HNZny1hy37XSDoIwmgZGXI"
    "ii/5byfyIEZfCrK1YmGYV3iWtaMdNFuzJNU2mNSvKxCX/KUBJ+GqkpEmMcmzsm7qcyDkaPFqTgpt"
    "GVj1FEzQm7XBqBkKHmsy+QIwCiABQBAEjJH+93LsMLGJFhAgiqwA3DDabwNkKcjHZQ75LURP8mYd"
    "C71j5tGbCVuf3FqmVAXOyrc49Z1E6V0QXveGKw1EIZZ2m9A9f9hZWKNfhftpy7LkxZgyejS5GpJ0"
    "XlfaxDWArvTcUir3UTf4G8/myA6+4nYzgYkpMlzRS4NrfXMup7PARx7qu7bMjGc2uV9QPxJ+Cp83"
    "F5qvwe+Eu8DKCzvqnD5CbU9XtNEPX6KVQzOcb4pe7c3d3iO1p2QMFW0quLwjVdhI9UIW/yBSZMaG"
    "5fLdIf+bPFgi0LMfTrygjTQvys5yWgBc9/Vx3pv1P112bqLuhSa8UwUyoMNUf4kcWrbLk3TMflZv"
    "ZlEuLCirA8Siuui3oHlupRJdomIZGkWSjVnsPNqKoQ9NfQ7y3aSAD+jiFXexN/MYUKkLJKYCovZi"
    "oHG0qGGPTTVfTHyGP5Ami+o1sjxnn/LyvCb0iP24bMBoIk1g0SqrfmMMoKElBGFjnVnCXgAAAxNt"
    "b292AAAAbG12aGQAAAAAAAAAAAAAAAAAAAPoAAAAUAABAAABAAAAAAAAAAAAAAAAAQAAAAAAAAAA"
    "AAAAAAAAAAEAAAAAAAAAAAAAAAAAAEAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACAAAC"
    "PXRyYWsAAABcdGtoZAAAAAMAAAAAAAAAAAAAAAEAAAAAAAAAUAAAAAAAAAAAAAAAAAAAAAAAAQAA"
    "AAAAAAAAAAAAAAAAAAEAAAAAAAAAAAAAAAAAAEAAAAAAgAAAAGAAAAAAACRlZHRzAAAAHGVsc3QA"
    "AAAAAAAAAQAAAFAAAAAAAAEAAAAAAbVtZGlhAAAAIG1kaGQAAAAAAAAAAAAAAAAAADIAAAAEAFXE"
    "AAAAAAAtaGRscgAAAAAAAAAAdmlkZQAAAAAAAAAAAAAAAFZpZGVvSGFuZGxlcgAAAAFgbWluZgAA"
    "ABR2bWhkAAAAAQAAAAAAAAAAAAAAJGRpbmYAAAAcZHJlZgAAAAAAAAABAAAADHVybCAAAAABAAAB"
    "IHN0YmwAAACgc3RzZAAAAAAAAAABAAAAkGF2MDEAAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAgABg"
    "AEgAAABIAAAAAAAAAAEWTGF2YzYwLjMxLjEwMiBsaWJyYXYxZQAAAAAAAAAAAAAY//8AAAAMYXYx"
    "Q4EfDAAAAAAKZmllbAEAAAAAEHBhc3AAAAABAAAAAQAAABRidHJ0AAAAAAAD1UAAA9VAAAAAGHN0"
    "dHMAAAAAAAAAAQAAAAIAAAIAAAAAFHN0c3MAAAAAAAAAAQAAAAEAAAAcc3RzYwAAAAAAAAABAAAA"
    "AQAAAAIAAAABAAAAHHN0c3oAAAAAAAAAAAAAAAIAAAhUAAABfAAAABRzdGNvAAAAAAAAAAEAAAAw"
    "AAAAYnVkdGEAAABabWV0YQAAAAAAAAAhaGRscgAAAAAAAAAAbWRpcmFwcGwAAAAAAAAAAAAAAAAt"
    "aWxzdAAAACWpdG9vAAAAHWRhdGEAAAABAAAAAExhdmY2MC4xNi4xMDA="
)

SR_KF_D12_YUV_SHA256 = "a2c514966fa54baad05292321e547fa67f44cfc395e721fff7bb8e08169a2f62"
SR_KF_D16_YUV_SHA256 = "e34a9cf8f1ceee6a9c0f0bfe69900130ea2f539de8c492762f35c8351f49a9d9"
SR_KF_D14_INTER_LR_YUV_SHA256 = "5c55bc988aa595c3a9228303a4ff16e4f9d977861c4d2baaf98e6b2426d19d9f"
RAV1E_4BYTE_AV1C_YUV_SHA256 = "6551f73ce8c88950afb6c7f0ac8204d7ab6a025ce2acc2f5f4cce008e74ee7e1"

ROOT = Path(__file__).resolve().parents[2]
LFFMPEG = Path(os.environ.get("LFFMPEG", ROOT / ".lake/build/bin/lffmpeg"))
FFMPEG = os.environ.get("FFMPEG") or shutil.which("ffmpeg") or "/usr/bin/ffmpeg"
FFPROBE = os.environ.get("FFPROBE") or shutil.which("ffprobe") or "/usr/bin/ffprobe"
STRACE = shutil.which("strace")
ISO_ENV = {
    "PATH": "/nonexistent",
}


def run(*args, env=None, check=True, timeout=60):
    return subprocess.run(
        [str(a) for a in args],
        check=check,
        capture_output=True,
        env=env,
        timeout=timeout,
    )



def av1_decoder_available():
    try:
        out = run(FFMPEG, "-hide_banner", "-decoders").stdout.decode(errors="replace")
    except (OSError, subprocess.SubprocessError):
        return False
    return "(codec av1)" in out or " av1 " in out


def libaom_av1_available():
    try:
        out = run(FFMPEG, "-hide_banner", "-encoders").stdout.decode(errors="replace")
    except (OSError, subprocess.SubprocessError):
        return False
    return "libaom-av1" in out


def libsvtav1_available():
    try:
        out = run(FFMPEG, "-hide_banner", "-encoders").stdout.decode(errors="replace")
    except (OSError, subprocess.SubprocessError):
        return False
    return "libsvtav1" in out


def librav1e_available():
    try:
        out = run(FFMPEG, "-hide_banner", "-encoders").stdout.decode(errors="replace")
    except (OSError, subprocess.SubprocessError):
        return False
    return "librav1e" in out


def aac_encoder_available():
    try:
        out = run(FFMPEG, "-hide_banner", "-encoders").stdout.decode(errors="replace")
    except (OSError, subprocess.SubprocessError):
        return False
    return " aac " in out


def isobmff_box_types(data):
    containers = {
        b"moov", b"trak", b"mdia", b"minf", b"dinf", b"stbl",
        b"edts", b"udta", b"mvex", b"moof", b"traf", b"mfra",
    }
    found = []

    def walk(buf, start, end):
        pos = start
        while pos + 8 <= end:
            sz = int.from_bytes(buf[pos:pos + 4], "big")
            typ = bytes(buf[pos + 4:pos + 8])
            hdr = 8
            if sz == 1:
                if pos + 16 > end:
                    break
                sz = int.from_bytes(buf[pos + 8:pos + 16], "big")
                hdr = 16
            elif sz == 0:
                sz = end - pos
            if sz < hdr or pos + sz > end:
                break
            found.append(typ)
            if typ in containers:
                walk(buf, pos + hdr, pos + sz)
            elif typ == b"stsd" and pos + hdr + 8 <= pos + sz:
                walk(buf, pos + hdr + 8, pos + sz)
            elif typ == b"av01" and pos + hdr + 78 <= pos + sz:
                walk(buf, pos + hdr + 78, pos + sz)
            pos += sz

    walk(data, 0, len(data))
    return found


def ffprobe_available():
    try:
        out = run(FFPROBE, "-version").stdout.decode(errors="replace")
    except (OSError, subprocess.SubprocessError):
        return False
    return out.startswith("ffprobe version ")


def synth_yuv420p(w, h, frames):
    buf = bytearray()
    for f in range(frames):
        for y in range(h):
            for x in range(w):
                v = (x * 7 + y * 5 + f * 19 + ((x ^ y) & 15) * 3) & 0xFF
                buf.append(v)
        cw = w // 2
        ch = h // 2
        for y in range(ch):
            for x in range(cw):
                buf.append((88 + x * 3 + y * 2 + f * 11) & 0xFF)
        for y in range(ch):
            for x in range(cw):
                buf.append((164 - x * 2 + y * 3 - f * 7) & 0xFF)
    return bytes(buf)


def psnr_db(ref_bytes, got_bytes):
    if len(ref_bytes) != len(got_bytes) or not ref_bytes:
        return 0.0
    mse = sum((a - b) * (a - b) for a, b in zip(ref_bytes, got_bytes)) / len(ref_bytes)
    if mse == 0.0:
        return 99.0
    return 10.0 * math.log10((255.0 * 255.0) / mse)


def decode_args(in_path, out_path):
    out_str = str(out_path)
    fmt = "null" if out_str == "-" else "rawvideo"
    return [LFFMPEG, "-json", "-y", "-i", in_path, "-an", "-f", fmt, out_path]


def encode_args(w, h, in_path, out_path, qidx=60, fmt=None, tc=1, tr=1):
    out_str = str(out_path)
    if fmt is None or fmt == "auto":
        if out_str.endswith(".mp4"):
            mux_fmt = "mp4"
        elif out_str.endswith(".ivf"):
            mux_fmt = "ivf"
        else:
            mux_fmt = "obu"
    else:
        mux_fmt = fmt
    return [
        LFFMPEG, "-json", "-y",
        "-f", "rawvideo", "-pix_fmt", "yuv420p", "-s", f"{w}x{h}",
        "-i", in_path,
        "-an", "-c:v", "av1", "-qp", str(qidx),
        "-tile-columns", str(tc.bit_length() - 1),
        "-tile-rows", str(tr.bit_length() - 1),
        "-f", mux_fmt, out_path,
    ]


PIX_SPECS = {
    "yuv420p":     (0, 8,  1, 1, "4:2:0"),
    "yuv422p":     (2, 8,  1, 0, "4:2:2"),
    "yuv444p":     (1, 8,  0, 0, "4:4:4"),
    "yuv420p10le": (0, 10, 1, 1, "4:2:0"),
    "yuv422p10le": (2, 10, 1, 0, "4:2:2"),
    "yuv444p10le": (1, 10, 0, 0, "4:4:4"),
    "yuv420p12le": (2, 12, 1, 1, "4:2:0"),
    "yuv422p12le": (2, 12, 1, 0, "4:2:2"),
    "yuv444p12le": (2, 12, 0, 0, "4:4:4"),
}


def synth_raw_planar(w, h, pix_fmt, frames):
    _, bd, ss_h, ss_v, _ = PIX_SPECS[pix_fmt]
    cw = (w + ss_h) >> ss_h
    ch = (h + ss_v) >> ss_v
    mx = (1 << bd) - 1
    out = bytearray()
    for f in range(frames):
        y_vals = [((x * 19 + y * 31 + f * 37 + (x ^ y) * 7) % (mx + 1)) for y in range(h) for x in range(w)]
        u_vals = [((x * 23 + y * 13 + f * 29 + 100) % (mx + 1)) for y in range(ch) for x in range(cw)]
        v_vals = [((x * 17 + y * 29 + f * 41 + 200) % (mx + 1)) for y in range(ch) for x in range(cw)]
        for arr in (y_vals, u_vals, v_vals):
            if bd == 8:
                out.extend(arr)
            else:
                out.extend(struct.pack(f"<{len(arr)}H", *arr))
    return bytes(out)


def psnr_raw_db(ref_bytes, got_bytes, bd):
    if len(ref_bytes) != len(got_bytes) or not ref_bytes:
        return 0.0
    if ref_bytes == got_bytes:
        return 99.0
    if bd == 8:
        a = list(ref_bytes)
        b = list(got_bytes)
    else:
        n = len(ref_bytes) // 2
        a = struct.unpack(f"<{n}H", ref_bytes)
        b = struct.unpack(f"<{n}H", got_bytes)
    mse = sum((x - y) * (x - y) for x, y in zip(a, b)) / len(a)
    if mse == 0.0:
        return 99.0
    mx = float((1 << bd) - 1)
    return 10.0 * math.log10((mx * mx) / mse)


def _find_lean_tool(name):
    found = shutil.which(name)
    if found:
        return Path(found)
    for cand in (
        Path.home() / ".elan/bin" / name,
        Path("/var/lib/sandboxed-node/work/caches/elan/bin") / name,
    ):
        if cand.exists():
            return cand
    raise RuntimeError(f"Unable to locate {name} binary")


AV1_RAW_DRIVER_LEAN_SRC = """import LeanAV.Av1Main

open LeanAV.Av1Main

def sampleFilmGrain (seed : Nat) (update : Bool) (chromaFromLuma : Bool) (overlap : Bool) : Av1FilmGrainParams :=
  { applyGrain := true
  , grainSeed := seed % 65536
  , updateGrain := update
  , filmGrainParamsRefIdx := 0
  , numYPoints := 4
  , yPoints := #[(0, 20), (64, 45), (160, 60), (255, 35)]
  , chromaScalingFromLuma := chromaFromLuma
  , numCbPoints := if chromaFromLuma then 0 else 3
  , cbPoints := if chromaFromLuma then #[] else #[(0, 15), (128, 30), (255, 25)]
  , numCrPoints := if chromaFromLuma then 0 else 3
  , crPoints := if chromaFromLuma then #[] else #[(0, 18), (128, 32), (255, 22)]
  , grainScalingMinus8 := 3
  , arCoeffLag := 2
  , arCoeffsY := #[1, -2, 3, -1, 2, 0, -3, 4, -2, 1, 2, -4]
  , arCoeffsCb := #[1, -1, 2, -2, 1, 0, -2, 3, -1, 1, 0, -2, 3]
  , arCoeffsCr := #[-1, 2, -2, 1, 0, -1, 2, -3, 1, -1, 2, 1, -4]
  , arCoeffShiftMinus6 := 2
  , grainScaleShift := 1
  , cbMult := 128
  , cbLumaMult := 192
  , cbOffset := 256
  , crMult := 128
  , crLumaMult := 192
  , crOffset := 256
  , overlapFlag := overlap
  , clipToRestrictedRange := false
  }

def main (args : List String) : IO UInt32 := do
  match args with
  | ["decode", inPath, outPath] =>
    let data ← IO.FS.readBinFile inPath
    match decodeAv1ToRaw data with
    | none => return 1
    | some (w, h, nFrames, bd, pixFmt, raw) =>
      IO.FS.writeBinFile outPath raw
      IO.println s!"{w},{h},{nFrames},{bd},{pixFmt},{raw.size}"
      return 0
  | ["decode420", inPath, outPath] =>
    let data ← IO.FS.readBinFile inPath
    match decodeAv1ToYuv420p data with
    | none => return 1
    | some (w, h, nFrames, raw) =>
      IO.FS.writeBinFile outPath raw
      IO.println s!"{w},{h},{nFrames},{raw.size}"
      return 0
  | ["encode", wStr, hStr, pixFmt, qStr, fmt, tcStr, trStr, fgMode, inPath, outPath] =>
    let some w := wStr.toNat? | return 2
    let some h := hStr.toNat? | return 2
    let some q := qStr.toNat? | return 2
    let some tc := tcStr.toNat? | return 2
    let some tr := trStr.toNat? | return 2
    let fg? : Option Av1FilmGrainParams :=
      match fgMode with
      | "none" => none
      | "fg1" => some (sampleFilmGrain 7391 true false true)
      | "fg_cfl" => some (sampleFilmGrain 12345 true true false)
      | "fg_reuse" => some (sampleFilmGrain 9999 false false true)
      | _ => none
    let raw ← IO.FS.readBinFile inPath
    match encodeAv1FromRaw w h pixFmt raw q fmt tc tr fg? with
    | none => return 1
    | some bytes =>
      IO.FS.writeBinFile outPath bytes
      IO.println s!"{bytes.size}"
      return 0
  | ["encode_mp4_payloads", wStr, hStr, pixFmt, qStr, inPath, outPath] =>
    let some w := wStr.toNat? | return 2
    let some h := hStr.toNat? | return 2
    let some q := qStr.toNat? | return 2
    let raw ← IO.FS.readBinFile inPath
    match encodeAv1Mp4TrackPayloadsRaw w h pixFmt raw q with
    | none => return 1
    | some (av1c, samples) =>
      IO.FS.writeBinFile outPath av1c
      IO.println s!"{av1c.size},{samples.size}"
      return 0
  | _ => return 2
"""


@unittest.skipUnless(LFFMPEG.exists(), "lffmpeg is not built")
class TestAv1Main(unittest.TestCase):
    _cls_tmp = None
    _raw_driver = None

    @classmethod
    def tearDownClass(cls):
        if cls._cls_tmp is not None:
            cls._cls_tmp.cleanup()
            cls._cls_tmp = None
            cls._raw_driver = None

    @classmethod
    def _get_raw_driver(cls):
        if cls._raw_driver is not None:
            return cls._raw_driver
        cls._cls_tmp = tempfile.TemporaryDirectory()
        d = Path(cls._cls_tmp.name)
        lean_bin = _find_lean_tool("lean")
        leanc_bin = _find_lean_tool("leanc")
        lean_src = d / "av1_raw_driver.lean"
        c_file = d / "av1_raw_driver.c"
        driver_bin = d / "av1_raw_driver"
        lean_src.write_text(AV1_RAW_DRIVER_LEAN_SRC)
        lean_env = dict(
            os.environ,
            PATH=f"{lean_bin.parent}:{os.environ.get('PATH', '')}:/var/lib/sandboxed-node/work/caches/elan/bin:/usr/local/bin:/usr/bin:/bin",
            LEAN_PATH=f"{ROOT / '.lake/build/lib/lean'}:{ROOT.parent / 'lean-sys/.lake/build/lib/lean'}",
        )
        try:
            subprocess.run(
                [str(lean_bin), "-c", str(c_file), str(lean_src)],
                cwd=d, env=lean_env, check=True, capture_output=True, timeout=180,
            )
            rsp_text = (ROOT / ".lake/build/bin/lffmpeg.rsp").read_text()
            rsp_args = (
                [s.strip().strip('"') for s in rsp_text.splitlines() if s.strip()]
                if "\n" in rsp_text else shlex.split(rsp_text)
            )
            objects = [
                s for s in rsp_args
                if s.endswith((".o.export", ".a", "leanav_zero_exec_stub.o"))
                and not s.endswith("/LeanAV/Main.c.o.export")
            ]
            subprocess.run(
                [str(leanc_bin), "-O2", "-o", str(driver_bin), str(c_file), *objects, "-lpthread"],
                cwd=ROOT, env=lean_env, check=True, capture_output=True, timeout=180,
            )
        except Exception:
            cls._cls_tmp.cleanup()
            cls._cls_tmp = None
            raise
        cls._raw_driver = driver_bin
        return driver_bin

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.dir = Path(self._tmp.name)

    def tearDown(self):
        self._tmp.cleanup()

    def _ffmpeg_decode_raw(self, in_path, pix_fmt, mux_fmt=None):
        out_raw = self.dir / f"{Path(in_path).name}.{pix_fmt}.ff.raw"
        cmd = [FFMPEG, "-y", "-v", "error"]
        if mux_fmt == "obu" or str(in_path).endswith(".obu"):
            cmd += ["-f", "obu"]
        cmd += ["-i", in_path, "-f", "rawvideo", "-pix_fmt", pix_fmt, out_raw]
        run(*cmd)
        return out_raw.read_bytes()

    def _ffmpeg_decode_yuv420p(self, in_path):
        out_yuv = self.dir / f"{Path(in_path).name}.ff.yuv"
        run(
            FFMPEG, "-y", "-v", "error",
            "-i", in_path,
            "-f", "rawvideo", "-pix_fmt", "yuv420p", out_yuv,
        )
        return out_yuv.read_bytes()

    def test_libaom_av1_to_lffmpeg_bit_exact_matrix(self):
        if not libaom_av1_available():
            self.skipTest("ffmpeg with libaom-av1 unavailable")
        cases = [
            ("intra_nocdef.ivf", 64, 48, 1, "ivf", ["-cpu-used", "8", "-crf", "32", "-g", "1", "-aom-params", "enable-cdef=0"]),
            ("intra_cdef_cpu8.ivf", 64, 48, 1, "ivf", ["-cpu-used", "8", "-crf", "32", "-g", "1"]),
            ("intra_cdef_cpu4.ivf", 64, 48, 1, "ivf", ["-cpu-used", "4", "-crf", "30", "-g", "1"]),
            ("ip_lag0_cpu8.ivf", 96, 80, 5, "ivf", ["-cpu-used", "8", "-crf", "36", "-lag-in-frames", "0"]),
            ("ip_lag0_cpu4.ivf", 96, 80, 4, "ivf", ["-cpu-used", "4", "-crf", "34", "-lag-in-frames", "0"]),
            ("ip_altref_def_cpu8.ivf", 96, 80, 5, "ivf", ["-cpu-used", "8", "-crf", "36"]),
            ("ip_altref_def_cpu4.ivf", 96, 80, 5, "ivf", ["-cpu-used", "4", "-crf", "34"]),
            ("tiles_2x2_lag0.ivf", 160, 128, 4, "ivf", ["-cpu-used", "8", "-crf", "34", "-lag-in-frames", "0", "-tile-columns", "1", "-tile-rows", "1", "-row-mt", "0"]),
            ("tiles_2x2_altref_cpu4.ivf", 160, 128, 4, "ivf", ["-cpu-used", "4", "-crf", "34", "-tile-columns", "1", "-tile-rows", "1", "-row-mt", "0"]),
            ("crop_98x66_cpu8.ivf", 98, 66, 4, "ivf", ["-cpu-used", "8", "-crf", "34"]),
            ("crop_98x66_cpu4.ivf", 98, 66, 3, "ivf", ["-cpu-used", "4", "-crf", "32"]),
            ("crop_130x98_cpu8.ivf", 130, 98, 3, "ivf", ["-cpu-used", "8", "-crf", "34"]),
            ("crop_130x98_cpu4.ivf", 130, 98, 3, "ivf", ["-cpu-used", "4", "-crf", "32"]),
            ("lossless_intra.ivf", 64, 48, 1, "ivf", ["-cpu-used", "8", "-crf", "0", "-g", "1", "-aom-params", "lossless=1"]),
            ("lossless_inter.ivf", 64, 48, 3, "ivf", ["-cpu-used", "8", "-crf", "0", "-lag-in-frames", "0", "-aom-params", "lossless=1"]),
            ("raw_stream.obu", 96, 80, 4, "obu", ["-cpu-used", "8", "-crf", "36"]),
            ("isobmff_av1c.mp4", 96, 80, 5, "mp4", ["-cpu-used", "8", "-crf", "36"]),
            ("isobmff_crop_98x66.mp4", 98, 66, 3, "mp4", ["-cpu-used", "8", "-crf", "34"]),
            ("uni_compound_cpu2_96x80.ivf", 96, 80, 6, "ivf", [
                "-cpu-used", "2", "-crf", "28", "-g", "6", "-aom-params",
                "enable-warped-motion=1:enable-obmc=1:enable-onesided-comp=1:"
                "enable-dist-wtd-comp=1:enable-diff-wtd-comp=1:enable-masked-comp=1:"
                "enable-interinter-wedge=1:enable-interintra-wedge=1:"
                "enable-interintra-comp=1:enable-smooth-interintra=1:"
                "enable-paeth-intra=1:enable-cfl-intra=1:enable-palette=1:"
                "enable-intrabc=1:enable-global-motion=1:enable-ref-frame-mvs=1:"
                "enable-dual-filter=1",
            ]),
            ("uni_compound_cpu2_tiles_128x96.ivf", 128, 96, 6, "ivf", [
                "-cpu-used", "2", "-crf", "28", "-g", "6",
                "-tile-columns", "1", "-tile-rows", "1", "-row-mt", "0",
                "-aom-params",
                "enable-warped-motion=1:enable-obmc=1:enable-onesided-comp=1:"
                "enable-dist-wtd-comp=1:enable-diff-wtd-comp=1:enable-masked-comp=1:"
                "enable-interinter-wedge=1:enable-interintra-wedge=1:"
                "enable-interintra-comp=1:enable-smooth-interintra=1:"
                "enable-paeth-intra=1:enable-cfl-intra=1:enable-palette=1:"
                "enable-intrabc=1:enable-global-motion=1:enable-ref-frame-mvs=1:"
                "enable-dual-filter=1",
            ]),
        ]
        for name, w, h, nf, mux_fmt, aom_opts in cases:
            with self.subTest(case=name):
                src_yuv = self.dir / f"src_{name}.yuv"
                raw_src = synth_yuv420p(w, h, nf)
                src_yuv.write_bytes(raw_src)
                stream_path = self.dir / name
                cmd = [
                    FFMPEG, "-y", "-v", "error",
                    "-f", "rawvideo", "-pix_fmt", "yuv420p", "-s", f"{w}x{h}", "-r", "25",
                    "-i", src_yuv,
                    "-c:v", "libaom-av1", "-pix_fmt", "yuv420p",
                    *aom_opts,
                ]
                if mux_fmt == "obu":
                    cmd += ["-f", "obu"]
                elif mux_fmt == "ivf":
                    cmd += ["-f", "ivf"]
                cmd.append(stream_path)
                run(*cmd)

                ref_yuv = self._ffmpeg_decode_yuv420p(stream_path)
                lean_yuv_path = self.dir / f"lean_{name}.yuv"
                dec_proc = run(*decode_args(stream_path, lean_yuv_path), env=ISO_ENV)
                dec_meta = json.loads(dec_proc.stdout.decode())
                self.assertTrue(dec_meta["ok"])
                self.assertEqual(dec_meta["width"], w)
                self.assertEqual(dec_meta["height"], h)
                self.assertEqual(dec_meta["frames"], nf)
                lean_bytes = lean_yuv_path.read_bytes()
                self.assertEqual(lean_bytes, ref_yuv)
                if "lossless" in name:
                    self.assertEqual(lean_bytes, raw_src)

                probe_proc = run(LFFMPEG, "av1-probe", stream_path, env=ISO_ENV)
                probe = json.loads(probe_proc.stdout.decode())
                self.assertTrue(probe["ok"])
                self.assertEqual(probe["codec"], "av1")
                self.assertEqual(probe["container"], mux_fmt)
                self.assertEqual(probe["profile"], 0)
                self.assertEqual(probe["width"], w)
                self.assertEqual(probe["height"], h)
                self.assertEqual(probe["bit_depth"], 8)
                self.assertEqual(probe["chroma_subsampling"], "4:2:0")
                self.assertEqual(probe["frames"], nf)

    def _assert_embedded_superres(self, name, w, h, coded_w, nf, expect_lr, b64, sha):
        stream_path = self.dir / name
        stream_path.write_bytes(base64.b64decode(b64))
        lean_yuv_path = self.dir / f"lean_{name}.yuv"
        dec_proc = run(*decode_args(stream_path, lean_yuv_path), env=ISO_ENV)
        dec_meta = json.loads(dec_proc.stdout.decode())
        self.assertTrue(dec_meta["ok"])
        self.assertEqual(dec_meta["width"], w)
        self.assertEqual(dec_meta["height"], h)
        self.assertEqual(dec_meta["frames"], nf)
        lean_bytes = lean_yuv_path.read_bytes()
        self.assertEqual(len(lean_bytes), w * h * 3 // 2 * nf)
        self.assertEqual(hashlib.sha256(lean_bytes).hexdigest(), sha)
        if av1_decoder_available():
            self.assertEqual(lean_bytes, self._ffmpeg_decode_yuv420p(stream_path))
        probe = json.loads(run(LFFMPEG, "av1-probe", stream_path, env=ISO_ENV).stdout.decode())
        self.assertTrue(probe["ok"])
        self.assertTrue(probe["superres"])
        self.assertLess(probe["coded_width"], probe["width"])
        self.assertEqual(probe["coded_width"], coded_w)
        self.assertEqual(probe["loop_restoration"], expect_lr)
        self.assertEqual(probe["frames"], nf)

    def test_embedded_svtav1_superres_fixtures(self):
        cases = [
            ("sr_kf_d12.ivf", 128, 96, 85, 1, False, SR_KF_D12_IVF_B64, SR_KF_D12_YUV_SHA256),
            ("sr_kf_d16.ivf", 128, 96, 64, 1, False, SR_KF_D16_IVF_B64, SR_KF_D16_YUV_SHA256),
            ("sr_kf_d14_inter_lr.ivf", 128, 96, 73, 3, True, SR_KF_D14_INTER_LR_IVF_B64, SR_KF_D14_INTER_LR_YUV_SHA256),
        ]
        for name, w, h, coded_w, nf, expect_lr, b64, sha in cases:
            with self.subTest(case=name):
                self._assert_embedded_superres(name, w, h, coded_w, nf, expect_lr, b64, sha)

    def test_embedded_scaled_inter_superres_rejected(self):
        scaled_path = self.dir / "scaled_inter_superres.ivf"
        scaled_path.write_bytes(base64.b64decode(SCALED_INTER_SUPERRES_IVF_B64))
        self.assertNotEqual(
            run(*decode_args(scaled_path, "-"), env=ISO_ENV, check=False).returncode,
            0,
        )
        self.assertNotEqual(
            run(LFFMPEG, "av1-probe", scaled_path, env=ISO_ENV, check=False).returncode,
            0,
        )

    def test_svtav1_superres_to_lffmpeg_bit_exact(self):
        if sys.platform == "darwin" or not libsvtav1_available():
            return
        cases = [
            ("sr_kf_d12.ivf", 128, 96, 1, "lp=1:superres-mode=1:superres-denom=8:superres-kf-denom=12"),
            ("sr_kf_d16.ivf", 128, 96, 1, "lp=1:superres-mode=1:superres-denom=8:superres-kf-denom=16"),
            ("sr_kf_d14_lr.ivf", 256, 192, 1, "lp=1:superres-mode=1:superres-denom=8:superres-kf-denom=14:enable-restoration=1"),
            ("sr_kf_d12_inter.ivf", 128, 96, 4, "lp=1:superres-mode=1:superres-denom=8:superres-kf-denom=12"),
            ("sr_kf_d14_inter_lr.ivf", 256, 192, 6, "lp=1:superres-mode=1:superres-denom=8:superres-kf-denom=14:enable-restoration=1"),
        ]
        for name, w, h, nf, svt_params in cases:
            with self.subTest(case=name):
                stream_path = self.dir / name
                run(
                    FFMPEG, "-y", "-v", "error",
                    "-f", "lavfi", "-i", f"testsrc2=size={w}x{h}:rate=25:duration=1",
                    "-c:v", "libsvtav1", "-preset", "12", "-pix_fmt", "yuv420p",
                    "-svtav1-params", svt_params,
                    "-frames:v", str(nf), "-f", "ivf", stream_path,
                )
                ref_yuv = self._ffmpeg_decode_yuv420p(stream_path)
                lean_yuv_path = self.dir / f"lean_{name}.yuv"
                dec_proc = run(*decode_args(stream_path, lean_yuv_path), env=ISO_ENV)
                dec_meta = json.loads(dec_proc.stdout.decode())
                self.assertTrue(dec_meta["ok"])
                self.assertEqual(dec_meta["width"], w)
                self.assertEqual(dec_meta["height"], h)
                self.assertEqual(dec_meta["frames"], nf)
                self.assertEqual(lean_yuv_path.read_bytes(), ref_yuv)
                probe = json.loads(run(LFFMPEG, "av1-probe", stream_path, env=ISO_ENV).stdout.decode())
                self.assertTrue(probe["ok"])
                self.assertTrue(probe["superres"])
                self.assertEqual(probe["frames"], nf)

    def test_lffmpeg_encode_to_ffmpeg_and_ffprobe_parity(self):
        if not av1_decoder_available():
            self.skipTest("ffmpeg unavailable")
        has_ffprobe = ffprobe_available()
        cases = [
            ("enc_lossless_64x48.obu", 64, 48, 2, 0, "obu", 1, 1),
            ("enc_lossless_98x66.ivf", 98, 66, 2, 0, "ivf", 1, 1),
            ("enc_lossless_mp4.mp4", 64, 48, 2, 0, "mp4", 1, 1),
            ("enc_q60_64x48.obu", 64, 48, 3, 60, "obu", 1, 1),
            ("enc_q60_96x80.ivf", 96, 80, 3, 60, "ivf", 1, 1),
            ("enc_q60_96x80.mp4", 96, 80, 3, 60, "mp4", 1, 1),
            ("enc_q60_crop_130x98.ivf", 130, 98, 2, 60, "ivf", 1, 1),
            ("enc_q60_tiles_2x2.obu", 128, 128, 2, 60, "obu", 2, 2),
            ("enc_q60_tiles_2x2.ivf", 128, 128, 3, 60, "ivf", 2, 2),
            ("enc_q60_tiles_2x2.mp4", 128, 128, 2, 60, "mp4", 2, 2),
        ]
        for name, w, h, nf, qidx, fmt, tc, tr in cases:
            with self.subTest(case=name):
                raw_in = synth_yuv420p(w, h, nf)
                in_path = self.dir / f"in_{name}.yuv"
                out_bs = self.dir / name
                lean_dec = self.dir / f"dec_{name}.yuv"
                in_path.write_bytes(raw_in)

                enc_proc = run(
                    *encode_args(w, h, in_path, out_bs, qidx, fmt, tc, tr),
                    env=ISO_ENV,
                )
                enc_meta = json.loads(enc_proc.stdout.decode())
                self.assertTrue(enc_meta["ok"])
                self.assertEqual(enc_meta["frames"], nf)
                self.assertGreater(out_bs.stat().st_size, 0)

                if fmt == "mp4":
                    mp4_boxes = isobmff_box_types(out_bs.read_bytes())
                    self.assertIn(b"av1C", mp4_boxes)
                    self.assertNotIn(b"ctts", mp4_boxes)

                run(*decode_args(out_bs, lean_dec), env=ISO_ENV)
                ff_yuv = self._ffmpeg_decode_yuv420p(out_bs)
                lean_bytes = lean_dec.read_bytes()
                self.assertEqual(lean_bytes, ff_yuv)
                if qidx == 0:
                    self.assertEqual(ff_yuv, raw_in)
                else:
                    self.assertGreater(psnr_db(raw_in, ff_yuv), 30.0)

                probe = json.loads(run(LFFMPEG, "av1-probe", out_bs, env=ISO_ENV).stdout.decode())
                self.assertTrue(probe["ok"])
                self.assertEqual(probe["container"], fmt)
                self.assertEqual(probe["width"], w)
                self.assertEqual(probe["height"], h)
                self.assertEqual(probe["frames"], nf)
                self.assertEqual(probe["tile_cols"], tc)
                self.assertEqual(probe["tile_rows"], tr)

                if has_ffprobe:
                    fp_proc = run(
                        FFPROBE, "-v", "error", "-select_streams", "v:0",
                        "-count_frames",
                        "-show_entries", "stream=codec_name,profile,pix_fmt,width,height,nb_read_frames",
                        "-of", "json", out_bs,
                    )
                    st = json.loads(fp_proc.stdout.decode())["streams"][0]
                    self.assertEqual(st["codec_name"], "av1")
                    self.assertEqual(st["profile"], "Main")
                    self.assertEqual(st["pix_fmt"], "yuv420p")
                    self.assertEqual(st["width"], w)
                    self.assertEqual(st["height"], h)
                    self.assertEqual(int(st["nb_read_frames"]), nf)

    def test_non_main_and_malformed_inputs_fail_closed(self):
        in_good = self.dir / "good.yuv"
        in_good.write_bytes(synth_yuv420p(64, 48, 1))
        good_obu = self.dir / "good.obu"
        run(*encode_args(64, 48, in_good, good_obu, 60, "obu"), env=ISO_ENV)
        good_raw = good_obu.read_bytes()

        bad_cases = {
            "empty.obu": b"",
            "junk.obu": b"\xff\xff\xff\xff\x00\x01\x02",
            "trunc_seq.obu": good_raw[:6],
            "trunc_frame.obu": good_raw[: max(18, len(good_raw) // 2)],
        }
        for tag, payload in bad_cases.items():
            p = self.dir / tag
            p.write_bytes(payload)
            self.assertNotEqual(
                run(*decode_args(p, "-"), env=ISO_ENV, check=False).returncode,
                0,
                tag,
            )

        for tag in ("empty.obu", "junk.obu", "trunc_seq.obu"):
            p = self.dir / tag
            self.assertNotEqual(
                run(LFFMPEG, "av1-probe", p, env=ISO_ENV, check=False).returncode,
                0,
                tag,
            )

        in_odd = self.dir / "odd.yuv"
        in_odd.write_bytes(b"\x80" * (63 * 48 * 3 // 2))
        self.assertNotEqual(
            run(*encode_args(63, 48, in_odd, self.dir / "odd.obu"), env=ISO_ENV, check=False).returncode,
            0,
        )

        if not libaom_av1_available():
            return
        src_yuv = self.dir / "neg_src.yuv"
        src_yuv.write_bytes(synth_yuv420p(64, 48, 1))
        for tag, pix_fmt, exp_prof, exp_bd, exp_cs in (
            ("av1_10bit.ivf", "yuv420p10le", 0, 10, "4:2:0"),
            ("av1_444.ivf", "yuv444p", 1, 8, "4:4:4"),
        ):
            neg_path = self.dir / tag
            run(
                FFMPEG, "-y", "-v", "error",
                "-f", "rawvideo", "-pix_fmt", "yuv420p", "-s", "64x48", "-r", "25",
                "-i", src_yuv,
                "-c:v", "libaom-av1", "-cpu-used", "8", "-pix_fmt", pix_fmt,
                "-frames:v", "1", "-f", "ivf", neg_path,
            )
            self.assertNotEqual(
                run(*decode_args(neg_path, "-"), env=ISO_ENV, check=False).returncode,
                0,
                tag,
            )
            probe = json.loads(run(LFFMPEG, "av1-probe", neg_path, env=ISO_ENV).stdout.decode())
            self.assertTrue(probe["ok"])
            self.assertEqual(probe["profile"], exp_prof)
            self.assertEqual(probe["bit_depth"], exp_bd)
            self.assertEqual(probe["chroma_subsampling"], exp_cs)

        mono_path = self.dir / "av1_mono.ivf"
        run(
            FFMPEG, "-y", "-v", "error",
            "-f", "rawvideo", "-pix_fmt", "yuv420p", "-s", "64x48", "-r", "25",
            "-i", src_yuv,
            "-c:v", "libaom-av1", "-cpu-used", "8", "-pix_fmt", "gray",
            "-frames:v", "1", "-f", "ivf", mono_path,
        )
        self.assertNotEqual(
            run(*decode_args(mono_path, "-"), env=ISO_ENV, check=False).returncode,
            0,
            "av1_mono.ivf",
        )
        self.assertNotEqual(
            run(LFFMPEG, "av1-probe", mono_path, env=ISO_ENV, check=False).returncode,
            0,
            "av1_mono.ivf",
        )

        fg_path = self.dir / "film_grain_active.ivf"
        run(
            FFMPEG, "-y", "-v", "error",
            "-f", "rawvideo", "-pix_fmt", "yuv420p", "-s", "64x48", "-r", "25",
            "-i", src_yuv,
            "-c:v", "libaom-av1", "-cpu-used", "8", "-pix_fmt", "yuv420p",
            "-aom-params", "film-grain-test=1",
            "-frames:v", "1", "-f", "ivf", fg_path,
        )
        fg_lean_yuv = self.dir / "film_grain_active.lean.yuv"
        fg_dec = json.loads(run(*decode_args(fg_path, fg_lean_yuv), env=ISO_ENV).stdout.decode())
        self.assertTrue(fg_dec["ok"])
        self.assertEqual(fg_lean_yuv.read_bytes(), self._ffmpeg_decode_yuv420p(fg_path))
        fg_probe = json.loads(run(LFFMPEG, "av1-probe", fg_path, env=ISO_ENV).stdout.decode())
        self.assertTrue(fg_probe["ok"])
        self.assertEqual(fg_probe["frames"], 1)

        if sys.platform != "darwin" and libsvtav1_available():
            scaled_path = self.dir / "scaled_inter_superres.ivf"
            run(
                FFMPEG, "-y", "-v", "error",
                "-f", "lavfi", "-i", "testsrc2=size=128x96:rate=25:duration=0.2",
                "-c:v", "libsvtav1", "-preset", "12", "-pix_fmt", "yuv420p",
                "-svtav1-params", "lp=1:superres-mode=1:superres-denom=12:superres-kf-denom=8",
                "-frames:v", "4", "-f", "ivf", scaled_path,
            )
            self.assertNotEqual(
                run(*decode_args(scaled_path, "-"), env=ISO_ENV, check=False).returncode,
                0,
                "scaled_inter_superres.ivf",
            )
            self.assertNotEqual(
                run(LFFMPEG, "av1-probe", scaled_path, env=ISO_ENV, check=False).returncode,
                0,
                "scaled_inter_superres.ivf",
            )

    def test_embedded_uni_compound_cpu2_fixture(self):
        ivf_path = self.dir / "uni_compound_cpu2_96x80.ivf"
        ivf_path.write_bytes(base64.b64decode(UNI_COMPOUND_CPU2_96X80_IVF_B64))
        lean_yuv = self.dir / "uni_compound_cpu2_96x80.yuv"
        dec_proc = run(*decode_args(ivf_path, lean_yuv), env=ISO_ENV)
        dec_meta = json.loads(dec_proc.stdout.decode())
        self.assertTrue(dec_meta["ok"])
        self.assertEqual(dec_meta["width"], 96)
        self.assertEqual(dec_meta["height"], 80)
        self.assertEqual(dec_meta["frames"], 6)
        lean_bytes = lean_yuv.read_bytes()
        self.assertEqual(len(lean_bytes), 96 * 80 * 3 // 2 * 6)
        self.assertEqual(hashlib.sha256(lean_bytes).hexdigest(), UNI_COMPOUND_CPU2_96X80_YUV_SHA256)
        if libaom_av1_available():
            self.assertEqual(lean_bytes, self._ffmpeg_decode_yuv420p(ivf_path))

    def test_embedded_tmv_and_compound_extended_refmv_fixture(self):
        ivf_path = self.dir / "refmv_compound_uncap_m11_32x32.ivf"
        ivf_path.write_bytes(base64.b64decode(REFMV_COMPOUND_UNCAP_M11_IVF_B64))
        lean_yuv = self.dir / "refmv_compound_uncap_m11_32x32.yuv"
        dec_proc = run(*decode_args(ivf_path, lean_yuv), env=ISO_ENV)
        dec_meta = json.loads(dec_proc.stdout.decode())
        self.assertTrue(dec_meta["ok"])
        self.assertEqual(dec_meta["width"], 32)
        self.assertEqual(dec_meta["height"], 32)
        self.assertEqual(dec_meta["frames"], 5)
        lean_bytes = lean_yuv.read_bytes()
        self.assertEqual(len(lean_bytes), 32 * 32 * 3 // 2 * 5)
        self.assertEqual(hashlib.sha256(lean_bytes).hexdigest(), REFMV_COMPOUND_UNCAP_M11_YUV_SHA256)
        if libaom_av1_available():
            self.assertEqual(lean_bytes, self._ffmpeg_decode_yuv420p(ivf_path))

    def test_strace_zero_child_spawns(self):
        in_path = self.dir / "iso_in.yuv"
        in_path.write_bytes(synth_yuv420p(64, 48, 2))
        bs_path = self.dir / "iso.obu"
        out_yuv = self.dir / "iso_out.yuv"
        run(*encode_args(64, 48, in_path, bs_path, 60, "obu", 1, 1), env=ISO_ENV)
        run(*decode_args(bs_path, out_yuv), env=ISO_ENV)
        run(LFFMPEG, "av1-probe", bs_path, env=ISO_ENV)
        if STRACE is None:
            return
        trace = "".join(["exec", "ve"])
        needle = trace + "("
        for cmd in (
            [STRACE, "-f", "-s", "4096", "-e", "trace=" + trace, LFFMPEG, "av1-probe", bs_path],
            [STRACE, "-f", "-s", "4096", "-e", "trace=" + trace, *encode_args(64, 48, in_path, self.dir / "s.obu")],
            [STRACE, "-f", "-s", "4096", "-e", "trace=" + trace, *decode_args(bs_path, self.dir / "s.yuv")],
        ):
            proc = run(*cmd, env=ISO_ENV)
            spawn_lines = [ln for ln in proc.stderr.decode(errors="replace").splitlines() if needle in ln]
            self.assertEqual(len(spawn_lines), 1, spawn_lines)
            self.assertIn("lffmpeg", spawn_lines[0])

    def _assert_rav1e_4byte_av1c(self, mp4_path, expected_sha=None):
        raw_mp4 = mp4_path.read_bytes()
        av1c_pos = raw_mp4.find(b"av1C")
        self.assertGreaterEqual(av1c_pos, 4)
        av1c_box_sz = int.from_bytes(raw_mp4[av1c_pos - 4:av1c_pos], "big")
        self.assertEqual(av1c_box_sz, 12)
        hdr = bytes(raw_mp4[av1c_pos + 4:av1c_pos + 8])
        self.assertEqual(hdr[0], 0x81)
        self.assertEqual(hdr[2:], b"\x0c\x00")

        probe = json.loads(run(LFFMPEG, "av1-probe", mp4_path, env=ISO_ENV).stdout.decode())
        self.assertTrue(probe["ok"])
        self.assertEqual(probe["container"], "mp4")
        self.assertEqual(probe["profile"], 0)
        self.assertEqual(probe["width"], 128)
        self.assertEqual(probe["height"], 96)
        self.assertEqual(probe["bit_depth"], 8)
        self.assertEqual(probe["chroma_subsampling"], "4:2:0")
        self.assertEqual(probe["frames"], 2)

        lean_yuv = self.dir / f"lean_{mp4_path.name}.yuv"
        dec = json.loads(run(*decode_args(mp4_path, lean_yuv), env=ISO_ENV).stdout.decode())
        self.assertTrue(dec["ok"])
        self.assertEqual(dec["width"], 128)
        self.assertEqual(dec["height"], 96)
        self.assertEqual(dec["frames"], 2)
        lean_bytes = lean_yuv.read_bytes()
        self.assertEqual(len(lean_bytes), 128 * 96 * 3 // 2 * 2)
        if expected_sha is not None:
            self.assertEqual(hashlib.sha256(lean_bytes).hexdigest(), expected_sha)
        if av1_decoder_available():
            self.assertEqual(lean_bytes, self._ffmpeg_decode_yuv420p(mp4_path))

        bad_headers = {
            "bad_marker.mp4": bytes([0x01, 0x1F, 0x0C, 0x00]),
            "bad_profile1.mp4": bytes([0x81, 0x3F, 0x0C, 0x00]),
            "bad_10bit.mp4": bytes([0x81, 0x1F, 0x4C, 0x00]),
            "bad_422.mp4": bytes([0x81, 0x1F, 0x08, 0x00]),
            "bad_mono.mp4": bytes([0x81, 0x1F, 0x1C, 0x00]),
            "bad_reserved_b3.mp4": bytes([0x81, 0x1F, 0x0C, 0x80]),
        }
        for tag, hdr4 in bad_headers.items():
            mutated = bytearray(raw_mp4)
            mutated[av1c_pos + 4:av1c_pos + 8] = hdr4
            bad_path = self.dir / f"{mp4_path.stem}_{tag}"
            bad_path.write_bytes(bytes(mutated))
            self.assertNotEqual(
                run(LFFMPEG, "av1-probe", bad_path, env=ISO_ENV, check=False).returncode,
                0,
                tag,
            )
            self.assertNotEqual(
                run(*decode_args(bad_path, "-"), env=ISO_ENV, check=False).returncode,
                0,
                tag,
            )

    def test_embedded_rav1e_4byte_av1c_fixture(self):
        mp4_path = self.dir / "embedded_rav1e_128x96.mp4"
        mp4_path.write_bytes(base64.b64decode(RAV1E_4BYTE_AV1C_MP4_B64))
        self._assert_rav1e_4byte_av1c(mp4_path, RAV1E_4BYTE_AV1C_YUV_SHA256)

    def test_rav1e_mp4_4byte_av1c_and_unsized_trailing_obu(self):
        if not librav1e_available():
            return
        mp4_path = self.dir / "rav1e_128x96.mp4"
        run(
            FFMPEG, "-y", "-v", "error",
            "-f", "lavfi", "-i", "testsrc2=size=128x96:rate=25:duration=0.08",
            "-frames:v", "2", "-c:v", "librav1e", "-pix_fmt", "yuv420p",
            mp4_path,
        )
        self._assert_rav1e_4byte_av1c(mp4_path)

    def test_multitrack_mp4_audio_video_interleaved_and_fmp4_fail_closed(self):
        if not (libaom_av1_available() and aac_encoder_available()):
            self.skipTest("ffmpeg with libaom-av1 + aac unavailable")
        for tag, map_args in (
            ("video_first.mp4", ["-map", "0:v:0", "-map", "1:a:0"]),
            ("audio_first.mp4", ["-map", "1:a:0", "-map", "0:v:0"]),
        ):
            with self.subTest(case=tag):
                mp4_path = self.dir / tag
                run(
                    FFMPEG, "-y", "-v", "error",
                    "-f", "lavfi", "-i", "testsrc2=size=128x96:rate=25:duration=0.4",
                    "-f", "lavfi", "-i", "sine=frequency=440:sample_rate=48000:duration=0.4",
                    *map_args,
                    "-c:v", "libaom-av1", "-cpu-used", "8", "-pix_fmt", "yuv420p",
                    "-c:a", "aac", "-b:a", "64k", "-shortest",
                    mp4_path,
                )
                ref_yuv = self._ffmpeg_decode_yuv420p(mp4_path)
                expected_frames = len(ref_yuv) // (128 * 96 * 3 // 2)
                self.assertGreater(expected_frames, 0)

                probe = json.loads(run(LFFMPEG, "av1-probe", mp4_path, env=ISO_ENV).stdout.decode())
                self.assertTrue(probe["ok"])
                self.assertEqual(probe["container"], "mp4")
                self.assertEqual(probe["width"], 128)
                self.assertEqual(probe["height"], 96)
                self.assertEqual(probe["frames"], expected_frames)

                lean_yuv = self.dir / f"lean_{tag}.yuv"
                dec = json.loads(run(*decode_args(mp4_path, lean_yuv), env=ISO_ENV).stdout.decode())
                self.assertTrue(dec["ok"])
                self.assertEqual(dec["frames"], expected_frames)
                self.assertEqual(lean_yuv.read_bytes(), ref_yuv)

        fmp4_path = self.dir / "frag_av1.mp4"
        run(
            FFMPEG, "-y", "-v", "error",
            "-f", "lavfi", "-i", "testsrc2=size=128x96:rate=25",
            "-frames:v", "4", "-c:v", "libaom-av1", "-cpu-used", "8", "-pix_fmt", "yuv420p",
            "-movflags", "frag_keyframe+empty_moov+default_base_moof",
            fmp4_path,
        )
        fmp4_boxes = isobmff_box_types(fmp4_path.read_bytes())
        self.assertTrue(b"moof" in fmp4_boxes or b"mvex" in fmp4_boxes)
        self.assertNotEqual(
            run(LFFMPEG, "av1-probe", fmp4_path, env=ISO_ENV, check=False).returncode,
            0,
        )
        self.assertNotEqual(
            run(*decode_args(fmp4_path, "-"), env=ISO_ENV, check=False).returncode,
            0,
        )

    def test_libaom_high_bitdepth_and_subsampling_decode_matrix(self):
        self.assertTrue(libaom_av1_available(), "ffmpeg with libaom-av1 required")
        self.assertTrue(av1_decoder_available(), "ffmpeg AV1 decoder required")
        drv = self._get_raw_driver()
        cases = [
            ("main10_420_ivf", 64, 48, 4, "yuv420p10le", "ivf", ["-cpu-used", "4", "-crf", "28"]),
            ("main10_420_mp4", 64, 48, 3, "yuv420p10le", "mp4", ["-cpu-used", "6", "-crf", "30"]),
            ("main10_420_lossless", 48, 32, 2, "yuv420p10le", "ivf", ["-cpu-used", "8", "-crf", "0", "-aom-params", "lossless=1"]),
            ("high8_444_odd", 47, 35, 3, "yuv444p", "ivf", ["-cpu-used", "6", "-crf", "28"]),
            ("high10_444_ivf", 64, 48, 4, "yuv444p10le", "ivf", ["-cpu-used", "4", "-crf", "28"]),
            ("high10_444_mp4_odd", 53, 39, 3, "yuv444p10le", "mp4", ["-cpu-used", "6", "-crf", "30"]),
            ("high10_444_lossless", 37, 29, 2, "yuv444p10le", "obu", ["-cpu-used", "8", "-crf", "0", "-aom-params", "lossless=1"]),
            ("prof8_422_odd_h", 50, 35, 3, "yuv422p", "ivf", ["-cpu-used", "6", "-crf", "28"]),
            ("prof10_422_ivf", 64, 48, 4, "yuv422p10le", "ivf", ["-cpu-used", "4", "-crf", "28"]),
            ("prof10_422_mp4", 64, 48, 3, "yuv422p10le", "mp4", ["-cpu-used", "6", "-crf", "30"]),
            ("prof12_420_ivf", 64, 48, 3, "yuv420p12le", "ivf", ["-cpu-used", "6", "-crf", "28"]),
            ("prof12_422_ivf", 64, 48, 4, "yuv422p12le", "ivf", ["-cpu-used", "4", "-crf", "28"]),
            ("prof12_422_mp4", 48, 35, 3, "yuv422p12le", "mp4", ["-cpu-used", "6", "-crf", "30"]),
            ("prof12_444_ivf", 53, 39, 3, "yuv444p12le", "ivf", ["-cpu-used", "6", "-crf", "28"]),
            ("prof12_444_lossless", 37, 29, 2, "yuv444p12le", "ivf", ["-cpu-used", "8", "-crf", "0", "-aom-params", "lossless=1"]),
        ]
        for name, w, h, nf, pix_fmt, mux_fmt, aom_opts in cases:
            with self.subTest(case=name):
                exp_prof, exp_bd, _, _, exp_cs = PIX_SPECS[pix_fmt]
                raw_src = synth_raw_planar(w, h, pix_fmt, nf)
                src_path = self.dir / f"{name}.src.raw"
                src_path.write_bytes(raw_src)
                stream_path = self.dir / f"{name}.{mux_fmt}"
                cmd = [
                    FFMPEG, "-y", "-v", "error",
                    "-f", "rawvideo", "-pix_fmt", pix_fmt, "-s", f"{w}x{h}", "-r", "25",
                    "-i", src_path,
                    "-c:v", "libaom-av1", "-pix_fmt", pix_fmt,
                    *aom_opts,
                ]
                if mux_fmt in ("ivf", "obu"):
                    cmd += ["-f", mux_fmt]
                cmd.append(stream_path)
                run(*cmd)

                ref_raw = self._ffmpeg_decode_raw(stream_path, pix_fmt, mux_fmt=mux_fmt)
                lean_out = self.dir / f"{name}.lean.raw"
                dec_res = run(drv, "decode", stream_path, lean_out, env=ISO_ENV)
                parts = dec_res.stdout.decode().strip().split(",")
                self.assertEqual(int(parts[0]), w)
                self.assertEqual(int(parts[1]), h)
                self.assertEqual(int(parts[2]), nf)
                self.assertEqual(int(parts[3]), exp_bd)
                self.assertEqual(parts[4], pix_fmt)
                lean_bytes = lean_out.read_bytes()
                self.assertEqual(lean_bytes, ref_raw)
                if "lossless" in name:
                    self.assertEqual(lean_bytes, raw_src)

                probe = json.loads(run(LFFMPEG, "av1-probe", stream_path, env=ISO_ENV).stdout.decode())
                self.assertTrue(probe["ok"])
                self.assertEqual(probe["profile"], exp_prof)
                self.assertEqual(probe["bit_depth"], exp_bd)
                self.assertEqual(probe["chroma_subsampling"], exp_cs)
                self.assertEqual(probe["width"], w)
                self.assertEqual(probe["height"], h)
                self.assertEqual(probe["frames"], nf)

    def test_libaom_film_grain_apply_grain_bit_exact_matrix(self):
        self.assertTrue(libaom_av1_available(), "ffmpeg with libaom-av1 required")
        self.assertTrue(av1_decoder_available(), "ffmpeg AV1 decoder required")
        drv = self._get_raw_driver()
        cases = [
            ("fg_main8_t1", 64, 48, 3, "yuv420p", "ivf", ["-aom-params", "film-grain-test=1"]),
            ("fg_main8_t3", 80, 64, 3, "yuv420p", "ivf", ["-aom-params", "film-grain-test=3"]),
            ("fg_main8_t11_fullrange", 64, 48, 2, "yuv420p", "mp4", ["-color_range", "pc", "-aom-params", "film-grain-test=11"]),
            ("fg_main10_t2", 80, 64, 4, "yuv420p10le", "ivf", ["-aom-params", "film-grain-test=2"]),
            ("fg_main10_denoise", 64, 48, 4, "yuv420p10le", "mp4", ["-denoise-noise-level", "22"]),
            ("fg_high10_444_t5", 53, 39, 3, "yuv444p10le", "ivf", ["-aom-params", "film-grain-test=5"]),
            ("fg_high10_444_t14", 64, 48, 3, "yuv444p10le", "mp4", ["-color_range", "pc", "-aom-params", "film-grain-test=14"]),
            ("fg_prof10_422_t7", 64, 45, 3, "yuv422p10le", "ivf", ["-aom-params", "film-grain-test=7"]),
            ("fg_prof12_422_t9", 64, 48, 3, "yuv422p12le", "ivf", ["-aom-params", "film-grain-test=9"]),
            ("fg_prof12_444_t16", 51, 37, 3, "yuv444p12le", "ivf", ["-aom-params", "film-grain-test=16"]),
        ]
        for name, w, h, nf, pix_fmt, mux_fmt, fg_opts in cases:
            with self.subTest(case=name):
                _, exp_bd, _, _, _ = PIX_SPECS[pix_fmt]
                raw_src = synth_raw_planar(w, h, pix_fmt, nf)
                src_path = self.dir / f"{name}.src.raw"
                src_path.write_bytes(raw_src)
                stream_path = self.dir / f"{name}.{mux_fmt}"
                cmd = [
                    FFMPEG, "-y", "-v", "error",
                    "-f", "rawvideo", "-pix_fmt", pix_fmt, "-s", f"{w}x{h}", "-r", "25",
                    "-i", src_path,
                    "-c:v", "libaom-av1", "-cpu-used", "6", "-crf", "28", "-pix_fmt", pix_fmt,
                    *fg_opts,
                ]
                if mux_fmt == "ivf":
                    cmd += ["-f", "ivf"]
                cmd.append(stream_path)
                run(*cmd)

                ref_raw = self._ffmpeg_decode_raw(stream_path, pix_fmt, mux_fmt=mux_fmt)
                lean_out = self.dir / f"{name}.lean.raw"
                dec_res = run(drv, "decode", stream_path, lean_out, env=ISO_ENV)
                parts = dec_res.stdout.decode().strip().split(",")
                self.assertEqual(int(parts[0]), w)
                self.assertEqual(int(parts[1]), h)
                self.assertEqual(int(parts[2]), nf)
                self.assertEqual(int(parts[3]), exp_bd)
                self.assertEqual(parts[4], pix_fmt)
                self.assertEqual(lean_out.read_bytes(), ref_raw)

                strict420_out = self.dir / f"{name}.strict420.yuv"
                strict420_res = run(drv, "decode420", stream_path, strict420_out, env=ISO_ENV, check=False)
                if pix_fmt == "yuv420p":
                    self.assertEqual(strict420_res.returncode, 0)
                    self.assertEqual(strict420_out.read_bytes(), ref_raw)
                else:
                    self.assertNotEqual(strict420_res.returncode, 0)

    def test_encode_raw_high_bitdepth_subsampling_and_film_grain_parity(self):
        self.assertTrue(av1_decoder_available(), "ffmpeg AV1 decoder required")
        drv = self._get_raw_driver()
        for pix_fmt, (exp_prof, bd, ss_h, ss_v, exp_cs) in PIX_SPECS.items():
            with self.subTest(pix_fmt=pix_fmt, mode="lossless"):
                w = 37 if ss_h == 0 else 48
                h = 29 if ss_v == 0 else 32
                src_bytes = synth_raw_planar(w, h, pix_fmt, 2)
                src_path = self.dir / f"{pix_fmt}_ll.src.raw"
                enc_path = self.dir / f"{pix_fmt}_ll.ivf"
                lean_dec = self.dir / f"{pix_fmt}_ll.lean.raw"
                src_path.write_bytes(src_bytes)
                run(drv, "encode", w, h, pix_fmt, 0, "ivf", 0, 0, "none", src_path, enc_path, env=ISO_ENV)
                run(drv, "decode", enc_path, lean_dec, env=ISO_ENV)
                ff_bytes = self._ffmpeg_decode_raw(enc_path, pix_fmt, mux_fmt="ivf")
                self.assertEqual(lean_dec.read_bytes(), src_bytes)
                self.assertEqual(ff_bytes, src_bytes)

            with self.subTest(pix_fmt=pix_fmt, mode="lossy_mp4_and_ivf"):
                w, h = 80, 64
                src_bytes = synth_raw_planar(w, h, pix_fmt, 3)
                src_path = self.dir / f"{pix_fmt}_lossy.src.raw"
                ivf_path = self.dir / f"{pix_fmt}_lossy.ivf"
                mp4_path = self.dir / f"{pix_fmt}_lossy.mp4"
                av1c_path = self.dir / f"{pix_fmt}.av1c"
                lean_ivf_dec = self.dir / f"{pix_fmt}_lossy_ivf.lean.raw"
                lean_mp4_dec = self.dir / f"{pix_fmt}_lossy_mp4.lean.raw"
                src_path.write_bytes(src_bytes)

                run(drv, "encode", w, h, pix_fmt, 52, "ivf", 1, 0, "none", src_path, ivf_path, env=ISO_ENV)
                run(drv, "decode", ivf_path, lean_ivf_dec, env=ISO_ENV)
                ff_ivf = self._ffmpeg_decode_raw(ivf_path, pix_fmt, mux_fmt="ivf")
                self.assertEqual(lean_ivf_dec.read_bytes(), ff_ivf)
                self.assertGreater(psnr_raw_db(src_bytes, ff_ivf, bd), 32.0)

                run(drv, "encode", w, h, pix_fmt, 52, "mp4", 0, 0, "none", src_path, mp4_path, env=ISO_ENV)
                run(drv, "decode", mp4_path, lean_mp4_dec, env=ISO_ENV)
                ff_mp4 = self._ffmpeg_decode_raw(mp4_path, pix_fmt, mux_fmt="mp4")
                self.assertEqual(lean_mp4_dec.read_bytes(), ff_mp4)
                self.assertGreater(psnr_raw_db(src_bytes, ff_mp4, bd), 32.0)

                probe = json.loads(run(LFFMPEG, "av1-probe", mp4_path, env=ISO_ENV).stdout.decode())
                self.assertEqual(probe["profile"], exp_prof)
                self.assertEqual(probe["bit_depth"], bd)
                self.assertEqual(probe["chroma_subsampling"], exp_cs)

                pay_res = run(drv, "encode_mp4_payloads", w, h, pix_fmt, 52, src_path, av1c_path, env=ISO_ENV)
                av1c_bytes = av1c_path.read_bytes()
                self.assertGreaterEqual(len(av1c_bytes), 4)
                self.assertEqual(av1c_bytes[0], 0x81)
                self.assertEqual(int(pay_res.stdout.decode().strip().split(",")[1]), 3)

        for pix_fmt in ("yuv420p10le", "yuv444p10le", "yuv422p10le", "yuv422p12le"):
            for fg_mode in ("fg1", "fg_cfl", "fg_reuse"):
                with self.subTest(pix_fmt=pix_fmt, fg_mode=fg_mode):
                    w, h = 64, 48
                    src_bytes = synth_raw_planar(w, h, pix_fmt, 3)
                    src_path = self.dir / f"{pix_fmt}_{fg_mode}.src.raw"
                    no_fg_path = self.dir / f"{pix_fmt}_{fg_mode}_nofg.ivf"
                    fg_path = self.dir / f"{pix_fmt}_{fg_mode}.ivf"
                    no_fg_dec = self.dir / f"{pix_fmt}_{fg_mode}_nofg.lean.raw"
                    fg_dec = self.dir / f"{pix_fmt}_{fg_mode}.lean.raw"
                    src_path.write_bytes(src_bytes)

                    run(drv, "encode", w, h, pix_fmt, 48, "ivf", 0, 0, "none", src_path, no_fg_path, env=ISO_ENV)
                    run(drv, "encode", w, h, pix_fmt, 48, "ivf", 0, 0, fg_mode, src_path, fg_path, env=ISO_ENV)
                    run(drv, "decode", no_fg_path, no_fg_dec, env=ISO_ENV)
                    run(drv, "decode", fg_path, fg_dec, env=ISO_ENV)
                    ff_fg = self._ffmpeg_decode_raw(fg_path, pix_fmt, mux_fmt="ivf")
                    self.assertEqual(fg_dec.read_bytes(), ff_fg)
                    self.assertNotEqual(fg_dec.read_bytes(), no_fg_dec.read_bytes())

        bad_10bit = bytearray(synth_raw_planar(16, 16, "yuv420p10le", 1))
        struct.pack_into("<H", bad_10bit, 0, 1024)
        bad_10bit_path = self.dir / "bad_10bit_sample.raw"
        bad_10bit_path.write_bytes(bytes(bad_10bit))
        self.assertNotEqual(
            run(drv, "encode", 16, 16, "yuv420p10le", 52, "ivf", 0, 0, "none", bad_10bit_path, self.dir / "bad10.ivf", env=ISO_ENV, check=False).returncode,
            0,
        )
        self.assertNotEqual(
            run(drv, "encode", 15, 16, "yuv422p10le", 52, "ivf", 0, 0, "none", bad_10bit_path, self.dir / "bad422w.ivf", env=ISO_ENV, check=False).returncode,
            0,
        )
        self.assertNotEqual(
            run(drv, "encode", 16, 16, "gray10le", 52, "ivf", 0, 0, "none", bad_10bit_path, self.dir / "badfmt.ivf", env=ISO_ENV, check=False).returncode,
            0,
        )


if __name__ == "__main__":
    unittest.main()
