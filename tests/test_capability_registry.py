import json
import os
import stat
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

SCRIPT = Path(__file__).resolve().parents[1] / "scripts" / "generate_capability_registry.py"
sys.path.insert(0, str(SCRIPT.parent))
import generate_capability_registry as registry


class CapabilityRegistryTests(unittest.TestCase):
    def test_positive_and_negative_parsing(self):
        text = """Codecs:\n D..... h264 H.264 / AVC / MPEG-4 AVC / MPEG-4 part 10\n .E.... aac AAC (Advanced Audio Coding)\n ------\n garbage without a table row\n"""
        parsed = registry.parse_listing(text, "codecs")
        self.assertEqual([item["name"] for item in parsed], ["h264", "aac"])
        self.assertTrue(parsed[0]["inventory_only"])
        self.assertEqual(registry.parse_listing("malformed\n--\n", "filters"), [])

    def test_banner_and_configuration_text_are_not_entries(self):
        text = """ffmpeg version 7.0 Copyright (c)\nbuilt with gcc 13.2.0\nconfiguration: --enable-gpl\n"""
        parsed = registry.parse_listing(text, "protocols")
        self.assertEqual([item["name"] for item in parsed], [])

    def test_actual_protocol_bsf_sample_disposition_and_pixel_grammars(self):
        cases = {
            "protocols": "Supported file protocols:\nInput:\n  file\n  pipe\nOutput:\n  http\n",
            "bsfs": "Bitstream filters:\naac_adtstoasc\nextract_extradata\n",
            "sample_fmts": "Sample formats:\nname   depth\nu8        8\ns16      16\n",
            "dispositions": "Dispositions:\ndefault\ndub\nforced\n",
            "pix_fmts": "Pixel formats:\nIO... yuv420p 3 12 8-8-8 8-8-8 1-1\nIO... rgb24   3 24 8-8-8 8-8-8 1-1\n",
        }
        self.assertEqual([item["name"] for item in registry.parse_listing(cases["protocols"], "protocols")], ["file", "pipe", "http"])
        self.assertEqual([item["name"] for item in registry.parse_listing(cases["bsfs"], "bsfs")], ["aac_adtstoasc", "extract_extradata"])
        self.assertEqual([item["name"] for item in registry.parse_listing(cases["sample_fmts"], "sample_fmts")], ["u8", "s16"])
        self.assertEqual([item["name"] for item in registry.parse_listing(cases["dispositions"], "dispositions")], ["default", "dub", "forced"])
        self.assertEqual([item["name"] for item in registry.parse_listing(cases["pix_fmts"], "pix_fmts")], ["yuv420p", "rgb24"])

    def test_unflagged_domains_are_defensive(self):
        parsed = registry.parse_listing("cuda CUDA hardware acceleration\nvaapi\n", "hwaccels")
        self.assertEqual([item["name"] for item in parsed], ["cuda", "vaapi"])

    def test_failed_command_is_not_empty_success(self):
        with mock.patch.object(registry, "run", return_value={"ok": False, "returncode": 1, "stdout": "", "stderr": "bad", "error": "nonzero_exit", "argv": ["ffmpeg", "-codecs"]}):
            result = registry.command_inventory("ffmpeg", "codecs")
        self.assertEqual(result["status"], "failed")
        self.assertFalse(result["complete"])
        self.assertEqual(result["entries"], [])

    def test_successful_empty_listing_is_explicitly_incomplete(self):
        with mock.patch.object(registry, "run", return_value={"ok": True, "returncode": 0, "stdout": "", "stderr": "", "error": None, "argv": ["ffmpeg", "-filters"]}):
            result = registry.command_inventory("ffmpeg", "filters")
        self.assertEqual(result["status"], "empty")
        self.assertFalse(result["complete"])

    def test_mutant_listings_are_marked_incomplete(self):
        listings = {
            "empty": "",
            "corrupted": "Filters:\nnot a filter row\n",
            "misclassified": "Codecs:\n D..... h264 H.264\n",
        }
        for label, listing in listings.items():
            with self.subTest(label=label):
                with mock.patch.object(registry, "run", return_value={"ok": True, "returncode": 0, "stdout": listing, "stderr": "", "error": None, "argv": ["ffmpeg", "-filters"]}):
                    result = registry.command_inventory("ffmpeg", "filters")
                self.assertNotEqual(result["status"], "complete")
                self.assertFalse(result["complete"])
                self.assertEqual(result["entries"], [])

    def test_file_formats_listing_parses_demuxers_and_muxers(self):
        text = """File formats:\n D.  mov QuickTime / MOV\n .E  mp4 MP4 (MPEG-4 Part 14)\n DE  matroska Matroska / WebM\n"""
        self.assertEqual([item["name"] for item in registry.parse_listing(text, "demuxers")], ["mov", "mp4", "matroska"])
        self.assertEqual([item["name"] for item in registry.parse_listing(text, "muxers")], ["mov", "mp4", "matroska"])

    def test_ffmpeg_listings_from_stderr_are_parsed(self):
        with mock.patch.object(registry, "run", return_value={"ok": True, "returncode": 0, "stdout": "", "stderr": "Formats:\n D. = Demuxing supported\n D  mov QuickTime\n", "error": None, "argv": ["ffmpeg", "-formats"]}):
            result = registry.command_inventory("ffmpeg", "formats")
        self.assertEqual(result["status"], "complete")
        self.assertTrue(result["complete"])
        self.assertEqual([item["name"] for item in result["entries"]], ["mov"])

    def test_wrapper_hash_is_not_underlying_binary_hash(self):
        with tempfile.TemporaryDirectory() as directory:
            wrapper = Path(directory) / "ffmpeg-wrapper"
            wrapper.write_text("#!/bin/sh\nexec /bin/true\n", encoding="utf-8")
            wrapper.chmod(wrapper.stat().st_mode | stat.S_IXUSR)
            info = registry.resolve_executable(str(wrapper))
        self.assertEqual(info["kind"], "wrapper")
        self.assertEqual(info["hash_path"], str(wrapper.resolve()))
        self.assertIsNotNone(info["sha256"])

    def test_generator_distinguishes_declared_and_tested(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "registry.json"
            with mock.patch.object(registry, "run", return_value={"ok": True, "returncode": 0, "stdout": " D..... h264 H264\n", "stderr": "", "error": None, "argv": []}):
                with mock.patch.object(registry, "resolve_executable", return_value={"requested": "tool", "resolved": "/tool", "exists": True, "sha256": "hash", "hash_path": "/tool", "kind": "binary"}):
                    self.assertEqual(registry.main(["--ffmpeg", "ffmpeg", "--ffprobe", "ffprobe", "--output", str(output)]), 0)
            data = json.loads(output.read_text(encoding="utf-8"))
        self.assertEqual(data["schema_version"], "1.1")
        self.assertEqual(data["tested_lean_ffmpeg_capabilities"]["status"], "untested")
        self.assertEqual(data["declared_ffmpeg_capabilities"]["codecs"]["entries"][0]["name"], "h264")

    def test_inventory_boundary_validation_requires_all_domains(self):
        registry_data = {
            "declared_ffmpeg_capabilities": {
                domain: {"status": "complete", "complete": True, "entries": [{"name": "x", "inventory_only": True}]}
                for domain in registry.DOMAINS
            }
        }
        self.assertEqual(registry.validate_inventory_boundaries(registry_data), [])
        del registry_data["declared_ffmpeg_capabilities"]["colors"]
        self.assertIn("declared domains do not match DOMAINS", registry.validate_inventory_boundaries(registry_data))

    def test_quorum_contract_blocks_missing_external_reviews(self):
        contract = json.loads((Path(__file__).resolve().parents[1] / "docs" / "contracts" / "quorum-wave-a.json").read_text(encoding="utf-8"))
        reviewers = contract["required_reviewers"]
        self.assertEqual(reviewers, ["fable", "astra", "gemini"])
        self.assertIn(contract["promotion"]["status"], ("blocked_pending_three_model_quorum", "quorum_completed_and_remediated"))
        self.assertTrue(contract["promotion"]["local_review_does_not_substitute"])
        if contract["promotion"]["status"] == "quorum_completed_and_remediated":
            self.assertTrue(all(contract["review_status"][r]["verdict"] in contract["allowed_verdicts"] for r in reviewers))
        else:
            self.assertTrue(all(contract["review_status"][r]["verdict"] is None for r in reviewers))

    def test_platform_qualification_contract_blocks_untested_platforms(self):
        contract = json.loads((Path(__file__).resolve().parents[1] / "docs" / "contracts" / "platform-qualification.json").read_text(encoding="utf-8"))
        self.assertEqual(
            contract["required_platforms"],
            ["linux-x86_64", "macos-arm64", "linux-arm64", "windows-x86_64"],
        )
        self.assertEqual(contract["platforms"]["linux-x86_64"]["status"], "tested_local")
        for platform_id in ("macos-arm64", "linux-arm64", "windows-x86_64"):
            self.assertEqual(contract["platforms"][platform_id]["status"], "untested")
            self.assertEqual(contract["platforms"][platform_id]["verified_gates"], [])
        self.assertEqual(contract["cross_platform_promotion"]["status"], "blocked_pending_untested_platforms_and_quorum")
        self.assertTrue(contract["cross_platform_promotion"]["untested_platforms_never_claimed_supported"])

    def test_cli_requires_explicit_paths(self):
        result = subprocess.run([sys.executable, str(SCRIPT)], capture_output=True, text=True, check=False)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("--ffmpeg", result.stderr)


if __name__ == "__main__":
    unittest.main()
