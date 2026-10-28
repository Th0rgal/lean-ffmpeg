"""-nostats disables progress, not codec diagnostics, including delegated audio."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
CANDIDATE = ROOT / '.lake/build/bin/lffmpeg'
REFERENCE = os.environ.get('LEANAV_FFMPEG_BIN', 'ffmpeg')


class DelegatedDiagnostics(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.source = self.root / 'source.flac'
        subprocess.run([REFERENCE, '-nostdin', '-v', 'error', '-f', 'lavfi',
                        '-i', 'sine=frequency=440:duration=0.1', '-c:a', 'flac',
                        str(self.source)], check=True, capture_output=True)

    def run_audio(self, binary, options, output):
        return subprocess.run([str(binary), '-nostdin', '-y', *options,
                               '-i', str(self.source), '-af', 'hdcd',
                               '-f', 's24le', str(output)], capture_output=True)

    def test_nostats_preserves_hdcd_diagnostic_and_audio(self):
        paths = [self.root / 'reference.raw', self.root / 'candidate.raw']
        for binary, path in zip((REFERENCE, CANDIDATE), paths):
            result = self.run_audio(binary, ['-nostats'], path)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn(b'HDCD detected: no', result.stderr)
            self.assertEqual(result.stdout, b'')
        self.assertEqual(paths[0].read_bytes(), paths[1].read_bytes())

    def test_nostats_preserves_stdout_media_and_stderr_diagnostic(self):
        results = [self.run_audio(binary, ['-nostats'], '-')
                   for binary in (REFERENCE, CANDIDATE)]
        for result in results:
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn(b'HDCD detected: no', result.stderr)
            self.assertTrue(result.stdout)
        self.assertEqual(results[0].stdout, results[1].stdout)

    def test_quiet_and_json_remain_suppressed_with_nostats(self):
        for options in (['-nostats', '-v', 'quiet'], ['-nostats', '-json']):
            with self.subTest(options=options):
                result = self.run_audio(CANDIDATE, options, self.root / 'out.raw')
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stderr, b'')
                if '-json' in options:
                    self.assertTrue(json.loads(result.stdout)['ok'])
                else:
                    self.assertEqual(result.stdout, b'')

    def test_explicit_pipe_protocol_keeps_existing_security_rejection(self):
        result = self.run_audio(CANDIDATE, ['-nostats'], 'pipe:1')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(b'Unsafe protocol', result.stderr)
        self.assertEqual(result.stdout, b'')
