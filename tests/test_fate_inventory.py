import importlib.util
from pathlib import Path
import tempfile
import unittest

P = Path(__file__).resolve().parents[1]/'scripts/fate_inventory.py'
S = importlib.util.spec_from_file_location('inventory', P)
M = importlib.util.module_from_spec(S); S.loader.exec_module(M)

class InventoryTests(unittest.TestCase):
    def test_generated_disabled_retained_and_aggregate_excluded(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root/'tests/api').mkdir(parents=True); (root/'tests/fate').mkdir()
            (root/'tests/api/Makefile').write_text('')
            (root/'tests/Makefile').write_text('''NAMES = one two
FATE_X-$(CONFIG_X) += $(NAMES:%=fate-generated-%)
FATE = fate-always $(FATE_X-yes)
fate-group: $(FATE)
# fate-comment-is-not-a-test
''')
            actual=M.expand(root, {'CONFIG_X':''}, [])
            all_features=M.expand(root, {'CONFIG_X':''}, [], hypothetical=True)
            self.assertEqual(actual['FATE'], {'fate-always'})
            self.assertEqual(all_features['FATE'], {'fate-always','fate-generated-one','fate-generated-two'})
            self.assertNotIn('fate-group', all_features['FATE'])
            self.assertNotIn('fate-comment-is-not-a-test', all_features['FATE'])
    def test_configured_helper_resolves_chkcfg_and_preserves_disabled(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp); (root/'tests').mkdir()
            (root/'tests/Makefile').write_text("""ALLYES = $(if $(call CHKCFG,CONFIG_$(1)),yes)
FATE = fate-always $(FATE-yes)
FATE-$(call ALLYES,ON) += fate-on
FATE-$(call ALLYES,OFF) += fate-off
""")
            actual=M.expand(root, {'CONFIG_ON':'yes','CONFIG_OFF':''}, [])
            self.assertEqual(actual['FATE'], {'fate-always','fate-on'})

    def test_transitive_include_hash_changes(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp); (root/'tests/nested').mkdir(parents=True)
            (root/'tests/Makefile').write_text('include $(SRC_PATH)/tests/nested/child.mak\n')
            child=root/'tests/nested/child.mak'; child.write_text('FATE = fate-child\n')
            first={}; second={}
            self.assertEqual(M.expand(root, {}, [], audit=first)['FATE'], {'fate-child'})
            child.write_text('FATE = fate-child-mutant\n')
            self.assertEqual(M.expand(root, {}, [], audit=second)['FATE'], {'fate-child-mutant'})
            self.assertIn('tests/nested/child.mak', first)
            self.assertNotEqual(first['tests/nested/child.mak'], second['tests/nested/child.mak'])

    def test_arch_and_negative_unstable_branches(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp); (root/'tests').mkdir()
            (root/'tests/Makefile').write_text("""FATE = fate-always
ifeq ($(ARCH_X86_64),yes)
FATE += fate-x86
else
FATE += fate-not-x86
endif
ifeq ($(CONFIG_UNSTABLE),yes)
FATE += fate-unstable
else
FATE += fate-stable
endif
ifeq ($(LARGE_TESTS),yes)
FATE += fate-large
endif
""")
            a=M.expand(root, {}, [], hypothetical=True,arch='X86_64',unstable=True,large=True)['FATE']
            b=M.expand(root, {}, [], hypothetical=True,arch='AARCH64',unstable=False,large=False)['FATE']
            self.assertEqual(a, {'fate-always','fate-x86','fate-unstable','fate-large'})
            self.assertEqual(b, {'fate-always','fate-not-x86','fate-stable'})

    def test_pixel_io_table_rejects_unrecognized_rows(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp); (root/'libavutil').mkdir(); (root/'libswscale').mkdir()
            (root/'libavutil/pixdesc.c').write_text('[AV_PIX_FMT_GOOD] = { .name = "good", }, [AV_PIX_FMT_INPUT] = { .name = "input", }')
            p=root/'libswscale/format.c'
            p.write_text('static const LegacyFormatEntry legacy_format_entries[] = {\n[AV_PIX_FMT_GOOD] = { 1, 1 },\n[AV_PIX_FMT_INPUT] = { 1, 0 },\n};')
            self.assertEqual(M.pixel_applicability(root), (['good','input'], {'good'}))
            p.write_text(p.read_text().replace('{ 1, 0 }','{ CONFIG_UNKNOWN, 1 }'))
            with self.assertRaises(ValueError): M.pixel_applicability(root)

    def test_empty_and_unexpanded_rejected(self):
        for assignment in ('FATE =', 'FATE = fate-unexpanded-%'):
            with self.subTest(assignment=assignment), tempfile.TemporaryDirectory() as tmp:
                root=Path(tmp); (root/'tests').mkdir(); (root/'tests/Makefile').write_text(assignment)
                with self.assertRaises(ValueError): M.expand(root, {}, [])
    def test_classification_evidence_not_filename_guess(self):
        groups={'FATE_FFMPEG':{'fate-video','fate-mixed'}, 'FATE_FFPROBE':{'fate-probe','fate-mixed'}}
        self.assertEqual(M.classify('fate-mixed',groups)[0], 'cli-mixed')
        self.assertEqual(M.classify('fate-unknown',groups)[0], 'unclassified')
        self.assertEqual(M.classify('fate-probe',groups)[0], 'cli-ffprobe')

if __name__=='__main__': unittest.main()
