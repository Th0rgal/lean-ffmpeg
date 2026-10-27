import importlib.util
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

SCRIPTS = Path(__file__).resolve().parents[1] / 'scripts'
sys.path.insert(0, str(SCRIPTS))
import fate_applicability as M


class ApplicabilityTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        for directory in ('tests/fate', 'tests/api', 'tests/checkasm', 'ffbuild', 'libavutil', 'libswscale'):
            (self.root / directory).mkdir(parents=True, exist_ok=True)
        (self.root/'tests/Makefile').write_text('FATE = fate-always\n')
        (self.root/'tests/api/Makefile').write_text('')
        (self.root/'tests/checkasm/Makefile').write_text('')
        (self.root/'ffbuild/config.mak').write_text('CONFIG_ON=yes\n!CONFIG_OFF=yes\n')
        (self.root/'libavutil/pixdesc.c').write_text('[AV_PIX_FMT_GOOD] = { .name = "good", },\n')
        (self.root/'libswscale/format.c').write_text('static const LegacyFormatEntry legacy_format_entries[] = {\n[AV_PIX_FMT_GOOD] = { 1, 1 },\n};\n')
        (self.root/'tests/pixfmts.mak').write_text('PIXFMTS = good\n')

    def manifest(self):
        names = ['fate-always', 'fate-variant'] + [f'fate-unused-{i}' for i in range(6063)]
        rows = [{'name': name, 'configured': name == 'fate-always', 'category': 'unclassified',
                 'applicability': 'upstream-manifest-case', 'pixfmt_universe_only': False,
                 'source_hints': [], 'samples_required': False, 'hardware_required': False}
                for name in names]
        rows += [{**rows[-1], 'name': f'fate-filter-pixdesc-unsupported{i}',
                  'applicability': 'source-overapproximation-not-upstream-test',
                  'pixfmt_universe_only': True} for i in range(68)]
        source_paths = [*M.inventory.transitive_sources(self.root), self.root/'tests/pixfmts.mak',
                        self.root/'libavutil/pixdesc.c', self.root/'libswscale/format.c']
        manifest = {'schema': 'maxwell.ffmpeg.fate-inventory.v3', 'upstream_commit': 'synthetic',
                    'config_sha256': M.sha(self.root/'ffbuild/config.mak'),
                    'source_sha256': {str(p.relative_to(self.root)): M.sha(p) for p in source_paths},
                    'full_manifest_certified': False, 'inventory_count': 6133, 'configured_count': 1,
                    'retained_overapproximation_count': 68, 'tests': rows}
        path = self.root/'manifest.json'
        path.write_text(json.dumps(manifest))
        return path, M.sha(path)

    def test_pins_refuse_manifest_config_source_commit_drift(self):
        for changed in ('manifest', 'config', 'source', 'commit'):
            with self.subTest(changed=changed):
                p, h = self.manifest()
                with patch.object(M.subprocess, 'check_output', return_value='synthetic\n') as git:
                    M.load_pinned(self.root, p, h)
                    if changed == 'manifest':
                        p.write_text(p.read_text() + ' ')
                    elif changed == 'config':
                        (self.root/'ffbuild/config.mak').write_text('CONFIG_CHANGED=yes\n')
                    elif changed == 'source':
                        (self.root/'tests/Makefile').write_text('FATE = fate-changed\n')
                    else:
                        git.return_value = 'different\n'
                    with self.assertRaises(ValueError):
                        M.load_pinned(self.root, p, h)

    def test_symlink_root_is_canonicalized_but_escape_pin_is_rejected(self):
        p, h = self.manifest()
        alias = self.root.parent / (self.root.name + '-alias')
        alias.symlink_to(self.root, target_is_directory=True)
        self.addCleanup(alias.unlink)
        with patch.object(M.subprocess, 'check_output', return_value='synthetic\n'):
            manifest, sources = M.load_pinned(alias, p, h)
        self.assertEqual(manifest['inventory_count'], 6133)
        self.assertTrue(all(path.is_relative_to(self.root.resolve()) for path in sources))
        outside = tempfile.TemporaryDirectory()
        self.addCleanup(outside.cleanup)
        escaped = Path(outside.name) / 'external.mak'
        escaped.write_text('FATE = fate-external\n')
        (self.root/'tests/escape.mak').symlink_to(escaped)
        for relative in ('../escape', 'tests/escape.mak'):
            with self.subTest(relative=relative):
                data = dict(manifest, source_sha256=dict(manifest['source_sha256']))
                data['source_sha256'][relative] = M.sha(escaped)
                p.write_text(json.dumps(data))
                with patch.object(M.subprocess, 'check_output', return_value='synthetic\n'):
                    with self.assertRaisesRegex(ValueError, 'Unsafe source pin path'):
                        M.load_pinned(alias, p, M.sha(p))

    def test_duplicate_and_removed_rows_are_rejected_even_with_new_pin(self):
        for mutation in ('duplicate', 'removed', 'certified'):
            p, _ = self.manifest()
            d = json.loads(p.read_text())
            if mutation == 'duplicate':
                d['tests'][1]['name'] = d['tests'][0]['name']
            elif mutation == 'removed':
                d['tests'].pop()
            else:
                d['full_manifest_certified'] = True
            p.write_text(json.dumps(d))
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                M.load_pinned(self.root, p, M.sha(p))

    def test_direct_unknown_symbol_and_unrecognized_conditional_fail(self):
        for source in ('FATE-$(CONFIG_UNKNOWN) = fate-x\n',
                       'ifnot ($(CONFIG_ON),yes)\nFATE = fate-x\nendif\n',
                       'ifeq $(CONFIG_ON),yes\nendif\n',
                       'ifdef CONFIG_ON\nFATE = fate-x\n',
                       'endif\n'):
            with self.subTest(source=source):
                (self.root/'tests/Makefile').write_text(source)
                with self.assertRaises(ValueError):
                    M.source_evidence(self.root, [self.root/'tests/Makefile'], {'CONFIG_ON': 'yes'})

    def test_dynamic_helper_unknown_symbol_fails_make_expansion(self):
        (self.root/'tests/Makefile').write_text('FATE = fate-always\nFATE += $(if $(call CHKCFG,CONFIG_UNKNOWN),fate-bad)\n')
        with self.assertRaisesRegex(RuntimeError, 'Unknown inventory config'):
            M.inventory.expand(self.root, M.make_flags({'CONFIG_ON': 'yes'}), [], strict_config=True)

    def test_empty_and_malformed_expansions_fail(self):
        for text in ('FATE =\n', 'FATE = fate-bad-%\n'):
            (self.root/'tests/Makefile').write_text(text)
            with self.subTest(text=text), self.assertRaises(ValueError):
                M.inventory.expand(self.root, {}, [], strict_config=True)

    def test_pixfmt_mismatch_and_malformed_generated_list_fail(self):
        self.assertEqual(M.pixels(self.root)[0], ['good'])
        for value in ('PIXFMTS = bad\n', 'PIXFMTS = good good\n',
                      'PIXFMTS = $(shell touch marker)\n', 'OTHER = good\n'):
            (self.root/'tests/pixfmts.mak').write_text(value)
            with self.subTest(value=value), self.assertRaises(ValueError):
                M.pixels(self.root)

    def test_other_and_executable_union_fail_closed(self):
        with self.assertRaisesRegex(ValueError, 'concrete architecture'):
            M.cell_configs({}, architectures=['OTHER'])
        with self.assertRaisesRegex(ValueError, 'Executable'):
            M.build_matrix(self.root, self.root/'absent', '0'*64, mode='executable')
        with self.assertRaises(ValueError):
            M.inventory.expand(self.root, {}, [], hypothetical=True, strict_config=True)

    def test_cells_record_exact_axis_flags_and_single_feature_changes(self):
        base = {k: '' for values in M.ARCHITECTURES.values() for k in values}
        base.update(HAVE_BIGENDIAN='', HAVE_FAST_64BIT='yes', CONFIG_UNSTABLE='',
                    CONFIG_LARGE_TESTS='', HAVE_XMLLINT='')
        cells = M.cell_configs(base, optional=['HAVE_XMLLINT'])
        self.assertEqual(len(cells), 50)
        self.assertEqual(cells[-1]['changes'], {'HAVE_XMLLINT': {'before': '', 'after': 'yes'}})
        for cell in cells[1:-1]:
            arch = cell['axes']['architecture']
            self.assertEqual({k for k, v in cell['flags'].items() if k.startswith('ARCH_') and v}, M.ARCHITECTURES[arch])
            expected = {k for k in base if base[k] != cell['flags'][k]}
            self.assertEqual(set(cell['changes']), expected)

    def test_provenance_keeps_nested_conditions_and_negated_symbols(self):
        (self.root/'tests/Makefile').write_text('''ifdef SAMPLES
ifeq ($(CONFIG_ON),yes)
FATE-$(CONFIG_ON) += fate-on
else
FATE-$(!CONFIG_ON) += fate-off
endif
endif
''')
        rows = M.source_evidence(self.root, [self.root/'tests/Makefile'], {'CONFIG_ON': 'yes'})
        on = next(r for r in rows if r['literal_target_tokens'] == ['fate-on'])
        off = next(r for r in rows if r['literal_target_tokens'] == ['fate-off'])
        self.assertEqual(len(on['enclosing_conditions']), 2)
        self.assertEqual(len(off['enclosing_conditions']), 2)
        self.assertEqual(off['literal_symbols'], ['!CONFIG_ON'])
        self.assertIn('conditional-else', rows[off['enclosing_conditions'][-1]]['forms'])

    def test_no_root_recipe_or_environment_makefile_is_used(self):
        marker = self.root/'marker'
        (self.root/'Makefile').write_text(f'$(shell touch {marker})\nall:; touch {marker}\n')
        with patch.dict(os.environ, {'MAKEFILES': str(self.root/'Makefile'), 'MAKEFLAGS': '-e'}):
            evidence = {}
            groups = M.inventory.expand(self.root, {}, [], strict_config=True, evidence=evidence)
        self.assertEqual(groups['FATE'], {'fate-always'})
        self.assertFalse(marker.exists())

        self.assertEqual(evidence['queried_config_symbols'], [])
        (self.root/'tests/Makefile').write_text(f'FATE := $(shell touch {marker})\n')
        with self.assertRaisesRegex(ValueError, 'Unsafe parse-time'):
            M.source_evidence(self.root, [self.root/'tests/Makefile'], {})
        self.assertFalse(marker.exists())

    def test_inherited_make_environment_cannot_change_cells_or_bypass_strict_queries(self):
        # Match upstream's goal assignment and LARGE_TESTS override. This does
        # not assume bare RUNNING_FATE survives its := assignment upstream.
        controls = """RUNNING_FATE := $(filter check fate%,$(MAKECMDGOALS))
ifneq (,$(RUNNING_FATE))
CHKCFG = yes
endif
ifeq ($(LARGE_TESTS),yes)
CONFIG_LARGE_TESTS := yes
endif
"""
        normal = """FATE_AUX += fate-normal
FATE = $(FATE_AUX) $(if $(call CHKCFG,CONFIG_LARGE_TESTS),fate-large,fate-small)
"""
        (self.root/'tests/Makefile').write_text(controls + normal)
        flags = M.make_flags({'CONFIG_LARGE_TESTS': ''})
        baseline_evidence = {}
        baseline = M.inventory.expand(self.root, flags, [], strict_config=True, evidence=baseline_evidence)
        injected = {'RUNNING_FATE': 'fate', 'LARGE_TESTS': 'yes', 'KEEP': 'yes',
                    'FATE_AUX': 'fate-injected', 'MAKEFLAGS': '-e', 'MFLAGS': '-e',
                    'GNUMAKEFLAGS': '-e', 'MAKEOVERRIDES': 'CONFIG_LARGE_TESTS=yes'}
        with patch.dict(os.environ, injected):
            observed_evidence = {}
            observed = M.inventory.expand(self.root, flags, [], strict_config=True, evidence=observed_evidence)
        self.assertEqual(baseline['FATE'], {'fate-normal', 'fate-small'})
        self.assertEqual(observed, baseline)
        self.assertEqual(observed_evidence, baseline_evidence)
        self.assertEqual(observed_evidence['queried_config_symbols'], ['CONFIG_LARGE_TESTS'])
        (self.root/'tests/Makefile').write_text(controls + 'FATE = $(call CHKCFG,CONFIG_UNKNOWN)\n')
        with patch.dict(os.environ, injected):
            with self.assertRaisesRegex(RuntimeError, 'Unknown inventory config'):
                M.inventory.expand(self.root, flags, [], strict_config=True)

    def test_report_retains_every_row_with_observed_active_disabled_and_memberships(self):
        (self.root/'tests/Makefile').write_text('FATE = fate-always\nFATE += $(if $(CONFIG_OFF),fate-variant)\nFATE_FFMPEG = $(FATE)\n')
        p, h = self.manifest()
        cells = [
            {'id': 'configured', 'kind': 'configured', 'flags': {'CONFIG_ON': 'yes', 'CONFIG_OFF': ''}},
            {'id': 'toggle', 'kind': 'variant', 'flags': {'CONFIG_ON': 'yes', 'CONFIG_OFF': 'yes'}},
        ]
        with patch.object(M.subprocess, 'check_output', return_value='synthetic\n'), patch.object(M, 'cell_configs', return_value=cells):
            report = M.build_matrix(self.root, p, h)
        self.assertEqual(len(report['tests']), 6133)
        self.assertEqual(sum('unsupported-pixdesc-overapprox' in r['statuses'] for r in report['tests']), 68)
        self.assertFalse(report['full_manifest_certified'])
        self.assertFalse(report['condition_model_complete'])
        self.assertFalse(report['recipes_executed'])
        variant = next(r for r in report['tests'] if r['name'] == 'fate-variant')
        self.assertEqual(variant['active_cells'], ['toggle'])
        self.assertEqual(variant['disabled_cells'], ['configured'])
        self.assertEqual(variant['memberships_by_cell']['toggle'], ['FATE', 'FATE_FFMPEG'])
        self.assertEqual(variant['v3_row'], json.loads(p.read_text())['tests'][1])
        self.assertTrue(variant['literal_target_evidence'])


if __name__ == '__main__':
    unittest.main()
