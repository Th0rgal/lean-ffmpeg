#!/usr/bin/env python3
"""Pinned, source-only applicability observations alongside a provisional v3 census.

This is a bounded matrix, not a configure solver or executable/FULL manifest.
GNU make evaluates the pinned source; no build, media, or FATE goal is executed.
"""
import argparse
from collections import Counter
import hashlib
import itertools
import json
from pathlib import Path
import re
import subprocess

import fate_inventory as inventory

ARCHITECTURES = {
    'x86_64': {'ARCH_X86', 'ARCH_X86_64'},
    'x86_32': {'ARCH_X86', 'ARCH_X86_32'},
    'aarch64': {'ARCH_AARCH64'},
    'arm': {'ARCH_ARM'},
    'ppc64': {'ARCH_PPC', 'ARCH_PPC64'},
    'riscv64': {'ARCH_RISCV'},
}
# Deliberately bounded one-feature probes. These are not dependency closures.
OPTIONAL_FEATURES = (
    'HAVE_XMLLINT', 'HAVE_THREADS', 'HAVE_INT128', 'HAVE_X86ASM', 'HAVE_NEON',
    'CONFIG_LIBASTCENC_ENCODER', 'CONFIG_LIBASTCENC_DECODER',
    'CONFIG_CUDA', 'CONFIG_SCALE_CUDA_FILTER', 'CONFIG_AV1_VAAPI_ENCODER',
    'CONFIG_SWSCALE_VULKAN',
)
SYMBOL = re.compile(r'!?\b(?:CONFIG|HAVE|ARCH)_[A-Z0-9_]+')
NAME = re.compile(r'fate-[A-Za-z0-9_.+-]+\Z')
HELPERS = ('ALLYES', 'XYES', 'ENCDEC', 'ENCDEC2', 'DEMDEC', 'ENCMUX',
           'TRANSCODE', 'REMUX', 'FRAMECRC', 'FRAMEMD5', 'CRC', 'PCM',
           'DEMMUX', 'FILTERFRAMECRC', 'FILTERDEMDEC', 'FILTERDEMDECENCMUX',
           'PARSERDEM', 'PARSERDEMDEC')


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load_pinned(root, manifest_path, expected_hash):
    # Canonicalize aliases before checking relative source pins. This preserves
    # containment checks while allowing a symlinked checkout path.
    root = Path(root).resolve()
    require(re.fullmatch(r'[0-9a-f]{64}', expected_hash), 'An explicit manifest SHA-256 is required')
    require(sha(manifest_path) == expected_hash, 'Manifest pin mismatch')
    manifest = json.loads(manifest_path.read_text())
    require(manifest['schema'] == 'maxwell.ffmpeg.fate-inventory.v3', 'Expected pinned v3 inventory')
    require(manifest['full_manifest_certified'] is False, 'Certified/executable union is outside this report')
    rows = manifest['tests']
    require(len(rows) == manifest['inventory_count'] == 6133, 'Expected every one of 6133 v3 rows')
    names = [row['name'] for row in rows]
    require(len(names) == len(set(names)) and all(NAME.fullmatch(n) for n in names), 'Malformed/duplicate manifest target')
    require(sum(row['applicability'] == 'source-overapproximation-not-upstream-test' for row in rows)
            == manifest['retained_overapproximation_count'] == 68, 'Expected all 68 overapproximation rows')
    require(sum(row['configured'] is True for row in rows) == manifest['configured_count'], 'Configured count mismatch')
    require(subprocess.check_output(['git', '-C', str(root), 'rev-parse', 'HEAD'], text=True).strip()
            == manifest['upstream_commit'], 'Upstream commit pin mismatch')
    require(sha(root/'ffbuild/config.mak') == manifest['config_sha256'], 'Config pin mismatch')
    for relative, digest in manifest['source_sha256'].items():
        path = root / relative
        require(not Path(relative).is_absolute() and path.resolve().is_relative_to(root)
                and '..' not in Path(relative).parts, 'Unsafe source pin path')
        require(isinstance(digest, str) and re.fullmatch(r'[0-9a-f]{64}', digest), 'Malformed source digest')
        require(path.is_file() and sha(path) == digest, 'Source pin mismatch: ' + relative)
    sources = inventory.transitive_sources(root)
    require(all(str(p.relative_to(root)) in manifest['source_sha256'] for p in sources),
            'Unpinned transitive source')
    return manifest, sources


def normalized_flags(config):
    raw = inventory.config_flags(config)
    require(raw and all(v == 'yes' for v in raw.values()), 'Expected configure yes/negated-yes flags')
    require(not any(k.startswith('!') and k[1:] in raw for k in raw), 'Contradictory config flags')
    return {k.lstrip('!'): ('' if k.startswith('!') else 'yes') for k in raw}


def logical_lines(text):
    pending, start = '', 0
    for number, line in enumerate(text.splitlines(), 1):
        if not pending:
            start = number
        pending += line
        if pending.endswith('\\'):
            pending = pending[:-1] + ' '
            continue
        yield start, pending
        pending = ''
    require(not pending, 'Dangling make line continuation')


def source_evidence(root, sources, flags):
    """Collect observed syntax, not a claim to solve every make expression.

    Directive structure and literal symbols are checked exhaustively in these
    files. Dynamic helper symbols are checked separately when make queries them.
    Recipes remain inert; their symbols are evidence, not prerequisites here.
    """
    evidence = []
    known = set(flags)
    for path in sources:
        stack = []
        for number, raw in logical_lines(path.read_text()):
            line = raw.strip()
            if not line or line.startswith('#'):
                continue
            # Pin checks happen before this scanner; additionally reject parse-
            # time external effects instead of relying on an inert goal alone.
            require(not re.search(r'\$[({]\s*(?:shell|file)\b', line)
                    and not re.search(r'^[^#\t]*\s!=', raw), 'Unsafe parse-time make operation')
            directive = re.match(r'^(?:(else)\s+)?(ifeq|ifneq|ifdef|ifndef)\b(.*)', line)
            forms = []
            parents = list(stack)
            if directive:
                kind, expression = directive[2], directive[3].strip()
                if kind in ('ifeq', 'ifneq'):
                    require(expression.startswith('(') and expression.endswith(')')
                            and ',' in expression and expression.count('(') == expression.count(')'),
                            'Unrecognized conditional syntax: ' + line)
                else:
                    require(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*', expression),
                            'Unrecognized conditional syntax: ' + line)
                if directive[1]:
                    require(stack, 'Conditional else without if')
                    parents = stack[:-1]
                    stack.pop()
                forms.append('conditional-directive')
            elif re.fullmatch(r'else(?:\s*#.*)?', line):
                require(stack, 'Conditional else without if')
                parents = stack[:-1]
                stack.pop()
                forms.append('conditional-else')
            elif re.fullmatch(r'endif(?:\s*#.*)?', line):
                require(stack, 'Conditional endif without if')
                parents = stack[:-1]
                stack.pop()
                forms.append('conditional-end')
            elif re.match(r'^(?:if\w*|else\w*|endif\w*|elif\w*)\b', line) and '=' not in line:
                raise ValueError('Unrecognized conditional syntax: ' + line)
            symbols = sorted(set(SYMBOL.findall(line)))
            unknown = {s.lstrip('!') for s in symbols} - known
            require(not unknown, 'Unknown config symbols: ' + ', '.join(sorted(unknown)))
            if symbols:
                forms.append('literal-config-symbol')
            for token, label in (('$(if ', 'make-if'), ('$(filter ', 'make-filter'),
                                 ('$(filter-out ', 'make-filter-out'), ('$(eval ', 'make-eval'),
                                 ('-$( ', 'suffix-variable')):
                if token in line:
                    forms.append(label)
            if re.search(r'-\$\(', line):
                forms.append('suffix-variable')
            if any(re.search(r'\$\(call\s+' + h + r'\s*,', line) for h in HELPERS):
                forms.append('config-helper-call')
            dynamic = bool(re.search(r'(?:CONFIG|HAVE|ARCH)_\$|\$\(\$|\$\([1-9]', line))
            if dynamic:
                forms.append('dynamic-expansion')
            targets = sorted(set(re.findall(r'\bfate-[A-Za-z0-9][A-Za-z0-9_.+-]*', line)))
            if forms or targets:
                index = len(evidence)
                evidence.append({'id': index, 'path': str(path.relative_to(root)), 'line': number,
                                 'text': line, 'forms': sorted(set(forms)), 'literal_symbols': symbols,
                                 'variable_references': sorted(set(re.findall(r'\$\(([^()\s,]+)\)', line))),
                                 'enclosing_conditions': parents, 'literal_target_tokens': targets,
                                 'recipe_text': raw.startswith('\t'),
                                 'dynamic_expansion_unmodeled_statically': dynamic})
                if directive or 'conditional-else' in forms:
                    stack.append(index)
        require(not stack, 'Unclosed source conditional: ' + str(path))
    return evidence


def make_flags(positive):
    result = {}
    for key, value in positive.items():
        require(re.fullmatch(r'(?:CONFIG|HAVE|ARCH)_[A-Z0-9_]+|LARGE_TESTS', key), 'Unsafe flag name')
        require(value in ('yes', '', 'no'), 'Unsafe flag value')
        result[key] = value
        if key != 'LARGE_TESTS':
            result['!' + key] = '' if value == 'yes' else 'yes'
    return result


def cell_configs(base, architectures=None, optional=OPTIONAL_FEATURES):
    architectures = tuple(ARCHITECTURES) if architectures is None else architectures
    require(all(a in ARCHITECTURES for a in architectures), 'OTHER/all is not a concrete architecture')
    cells = [{'id': 'configured', 'kind': 'configured-source-expansion', 'flags': dict(base),
              'changes': {}, 'reason': 'Exact pinned configure flags; external samples enabled as a source sentinel'}]
    for arch, endian, unstable, large in itertools.product(architectures, ('little', 'big'), (False, True), (False, True)):
        flags = dict(base)
        require(ARCHITECTURES[arch] <= set(base), 'Missing architecture config symbols')
        flags.update({k: ('yes' if k in ARCHITECTURES[arch] else '') for k in base if k.startswith('ARCH_')})
        flags.update(HAVE_BIGENDIAN='yes' if endian == 'big' else '',
                     HAVE_FAST_64BIT='yes' if arch in ('x86_64', 'aarch64', 'ppc64', 'riscv64') else '',
                     CONFIG_UNSTABLE='yes' if unstable else '', CONFIG_LARGE_TESTS='yes' if large else '')
        require(set(flags) == set(base), 'Unmodeled axis symbol')
        key = f'arch={arch},endian={endian},unstable={int(unstable)},large={int(large)}'
        changes = {k: {'before': base[k], 'after': v} for k, v in flags.items() if base[k] != v}
        cells.append({'id': key, 'kind': 'axis-variant', 'flags': flags, 'changes': changes,
                      'axes': {'architecture': arch, 'endian': endian, 'unstable': unstable, 'large': large},
                      'reason': 'Change named architecture/word-size/endian/unstable/large flags only; other configure flags retained'})
    for feature in optional:
        require(feature in base, 'Unknown optional feature: ' + feature)
        flags = dict(base)
        flags[feature] = '' if base[feature] == 'yes' else 'yes'
        cells.append({'id': 'toggle=' + feature, 'kind': 'one-feature-toggle', 'flags': flags,
                      'changes': {feature: {'before': base[feature], 'after': flags[feature]}},
                      'reason': 'Flip only ' + feature + '; no dependency closure or availability assertion'})
    return cells


def pixels(root):
    descriptors, supported = inventory.pixel_applicability(root)
    generated = (root/'tests/pixfmts.mak').read_text()
    match = re.fullmatch(r'\s*PIXFMTS\s*[:?]?=\s*([a-zA-Z0-9_\s]+)\s*', generated)
    require(match, 'Malformed generated PIXFMTS assignment')
    names = match[1].split()
    require(names and len(names) == len(set(names)) and set(names) == supported,
            'Generated PIXFMTS mismatch against legacy_format_entries')
    return names, descriptors


def build_matrix(root, manifest_path, expected_hash, mode='source-only'):
    require(mode == 'source-only', 'Executable/all-features-union manifests are not supported')
    root = root.resolve()
    require(not any(c.isspace() or c in '#$' for c in str(root)), 'Unsafe make source path')
    manifest, sources = load_pinned(root, manifest_path, expected_hash)
    base = normalized_flags(root/'ffbuild/config.mak')
    evidence = source_evidence(root, sources, base)
    pixel_names, _ = pixels(root)
    cells = cell_configs(base)
    retained = {r['name'] for r in manifest['tests']}
    expansions = {}
    for cell in cells:
        included, queried = {}, {}
        groups = inventory.expand(root, make_flags(cell['flags']), pixel_names,
                                  audit=included, strict_config=True, evidence=queried)
        require(all(manifest['source_sha256'].get(p) == h for p, h in included.items()),
                'Unexpected/mutated source include during expansion')
        require(groups['FATE'] <= retained, 'Expansion contains targets outside pinned census')
        cell.update({'flags_sha256': hashlib.sha256(json.dumps(cell['flags'], sort_keys=True).encode()).hexdigest(),
                     'active_targets': sorted(groups['FATE']), 'active_count': len(groups['FATE']),
                     'queried_config_symbols': queried['queried_config_symbols'],
                     'included_sources': sorted(included), 'recipes_executed': False,
                     'samples_path': '/__fate_samples__', 'samples_available_verified': False,
                     'executable_configuration_verified': False, 'unmodeled_constraints': [
                         'configure dependency consistency and architecture-specific capability closure',
                         'actual sample files, tool/library presence, and hardware/device availability']})
        expansions[cell['id']] = groups
    configured = expansions['configured']['FATE']
    require(configured == {r['name'] for r in manifest['tests'] if r['configured']}, 'Configured membership differs from pinned v3')
    by_target = {}
    by_file = {}
    for item in evidence:
        by_file.setdefault(item['path'], []).append(item['id'])
        for name in item['literal_target_tokens']:
            by_target.setdefault(name, []).append(item['id'])
    rows = []
    for original in manifest['tests']:
        name = original['name']
        active = [c['id'] for c in cells if name in expansions[c['id']]['FATE']]
        memberships = {c['id']: [g for g, names in expansions[c['id']].items() if name in names]
                       for c in cells}
        literal = by_target.get(name, [])
        context = sorted({i for p in original['source_hints'] for i in by_file.get(p, [])})
        direct_symbols = sorted({s for i in literal for s in evidence[i]['literal_symbols']})
        tool_evidence = [i for i in literal if any(s in ('HAVE_XMLLINT',) for s in evidence[i]['literal_symbols'])]
        statuses = ['configured-active' if name in configured else 'variant-only' if active else 'not-observed-in-bounded-cells']
        if original['pixfmt_universe_only']:
            statuses.append('unsupported-pixdesc-overapprox')
        if original['samples_required']:
            statuses.append('sample-required')
        if original['hardware_required']:
            statuses.append('hardware/device-required')
        if tool_evidence:
            statuses.append('external-tool-evidence')
        rows.append({'name': name, 'v3_row': original, 'statuses': statuses,
                     'active_cells': active, 'disabled_cells': [c['id'] for c in cells if c['id'] not in active],
                     'memberships_by_cell': memberships,
                     'literal_target_evidence': literal, 'source_file_context_evidence': context,
                     'direct_literal_config_symbols': direct_symbols,
                     'required_config_symbols_complete': False,
                     'external_tool_evidence': tool_evidence,
                     'config_incompatibility': 'not-assessed; disabled membership is not proof of incompatibility',
                     'provenance_limits': ['literal/source-file links are lexical evidence, not a complete dependency derivation',
                                           'generated names and transitive helper requirements are not attributed exhaustively']})
    # Catch concurrent changes as well as pre-existing drift. Never mutate v3.
    load_pinned(root, manifest_path, expected_hash)
    return {'schema': 'maxwell.ffmpeg.fate-applicability.v1', 'mode': mode,
            'upstream_commit': manifest['upstream_commit'], 'v3_manifest_path': str(manifest_path.resolve()),
            'v3_manifest_sha256': expected_hash, 'config_sha256': manifest['config_sha256'],
            'source_sha256': manifest['source_sha256'],
            'implementation_sha256': {str(p.resolve()): sha(p) for p in (Path(__file__), Path(inventory.__file__))},
            'inventory_count': len(rows), 'retained_overapproximation_count': 68,
            'configured_count': len(configured), 'cell_count': len(cells), 'cells': cells,
            'source_evidence': evidence, 'evidence_form_counts': dict(Counter(f for x in evidence for f in x['forms'])),
            'tests': rows, 'full_manifest_certified': False, 'runnable_matrix_certified': False,
            'condition_model_complete': False, 'recipes_executed': False, 'media_executed': False,
            'unmodeled_conditions': ['not a complete parser/proof for arbitrary GNU make or all configurations',
                                    'symbol queries are observed in bounded cells; short-circuited helper branches may remain unqueried',
                                    'one-feature toggles do not enable prerequisite feature closures',
                                    'lexical per-target evidence is not a complete required-symbol derivation',
                                    'v3 all-feature source-union rows remain retained even when absent from every bounded cell'],
            'claim': 'Provisional source-universe applicability observations only; no FULL, execution, parity, or performance certification'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ffmpeg-root', type=Path, required=True)
    parser.add_argument('--manifest', type=Path, required=True)
    parser.add_argument('--manifest-sha256', required=True)
    parser.add_argument('--mode', choices=['source-only'], default='source-only')
    parser.add_argument('--output', type=Path, required=True, help='Must not exist; each attempt gets a new receipt')
    args = parser.parse_args()
    require(not args.output.exists(), 'Refusing to overwrite an existing receipt')
    result = build_matrix(args.ffmpeg_root, args.manifest, args.manifest_sha256, args.mode)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open('x') as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write('\n')
    print(json.dumps({k: result[k] for k in ('inventory_count', 'retained_overapproximation_count',
                                          'configured_count', 'cell_count', 'full_manifest_certified')}))


if __name__ == '__main__':
    main()
