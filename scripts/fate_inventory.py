#!/usr/bin/env python3
"""Expand upstream FATE with GNU make, retaining disabled cases explicitly.

This is a source-universe census, not an assertion that hypothetical all-feature
configurations are buildable. No FFmpeg build recipes or test binaries run.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

GROUPS = ['FATE', 'FATE_FFMPEG', 'FATE_AVCONV', 'FATE_SAMPLES_AVCONV',
          'FATE_SAMPLES_FFMPEG', 'FATE_FFPROBE', 'FATE_SAMPLES_FFPROBE',
          'FATE_FFMPEG_FFPROBE', 'FATE_SAMPLES_FFMPEG_FFPROBE', 'FATE_EXTERN',
          'FATE_HW-yes', 'FATE_CHECKASM', 'FATE_LIBAVFILTER-yes', 'FATE_LIBAVFORMAT',
          'FATE_SWR_SELFTEST-yes', 'FATE_LIBSWSCALE_SAMPLES', 'FATE_SAMPLES_ENC_RECON-yes',
          'FATE_SAMPLES_DUMP_STREAM_META', 'FATE_WAV_ENCINFO-yes', 'FATE_SCALE_CUDA-yes',
          'FATE_HWCONTEXT', 'FATE_SAMPLES_FASTSTART']


def files(root):
    return [root/'tests/Makefile', root/'tests/api/Makefile',
            root/'tests/checkasm/Makefile', *sorted((root/'tests/fate').glob('*.mak'))]

def transitive_sources(root):
    """Resolve Makefile includes without executing recipes; retain hashes."""
    seen, queue = set(), [root/'tests/Makefile']
    while queue:
        path = queue.pop()
        if path in seen or not path.is_file():
            continue
        seen.add(path)
        text = path.read_text(errors='replace')
        for raw in re.findall(r'^[ \t]*-?include[ \t]+(?:\$\(SRC_PATH\)/)?([^ \t#]+)', text, re.M):
            candidate = root/raw if not raw.startswith('/') else Path(raw)
            if candidate.exists():
                queue.append(candidate)
        if path == root/'tests/Makefile':
            queue.extend(sorted((root/'tests/fate').glob('*.mak')))
            queue.append(root/'tests/api/Makefile')
            queue.append(root/'tests/checkasm/Makefile')
    return sorted(seen)


def pixel_applicability(root):
    """Pin the actual IO table used by upstream `ffmpeg -pix_fmts`.

    This parser supports the pinned upstream representation; syntax changes fail
    closed instead of silently selecting fewer formats.
    """
    desc = (root/'libavutil/pixdesc.c').read_text()
    names = dict(re.findall(r'\[(AV_PIX_FMT_[A-Z0-9_]+)\]\s*=\s*\{\s*\.name\s*=\s*"([^"]+)"', desc))
    text = (root/'libswscale/format.c').read_text()
    table = text.split('static const LegacyFormatEntry legacy_format_entries[] = {', 1)[1].split('\n};', 1)[0]
    if re.search(r'^\s*#', table, re.M):
        raise ValueError('Conditional pixel IO table requires preprocessor applicability review')
    rows = re.findall(r'\[(AV_PIX_FMT_[A-Z0-9_]+)\]\s*=\s*\{\s*([01])\s*,\s*([01])(?:\s*,\s*[01])?\s*}', table)
    if not rows or len(rows) != table.count('[AV_PIX_FMT_'):
        raise ValueError('Unrecognized pixel IO table row; refusing partial applicability')
    if any(enum not in names for enum, _, _ in rows):
        raise ValueError('Pixel IO table references descriptor without a literal name')
    return sorted(names.values()), {names[e] for e, i, o in rows if i == o == '1'}


def conditional_audit(root, included):
    result = []
    for relative in sorted(included):
        for number, line in enumerate((root/relative).read_text().splitlines(), 1):
            if re.match(r'^\s*(?:else\s+)?(ifeq|ifneq|ifdef|ifndef)\b', line):
                result.append({'path': relative, 'line': number, 'condition': line.strip()})
    return result

def config_flags(path):
    flags = {}
    for line in path.read_text().splitlines():
        m = re.fullmatch(r'(!?((?:CONFIG|HAVE|ARCH)_[A-Z0-9_]+))=(.*)', line)
        if m:
            flags[m[1]] = m[3]
    return flags


def expand(root, flags, pixfmts, hypothetical=False, bigendian=False, arch='all', unstable=True, large=True, audit=None):
    """Use only tests/Makefile in an empty cwd; no root/library build rules.

    Goal name is deliberately not fate-list: that goal auto-includes a generated
    pixfmts makefile and may compile ffmpeg even under make -n/-p.
    """
    with tempfile.TemporaryDirectory(prefix='fate-inventory-') as temp:
        temp = Path(temp)
        lines = [f'SRC_PATH := {root}', 'SAMPLES := /__fate_samples__',
                 'TARGET_SAMPLES := $(SAMPLES)', f'TARGET_PATH := {root}',
                 'PIXFMTS := ' + ' '.join(pixfmts), 'CHKCFG = $($(1))']
        if hypothetical:
            keys = {k.lstrip('!') for k in flags}
            # Include direct flag references even if configure omitted them.
            for path in transitive_sources(root):
                keys.update(re.findall(r'\$\(((?:CONFIG|HAVE|ARCH)_[A-Z0-9_]+)\)', path.read_text()))
            lines += [f'{k} := yes' for k in sorted(keys)]
            lines += ['HAVE_BIGENDIAN := ' + ('yes' if bigendian else ''),
                      'LARGE_TESTS := ' + ('yes' if large else 'no'),
                      'CONFIG_UNSTABLE := ' + ('yes' if unstable else '')]
            if arch != 'all':
                lines += [f'{key} := ' + ('yes' if key == 'ARCH_' + arch or (arch == 'X86_64' and key == 'ARCH_X86') else '')
                          for key in sorted(keys | {'ARCH_X86_64','ARCH_AARCH64','ARCH_X86'}) if key.startswith('ARCH_')]
        else:
            lines += [f'{k} := {v}' for k, v in sorted(flags.items())]
        lines += [f'include {root}/tests/Makefile']
        groups = GROUPS + [f'FATE_{x}' for x in ('LIBAVCODEC-yes', 'LIBAVUTIL', 'LIBAVFORMAT-yes',
                    'LIBAVDEVICE-yes', 'LIBSWRESAMPLE-yes', 'LIBSWSCALE', 'API-yes')]
        # Expansion is printed by make itself; no shell interpolation of values.
        lines += [f'$(info INVENTORY|{g}|$(sort $({g})))' for g in groups]
        lines += ['$(info INCLUDED|$(MAKEFILE_LIST))', '.PHONY: inventory', 'inventory:;@:']
        mk = temp/'inventory.mk'
        mk.write_text('\n'.join(lines)+'\n')
        command = ['make', '-rR', '--no-print-directory', '-f', str(mk), 'inventory']
        proc = subprocess.run(command, cwd=temp, text=True, capture_output=True, timeout=30)
        if proc.returncode:
            raise RuntimeError(f'GNU make expansion failed: {proc.stderr}')
        if audit is not None:
            included = next(line.split('|', 1)[1].split() for line in proc.stdout.splitlines() if line.startswith('INCLUDED|'))
            audit.update({str(Path(x).relative_to(root)): hashlib.sha256(Path(x).read_bytes()).hexdigest()
                          for x in included if Path(x).is_relative_to(root)})
        groups_out = {}
        for line in proc.stdout.splitlines():
            if line.startswith('INVENTORY|'):
                _, group, names = line.split('|', 2)
                groups_out[group] = set(names.split())
        if not groups_out.get('FATE'):
            raise ValueError('Empty FATE expansion; refusing empty denominator')
        bad = [n for names in groups_out.values() for n in names if not re.fullmatch(r'fate-[A-Za-z0-9_.+-]+', n)]
        if bad:
            raise ValueError(f'Unexpanded FATE identifiers: {bad[:10]}')
        return groups_out


def classify(name, groups):
    memberships = [g for g, values in groups.items() if name in values]
    if name.startswith('fate-api-'):
        return 'library-api', memberships
    if name in groups.get('FATE_CHECKASM', set()):
        return 'library-checkasm', memberships
    ffmpeg = any(g in memberships for g in ('FATE_FFMPEG', 'FATE_AVCONV', 'FATE_SAMPLES_AVCONV', 'FATE_SAMPLES_FFMPEG'))
    ffprobe = any(g in memberships for g in ('FATE_FFPROBE', 'FATE_SAMPLES_FFPROBE'))
    mixed = any(g in memberships for g in ('FATE_FFMPEG_FFPROBE', 'FATE_SAMPLES_FFMPEG_FFPROBE'))
    if mixed or (ffmpeg and ffprobe):
        return 'cli-mixed', memberships
    if ffmpeg:
        return 'cli-ffmpeg', memberships
    if ffprobe:
        return 'cli-ffprobe', memberships
    if name in groups.get('FATE_SCALE_CUDA-yes', set()):
        return 'cli-ffmpeg', memberships
    if name in groups.get('FATE_SAMPLES_FASTSTART', set()):
        return 'standalone-tool', memberships
    if name == 'fate-source':
        return 'source-check', memberships
    if name == 'fate-hwcontext-cuda':
        return 'library-api', memberships
    if any(g.startswith('FATE_LIB') for g in memberships) or any(g in memberships for g in
            ('FATE_SWR_SELFTEST-yes','FATE_SAMPLES_ENC_RECON-yes','FATE_SAMPLES_DUMP_STREAM_META',
             'FATE_WAV_ENCINFO-yes','FATE_HWCONTEXT')):
        return 'library-api', memberships
    return 'unclassified', memberships


def inventory(root, config, saved_list=None):
    root = root.resolve()
    if any(c.isspace() or c in '#$' for c in str(root)):
        raise ValueError('Source path must not contain make metacharacters or whitespace')
    flags = config_flags(config)
    # Generated pixdesc cases are declared over swscale-supported IO formats.
    # All descriptor names are a conservative source universe, not runnable claims.
    descriptors, supported_pixels = pixel_applicability(root)
    generated = root/'tests/pixfmts.mak'
    configured_pixels = generated.read_text().split('=', 1)[1].split() if generated.exists() else []
    if set(configured_pixels) != supported_pixels:
        raise ValueError('Generated PIXFMTS differs from source IO applicability; review configuration before inventory')
    actual = expand(root, flags, configured_pixels)
    groups = {}
    variants = {}
    source_census = {}
    for endian in (False, True):
        for arch in ('X86_64', 'AARCH64', 'OTHER'):
            for unstable in (False, True):
                for large in (False, True):
                    expanded = expand(root, flags, descriptors, hypothetical=True, bigendian=endian,
                                      arch=arch, unstable=unstable, large=large, audit=source_census)
                    key = f'endian={"big" if endian else "little"},arch={arch},unstable={unstable},large={large}'
                    variants[key] = len(expanded['FATE'])
                    for group, names in expanded.items():
                        groups.setdefault(group, set()).update(names)
    for group, names in actual.items():
        groups.setdefault(group, set()).update(names)
    active = actual['FATE']
    if saved_list:
        saved = set(saved_list.read_text().split())
        if saved != active:
            raise ValueError(f'Saved configured list mismatch: missing={sorted(saved-active)[:5]}, extra={sorted(active-saved)[:5]}')
    hints = {}
    for path in transitive_sources(root):
        text = path.read_text(errors='replace')
        for name in set(re.findall(r'\bfate-[A-Za-z0-9][A-Za-z0-9_.+-]*\b', text)):
            hints.setdefault(name, set()).add(str(path.relative_to(root)))
    tests = []
    for name in sorted(groups['FATE']):
        category, memberships = classify(name, groups)
        tests.append(dict(name=name, category=category, memberships=memberships,
                          configured=name in active, reference_result='not-run', candidate_result='not-run',
                          samples_required=name in groups.get('FATE_EXTERN', set()),
                          hardware_required=name in groups.get('FATE_HW-yes', set()),
                          pixfmt_universe_only=name.startswith('fate-filter-pixdesc-') and name.removeprefix('fate-filter-pixdesc-') not in configured_pixels,
                          source_hints=sorted(hints.get(name, set())),
                          applicability=('source-overapproximation-not-upstream-test'
                              if name.startswith('fate-filter-pixdesc-') and name.removeprefix('fate-filter-pixdesc-') not in supported_pixels
                              else 'upstream-manifest-case')))
    conditions = conditional_audit(root, source_census)
    for rel in ('libswscale/format.c', 'fftools/opt_common.c', 'tests/fate-run.sh'):
        source_census[rel] = hashlib.sha256((root/rel).read_bytes()).hexdigest()
    source_census['libavutil/pixdesc.c'] = hashlib.sha256((root/'libavutil/pixdesc.c').read_bytes()).hexdigest()
    if generated.exists():
        source_census['tests/pixfmts.mak'] = hashlib.sha256(generated.read_bytes()).hexdigest()
    source_census['tests/pixfmts.mak'] = hashlib.sha256(generated.read_bytes()).hexdigest() if generated.exists() else None
    commit = subprocess.check_output(['git','-C',str(root),'rev-parse','HEAD'], text=True).strip()
    return dict(schema='maxwell.ffmpeg.fate-inventory.v3', upstream_commit=commit,
                config_sha256=hashlib.sha256(config.read_bytes()).hexdigest(), source_sha256=source_census,
                inventory_count=len(tests), configured_count=len(active), variants=variants,
                upstream_case_count=sum(t['applicability']=='upstream-manifest-case' for t in tests),
                retained_overapproximation_count=sum(t['applicability']!='upstream-manifest-case' for t in tests),
                conditional_directives=conditions,
                pixel_applicability={'descriptor_count':len(descriptors),'upstream_io_count':len(supported_pixels),
                                     'generated_list_equal':True, 'evidence':'libswscale/format.c legacy_format_entries; fftools/opt_common.c show_pix_fmts'},
                category_counts=dict(Counter(t['category'] for t in tests)),
                full_manifest_certified=False,
                blockers=['All-feature source cases include unavailable libraries/hardware and incompatible configurations; executability is not claimed.',
                          'Conditional directive ledger and 24 architecture/endian/UNSTABLE/LARGE variants require independent completeness review.',
                          'Unsupported PIXFMTS descriptor candidates are retained separately as source overapproximation, not counted as upstream runnable tests.',
                          'Source universe and library/CLI applicability do not certify candidate library implementations or any execution result.' ], tests=tests)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ffmpeg-root', type=Path, required=True)
    parser.add_argument('--config', type=Path)
    parser.add_argument('--configured-list', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    report = inventory(args.ffmpeg_root, args.config or args.ffmpeg_root/'ffbuild/config.mak', args.configured_list)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True)+'\n')
    print(json.dumps({k: report[k] for k in ('inventory_count','configured_count','category_counts','full_manifest_certified')}))

if __name__ == '__main__':
    main()
