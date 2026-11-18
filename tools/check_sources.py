"""Verify the delivered proof source hashes and local import closure."""
import argparse
import hashlib
import json
import re
from pathlib import Path


def without_comments(text):
    result = []
    index = depth = 0
    while index < len(text):
        if text.startswith('/-', index):
            depth += 1
            index += 2
        elif depth and text.startswith('-/', index):
            depth -= 1
            index += 2
        elif not depth and text.startswith('--', index):
            end = text.find('\n', index)
            index = len(text) if end < 0 else end
        else:
            if not depth or text[index] == '\n':
                result.append(text[index])
            index += 1
    return ''.join(result)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compare-source', type=Path,
                        help='Optional original formalization directory')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    manifest = json.loads((root / 'provenance/local_source_manifest.json').read_text(encoding='utf-8'))
    copied = {row['module']: row for row in manifest['copied_modules']}
    authored = {row['module']: row for row in manifest.get('authored_modules', [])}
    modules = copied | authored
    assert len(modules) == len(copied) + len(authored)
    assert len(copied) == len(manifest['copied_modules'])
    assert len(authored) == len(manifest['authored_modules'])
    sources = {root / 'FourierTensor.lean'}
    for directory in ('FourierTensor', 'support'):
        sources.update((root / directory).rglob('*.lean'))
    assert sources == {root / row['path'] for row in modules.values()}
    for row in modules.values():
        source = root / row['path']
        content = source.read_bytes()
        assert hashlib.sha256(content).hexdigest() == row['sha256'], row['path']
        if args.compare_source and row['module'] in copied:
            original_path = row['source_path'].removeprefix('formalization/')
            assert content == (args.compare_source / original_path).read_bytes(), row['path']
        actual = []
        for match in re.finditer(r'(?m)^\s*(?:public\s+)?import\s+([^\n]+)',
                                 without_comments(content.decode('utf-8-sig'))):
            actual.extend(match.group(1).split())
        assert set(actual) == set(row['local_imports'] + row['external_imports']), row['module']
        assert all(dependency in modules for dependency in row['local_imports']), row['module']
        assert all(dependency == 'Lean' or dependency.startswith('Mathlib.')
                   for dependency in row['external_imports']), row['module']
    for row in manifest['copied_provenance_files']:
        assert hashlib.sha256((root / row['path']).read_bytes()).hexdigest() == row['sha256'], row['path']
    upstream = json.loads((root / 'provenance/upstream_compatibility_manifest.json').read_text(encoding='utf-8'))
    bundle = root / modules['vendor.OpenAIUniformFourierBundle']['path']
    assert hashlib.sha256(bundle.read_bytes()).hexdigest() == upstream['bundle_sha256']

    def closure(entry):
        reached = set()
        pending = [entry]
        while pending:
            module = pending.pop()
            if module not in reached:
                reached.add(module)
                pending.extend(modules[module]['local_imports'])
        return reached

    primary = closure(manifest['root_module'])
    prior = closure(manifest['prior_executor_module'])
    assert len(primary) == manifest['executor_closure_count']
    assert len(prior) == manifest['prior_executor_closure_count']
    assert set(copied) == prior | {manifest['additional_audit_module']}
    assert closure('FourierTensor.Check') == set(modules)
    lake_manifest = json.loads((root / 'lake-manifest.json').read_text(encoding='utf-8'))
    mathlib = next(row for row in lake_manifest['packages'] if row['name'] == 'mathlib')
    assert mathlib['rev'] == mathlib['inputRev'] == manifest['mathlib_revision']
    assert manifest['mathlib_revision'] in (root / 'lakefile.lean').read_text(encoding='utf-8')
    assert (root / 'lean-toolchain').read_text(encoding='utf-8').strip() == manifest['lean_toolchain']
    print(f"PASS: {len(primary)} modules in {manifest['root_module']}, "
          f'{len(modules)} modules in the public checker, '
          f"{len(manifest['copied_provenance_files'])} provenance files, and exact dependency pins")


if __name__ == '__main__':
    main()
