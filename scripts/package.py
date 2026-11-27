#!/usr/bin/env python3
"""Package proof sources and verification evidence without dependency caches."""

from pathlib import Path
import hashlib
import json
import subprocess
import sys
import zipfile

root = Path(__file__).resolve().parent.parent
# Revalidate the current source set, hashes and logs instead of trusting a
# possibly stale successful result from an earlier packaging attempt.
subprocess.run(
    [sys.executable, str(root / 'scripts/record-verification.py')],
    check=True,
    stdout=subprocess.DEVNULL,
)
result = json.loads((root / 'verification/result.json').read_text())
if result.get('fresh_build') != 'passed' or result.get('transitive_axiom_audit') != 'passed':
    raise SystemExit('Finish the fresh build and transitive axiom audit before packaging.')
if not result.get('unconditional_main_theorem_proved') or result.get('independent_target_check') != 'passed':
    raise SystemExit('The unconditional main theorem and exact target check are required.')

output = root.parent / 'intervals_turan_complete_formalization.zip'
files = [root / name for name in [
    'README.md', 'LICENSE', '.gitignore', 'lean-toolchain', 'lakefile.toml',
    'lake-manifest.json', 'IntervalsTuran.lean', 'Challenge.lean',
    'Solution.lean', 'comparator.json', 'formalization.yaml',
    '.github/workflows/verify.yml',
]]
for directory in ['IntervalsTuran', 'scripts', 'docs', 'verification']:
    files.extend(p for p in (root / directory).rglob('*')
                 if p.is_file() and not p.is_symlink()
                 and '__pycache__' not in p.parts
                 and p.suffix not in {'.pyc', '.olean', '.ilean', '.ir'})

with zipfile.ZipFile(output, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
    for path in sorted(set(files)):
        archive.write(path, Path('intervals-turan') / path.relative_to(root))

print(json.dumps({
    'path': str(output),
    'bytes': output.stat().st_size,
    'sha256': hashlib.sha256(output.read_bytes()).hexdigest(),
    'files': len(set(files)),
    'unconditional_main_theorem_proved': result['unconditional_main_theorem_proved'],
}, indent=2))
