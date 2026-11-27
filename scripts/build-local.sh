#!/usr/bin/env bash
# Optional offline build using existing dependency caches, without modifying them.
set -euo pipefail
ut_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$ut_root"
python3 - "$ut_root" <<'PYBUILD'
from pathlib import Path
import re
import subprocess
import sys
root = Path(sys.argv[1])
sources = list((root / 'IntervalsTuran').rglob('*.lean'))
if (root / 'IntervalsTuran.lean').exists():
    sources.append(root / 'IntervalsTuran.lean')
files = {'.'.join(p.relative_to(root).with_suffix('').parts): p for p in sources}
if not files:
    raise SystemExit('No Lean source files exist yet.')
order, active, done = [], set(), set()
def visit(name):
    if name in done:
        return
    if name in active:
        raise SystemExit('Cyclic local Lean imports at '+name)
    active.add(name)
    source = re.sub(r'/\-.*?\-/', '', files[name].read_text(), flags=re.S)
    for imports in re.findall(r'^\s*(?:(?:public|private)\s+)?import\s+([^\n]+)', source, re.M):
        for dep in imports.split('--',1)[0].split():
            if dep in files:
                visit(dep)
    active.remove(name)
    done.add(name)
    order.append(name)
for name in sorted(files):
    visit(name)
for i, name in enumerate(order, 1):
    rel = files[name].relative_to(root)
    print(f'[{i}/{len(order)}] {name}', flush=True)
    subprocess.run([str(root/'scripts/lean-local.sh'),str(rel)],check=True,cwd=root)
print(f'Built {len(order)} local Lean modules successfully.', flush=True)
PYBUILD
