#!/usr/bin/env python3
"""Check local proof sources and produce a deterministic source manifest.

This is supplementary tooling. The transitive axiom audit is implemented in
verification/AxiomAudit.lean and must also be run through the pinned Lean.
"""

from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parent.parent
sources = sorted((root / 'IntervalsTuran').rglob('*.lean'))
entry = root / 'IntervalsTuran.lean'
if entry.exists():
    sources.append(entry)


def strip_comments_and_strings(text):
    """Lean supports nested block comments; preserve newlines for diagnostics."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif text.startswith('/-', i):
            depth = 1
            i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            out.append(' ')
            i += 1
            while i < len(text):
                if text[i] == '\\':
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    out.append('\n' if text[i] == '\n' else ' ')
                    i += 1
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise ValueError('Unterminated block comment')
    return ''.join(out)


forbidden = re.compile(
    r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern)\b'
    r'|skipKernel|debug\.skip'
)
records, failures = [], []
for source in sources:
    data = source.read_bytes()
    text = data.decode('utf-8')
    code = strip_comments_and_strings(text)
    for match in forbidden.finditer(code):
        line = code.count('\n', 0, match.start()) + 1
        failures.append(f'{source.relative_to(root)}:{line}: {match.group()}')
    records.append({
        'path': str(source.relative_to(root)),
        'sha256': hashlib.sha256(data).hexdigest(),
        'lines': len(text.splitlines()),
    })
if failures:
    raise SystemExit('\n'.join(failures))
(root / 'verification/source-manifest.json').write_text(
    json.dumps({'files': records}, ensure_ascii=False, indent=2) + '\n'
)
print(f'Source scan passed: {len(records)} files, {sum(x["lines"] for x in records)} lines.')
print('No forbidden proof placeholders, custom axioms, native_decide, unsafe or kernel-bypass directives.')
print('This scan is not a proof of the main theorem; run the kernel and inspect its hypotheses.')
