#!/usr/bin/env python3
"""Record completed build, axiom audit, exact target check and source hashes."""

from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parent.parent
build = (root / 'verification/full-build.log').read_text()
audit = (root / 'verification/axiom-audit.log').read_text()
scan = (root / 'verification/source-scan.log').read_text()
main = (root / 'verification/unconditional-main.log').read_text()

built = re.search(r'Built (\d+) local Lean modules successfully\.', build)
audited = re.search(r'AUDIT PASSED: (\d+) project declarations; (\d+) theorems;', audit)
scanned = re.search(r'Source scan passed: (\d+) files, (\d+) lines\.', scan)
if not built or not audited or not scanned:
    raise SystemExit('A successful build, full axiom audit and source scan are required.')
if int(built[1]) != int(scanned[1]):
    raise SystemExit('Build and source-scan module counts disagree.')
if 'UNCONDITIONAL MAIN VERIFIED: exact target and ordinary-density expansion' not in main:
    raise SystemExit('The independent unconditional target check is required.')
if 'IntervalsTuran.main_theorem : IntervalsTuran.MainTheoremStatement' not in main:
    raise SystemExit('The parameter-free main theorem type was not found.')
# A declaration such as `tripleSum_le_variance_error:` is an audit entry,
# not a compiler diagnostic. Match Lean's diagnostic prefix and location.
lean_error = re.compile(r'^(?:[^\n]+:\d+:\d+:\s*)?error:', re.MULTILINE)
if any(lean_error.search(log) for log in [build, audit, main]) or 'UNEXPECTED AXIOMS' in audit or 'PROJECT AXIOM:' in audit:
    raise SystemExit('A verification log contains an error.')

manifest = json.loads((root / 'verification/source-manifest.json').read_text())
current_sources = {
    str(path.relative_to(root))
    for path in (root / 'IntervalsTuran').rglob('*.lean')
}
current_sources.add('IntervalsTuran.lean')
recorded_sources = {item['path'] for item in manifest['files']}
if current_sources != recorded_sources or len(manifest['files']) != len(recorded_sources):
    raise SystemExit('The current Lean source set differs from the scanned manifest.')
if len(current_sources) != int(scanned[1]):
    raise SystemExit('The source manifest and scan counts disagree.')
for item in manifest['files']:
    actual = hashlib.sha256((root / item['path']).read_bytes()).hexdigest()
    if actual != item['sha256']:
        raise SystemExit('Source changed after the scan: ' + item['path'])

result = {
    'project': 'Intervals of hypergraph Turan densities',
    'paper': 'https://arxiv.org/abs/2605.25914v1',
    'scope': 'Unconditional formalization of Theorem 1.1, using an alternative MGG-based spectral construction',
    'lean_toolchain': (root / 'lean-toolchain').read_text().strip(),
    'mathlib_revision': '065356127b1dc0016f66b7283ce0ce2c4055aa55',
    'lean_compiler_commit': '11acb17ec6b07a8f9e9173e6845197929540936b',
    'fresh_build': 'passed',
    'build_method': 'Every project module recompiled from source with pinned Lean, using existing pinned dependency caches',
    'modules_built': int(built[1]),
    'transitive_axiom_audit': 'passed',
    'declarations_audited': int(audited[1]),
    'theorem_declarations_including_generated': int(audited[2]),
    'allowed_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
    'source_scan': 'passed',
    'source_files_scanned': int(scanned[1]),
    'source_lines_including_reused_foundations': int(scanned[2]),
    'source_count_note': 'Includes the documented reused foundations and the 12 vendored AKS modules, as well as new proofs.',
    'conditional_main_theorem_compiled': True,
    'conditional_main_theorem': 'IntervalsTuran.main_theorem_of_spectral_existence',
    'conditional_main_type': 'Nonempty IntervalsTuran.Spectral.SmoothSpectralFamily → IntervalsTuran.MainTheoremStatement',
    'unconditional_main_theorem_proved': True,
    'unconditional_main_theorem': 'IntervalsTuran.main_theorem',
    'unconditional_main_type': 'IntervalsTuran.MainTheoremStatement',
    'ordinary_density_expansion': 'IntervalsTuran.ordinary_density_terminal_interval',
    'independent_target_check': 'passed',
    'remaining_obligation': None,
    'remaining_obligation_summary': 'No unresolved mathematical premise in the final main theorem.',
    'proof_route': 'MGG spectral theorem -> sixteen-step permutation multigraph -> simple finite-field bipartite lift -> additive tripartite hypergraph -> exact outer Lagrangians -> recursive interval -> suspension and complete joins',
    'mgg_upstream_repository': 'https://github.com/girving/aks',
    'mgg_upstream_commit': 'c7fb62ed80a4a610f87f34db0082cadbd7c00c9f',
    'mgg_upstream_modules_vendored': 12,
    'mgg_upstream_license': 'Apache-2.0',
    'density_model': 'Ordinary binomial-normalized Turan density for arbitrary forbidden families and globally injective embeddings',
    'nonempty_spectral_family_instance_supplied': False,
    'old_lps_cayley_input_needed_by_unconditional_main': False,
    'old_lps_input_note': 'The degree-138 Cayley-family interface is retained for the historical conditional route. It is not asserted to be inhabited and is not a premise of the completed main theorem.',
    'new_machine_network_dependency_build_performed': False,
    'new_external_submission_or_publication': False,
}
(root / 'verification/result.json').write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
print(json.dumps(result, ensure_ascii=False, indent=2))
