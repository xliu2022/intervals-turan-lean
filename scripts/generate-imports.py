#!/usr/bin/env python3
"""Regenerate the public library imports and the full proof-audit imports."""

from pathlib import Path

root = Path(__file__).resolve().parent.parent
modules = sorted(
    ".".join(p.relative_to(root).with_suffix("").parts)
    for p in (root / "IntervalsTuran").rglob("*.lean")
)
documentation = """/-!
# Intervals of hypergraph Turan densities: formalization library

Author and maintainer: Xizhi Liu.

The unconditional main theorem is `IntervalsTuran.main_theorem`. Its proof
uses the checked MGG construction and an actual simple bipartite lift.
The earlier LPS-based conditional lemmas are retained as separate results.
-/

"""
(root / "IntervalsTuran.lean").write_text(
    "module\n\n" + "".join(f"public import {name}\n" for name in modules)
    + "\n" + documentation, encoding="utf-8"
)
audit = root / "verification/AxiomAudit.lean"
lines = audit.read_text(encoding="utf-8").splitlines()
start = lines.index("import all IntervalsTuran")
end = lines.index("", start)
lines[start:end] = [f"import all {name}" for name in ["IntervalsTuran", *modules]]
audit.write_text("\n".join(lines) + "\n", encoding="utf-8")
print(f"Generated public and audit imports for {len(modules)} modules.")
