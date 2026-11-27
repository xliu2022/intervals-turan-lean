#!/usr/bin/env python3
"""Regenerate the library entry point from all committed-style source modules."""

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
print(f"Generated library entry point for {len(modules)} modules.")
