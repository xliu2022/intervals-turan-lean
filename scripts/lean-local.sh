#!/usr/bin/env bash
# Optional helper for a preinstalled Lean and cached dependencies.
# Portable builds should use `lake build`; this helper never builds dependencies.
set -euo pipefail
it_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
it_lean="${INTERVALS_TURAN_LEAN_BIN:-}"
if [[ -z "$it_lean" ]]; then
  if command -v lean >/dev/null 2>&1; then
    it_lean="$(command -v lean)"
  elif [[ -x /workspace/scratch/2f4694a9bf7a/toolchains/lean-4.35.0-rc2-linux/bin/lean ]]; then
    it_lean=/workspace/scratch/2f4694a9bf7a/toolchains/lean-4.35.0-rc2-linux/bin/lean
  else
    echo 'Set INTERVALS_TURAN_LEAN_BIN to the pinned Lean executable.' >&2
    exit 1
  fi
fi
if [[ $# -ne 1 ]]; then
  echo 'Usage: scripts/lean-local.sh <project-relative .lean file>' >&2
  exit 2
fi
it_input="$1"
if [[ "$it_input" == /* ]]; then
  it_input="${it_input#"$it_root"/}"
fi
if [[ "$it_input" == /* || "$it_input" == ../* || "$it_input" != *.lean ]]; then
  echo 'The source file must be inside this project and end in .lean.' >&2
  exit 2
fi
it_packages="${INTERVALS_TURAN_PACKAGE_ROOT:-$it_root/.lake/packages}"
it_lib="$it_root/.lake/build/lib/lean"
it_path="$it_lib"
for it_pkg in "$it_packages"/*; do
  if [[ -d "$it_pkg/.lake/build/lib/lean" ]]; then
    it_path="$it_path:$it_pkg/.lake/build/lib/lean"
  fi
done
export LEAN_PATH="$it_path${LEAN_PATH:+:$LEAN_PATH}"
it_output="$it_lib/${it_input%.lean}"
mkdir -p -- "$(dirname -- "$it_output")"
cd -- "$it_root"
exec "$it_lean" -j "${INTERVALS_TURAN_THREADS:-2}" -R "$it_root" -o "$it_output.olean" -i "$it_output.ilean" "$it_input"
