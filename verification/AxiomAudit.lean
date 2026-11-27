module

import IntervalsTuran
import Lean.Util.CollectAxioms

/-!
Audit every public or private project declaration from a fresh library import.
This is verification tooling, not an added mathematical assumption.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let mut names : Array Name := #[]
  let mut theoremCount : Nat := 0
  for (name, info) in env.constants.toList do
    let text := name.toString
    -- Module provenance also covers vendored AKS declarations that preserve
    -- their upstream namespaces rather than adopting the project namespace.
    let fromProjectModule := match env.getModuleIdxFor? name with
      | some idx => (env.header.moduleNames[idx.toNat]!).toString.startsWith "IntervalsTuran."
      | none => false
    if fromProjectModule || text.startsWith "IntervalsTuran." ||
        text.startsWith "_private.IntervalsTuran." then
      if info.isAxiom then
        throwError "PROJECT AXIOM: {name}"
      if info.isTheorem then
        theoremCount := theoremCount + 1
      names := names.push name
  names := names.qsort Name.lt
  for name in names do
    let axioms ← collectAxioms name
    let unexpected := axioms.filter (fun ax => !allowed.contains ax)
    if !unexpected.isEmpty then
      throwError "UNEXPECTED AXIOMS: {name}: {unexpected.toList}"
    logInfo m!"AUDIT {name}: {axioms.qsort Name.lt |>.toList}"
  logInfo m!"AUDIT PASSED: {names.size} project declarations; {theoremCount} theorems; permitted axioms only: {allowed}"
