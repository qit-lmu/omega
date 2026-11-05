import Omega
import Lean.Util.CollectAxioms

/-!
Check the transitive axiom dependencies of every declaration in the project's
imported modules, including private helpers and generated declarations.
This is intentionally stronger than searching source text for placeholders.
Run after `lake build` with `lake env lean scripts/Audit.lean`.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let moduleName := env.header.moduleNames[idx]!
    unless (`Omega).isPrefixOf moduleName do continue
    count := count + 1
    for axiomName in ← collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on disallowed axiom {axiomName}"
  if count == 0 then
    throwError "No project declarations were audited; check the root imports."
  logInfo m!"Axiom audit passed for {count} project declarations."
