import Lean

/-!
# Checking the axioms a theorem depends on
-/

open Lean Elab Command

/-- Prints the axioms a declaration depends on, and fails unless they are among Lean's standard axioms: no `sorry`,
nothing that trusts compiled code (`native_decide`, `bv_decide`), no axiom of this package. -/
elab "#assert_standard_axioms " id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axioms ← collectAxioms name
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  let others := axioms.filter (!standard.contains ·)
  unless others.isEmpty do
    throwError "{name} depends on axioms other than the standard ones: {others.toList}"
  logInfo m!"{name} depends on axioms: {axioms.toList}"
