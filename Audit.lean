import CurrentAFT
import Theorem99
import Lean.Util.CollectAxioms

/-! Audit every current declaration and every reused AFT declaration in
the imported environment, including their transitive axiom dependencies. -/

open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  unless environment.contains `CurrentAFT.ActualConstructiveSampler.constructive_gaussian_aft do
    throwError "The complete current constructive theorem is not imported."
  unless environment.contains `CurrentAFT.ActualConstructiveSampler.quantitative_eventually do
    throwError "The current quantitative transport theorem is not imported."
  unless environment.contains `CurrentAFT.ActualAffineEvaluator.polynomial_work do
    throwError "The deterministic affine evaluator is not imported."
  unless environment.contains `CurrentAFT.BinaryPublicBitDecode.current_work do
    throwError "The actual flat-tape decoder is not imported."
  unless environment.contains `Theorem99.theorem_9_9 do
    throwError "Root Theorem 9.9 is not imported."
  unless environment.contains `Theorem99.evaluator_correct_and_polynomial do
    throwError "Root evaluator theorem is not imported."
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checkedRoot := 0
  let mut checkedCurrent := 0
  let mut checkedReused := 0
  let mut state : Lean.CollectAxioms.State := {}
  for (name, _) in environment.constants.toList do
    if (`Theorem99).isPrefixOf name || (`_private.Theorem99).isPrefixOf name ||
        (`CurrentAFT).isPrefixOf name || (`_private.CurrentAFT).isPrefixOf name ||
        (`AFT).isPrefixOf name || (`_private.AFT).isPrefixOf name then
      if (`Theorem99).isPrefixOf name || (`_private.Theorem99).isPrefixOf name then
        checkedRoot := checkedRoot + 1
      else if (`CurrentAFT).isPrefixOf name || (`_private.CurrentAFT).isPrefixOf name then
        checkedCurrent := checkedCurrent + 1
      else
        checkedReused := checkedReused + 1
      let (_, nextState) := ((Lean.CollectAxioms.collect name).run environment).run state
      state := nextState
  for dependency in state.axioms do
    unless allowed.contains dependency do
      throwError "Current AFT declarations depend on unapproved axiom {dependency}"
  if checkedCurrent == 0 then
    throwError "No CurrentAFT declarations imported; the audit is empty."
  logInfo m!"Theorem 9.9 axiom audit passed: {checkedRoot} root, {checkedCurrent} current and {checkedReused} reused declarations. Allowed: propext, Classical.choice, Quot.sound."
