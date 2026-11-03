import CurrentAFT.CurrentFlagArray

/-! Reindexing the literal rational response preserves arbitrary chart arrays. -/

namespace CurrentAFT.CurrentFlagReindex

open AFT AFT.BoundaryCalibration CurrentRationalFlagLaw CurrentFlagIteration
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000

variable {Ω Ω' C I : Type*} [Fintype Ω] [Fintype Ω'] [Fintype C] [Fintype I]

theorem expectation_reindex (e : Ω' ≃ Ω) (profile : Ω → ℚ) :
    expectationQ (profile ∘ e) = expectationQ profile := by
  simp only [expectationQ, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply]
  rw [Fintype.card_congr e, Equiv.sum_comp e profile]

theorem conditional_reindex (e : Ω' ≃ Ω) (feature : Ω → C) (profile : Ω → ℚ) :
    conditionalQ (feature ∘ e) (profile ∘ e) = conditionalQ feature profile := by
  funext color
  change (Fintype.card C : ℚ) * expectationQ
    ((fun x => if feature x = color then profile x else 0) ∘ e) = _
  rw [expectation_reindex]
  rfl

theorem component_reindex (e : Ω' ≃ Ω) (feature : Ω → C) (allowed : Finset C)
    (profile : Ω → ℚ) (point : Ω') :
    featureProjectionQ (feature ∘ e) allowed (profile ∘ e) point =
      featureProjectionQ feature allowed profile (e point) := by
  change centerAllowedQ allowed (conditionalQ (feature ∘ e) (profile ∘ e)) (feature (e point)) = _
  rw [conditional_reindex]
  rfl

theorem projection_reindex (e : Ω' ≃ Ω) (features : I → Ω → C) (allowed : I → Finset C)
    (profile : Ω → ℚ) (point : Ω') :
    projectionQ (fun index => features index ∘ e) allowed (profile ∘ e) point =
      projectionQ features allowed profile (e point) := by
  simp only [projectionQ, LinearMap.coe_mk, AddHom.coe_mk, expectation_reindex, component_reindex]

omit [Fintype Ω] [Fintype Ω'] in
theorem badMask_reindex (e : Ω' ≃ Ω) (safe : Ω → Prop) (profile : Ω → ℚ) :
    badMaskQ (safe ∘ e) (profile ∘ e) = badMaskQ safe profile ∘ e := by
  funext point
  simp only [badMaskQ, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply]

theorem response_reindex (e : Ω' ≃ Ω) (features : I → Ω → C) (allowed : I → Finset C)
    (safe : Ω → Prop) (profile : Ω → ℚ) :
    responseQ (fun index => features index ∘ e) allowed (safe ∘ e) (profile ∘ e) =
      responseQ features allowed safe profile ∘ e := by
  funext point
  simp only [responseQ, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
    Pi.sub_apply, Function.comp_apply]
  rw [badMask_reindex, projection_reindex]

theorem defect_reindex (e : Ω' ≃ Ω) (features : I → Ω → C) (allowed : I → Finset C)
    (line : I → Prop) (spike : Ω → ℚ) :
    offLineDefectQ (fun index => features index ∘ e) allowed line (spike ∘ e) =
      offLineDefectQ features allowed line spike ∘ e := by
  funext point
  simp only [offLineDefectQ, Finset.sum_apply, Function.comp_apply]
  apply Finset.sum_congr rfl
  intro index _
  split_ifs <;> first | rfl | exact component_reindex e _ _ _ _

variable [DecidableEq Ω] [DecidableEq Ω']

theorem iterate_reindex (e : Ω' ≃ Ω) (features : I → Ω → C) (allowed : I → Finset C)
    (safe : Ω → Prop) (target : Ω → ℚ) (steps : ℕ) :
    CurrentFlagIteration.iterate (fun index => features index ∘ e) allowed (safe ∘ e)
        (target ∘ e) steps = CurrentFlagIteration.iterate features allowed safe target steps ∘ e := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    simp only [CurrentFlagIteration.iterate] at ih
    change (target ∘ e) - AFT.RationalNumerics.matrixApply _ _ =
      (target - AFT.RationalNumerics.matrixApply _ _) ∘ e
    rw [CurrentFlagIteration.matrixApply_eq, CurrentFlagIteration.matrixApply_eq, ih, response_reindex]
    rfl

theorem regular_reindex (e : Ω' ≃ Ω) (features : I → Ω → C) (allowed : I → Finset C)
    (line : I → Prop) (safe : Ω → Prop) (atom : ℚ) (spike : Ω → ℚ) (steps : ℕ) :
    regularIterate (fun index => features index ∘ e) allowed line (safe ∘ e) atom (spike ∘ e) steps =
      regularIterate features allowed line safe atom spike steps ∘ e := by
  have ht : (1 - (atom / (1 - atom)) •
      offLineDefectQ (fun index => features index ∘ e) allowed line (spike ∘ e)) =
      (1 - (atom / (1 - atom)) • offLineDefectQ features allowed line spike) ∘ e := by
    rw [defect_reindex]
    rfl
  funext point
  simp only [regularIterate, Function.comp_apply]
  split_ifs
  · rw [ht, iterate_reindex]
    rfl
  · rfl

end
end CurrentAFT.CurrentFlagReindex
