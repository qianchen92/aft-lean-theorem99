import CurrentAFT.CurrentFlagReindex

/-! Exact color and protected-input coordinate changes for the rational repair. -/

namespace CurrentAFT.CurrentFlagReindex

open AFT AFT.BoundaryCalibration CurrentRationalFlagLaw CurrentFlagIteration
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 200000

variable {Ω C C' I I' : Type*} [Fintype Ω] [Fintype C] [Fintype C'] [Fintype I] [Fintype I']

theorem conditional_color (e : C' ≃ C) (feature : Ω → C) (profile : Ω → ℚ) (color : C') :
    conditionalQ (e.symm ∘ feature) profile color = conditionalQ feature profile (e color) := by
  simp only [conditionalQ, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply]
  rw [Fintype.card_congr e]
  apply congrArg (fun value : ℚ => (Fintype.card C : ℚ) * value)
  apply congrArg expectationQ
  funext point
  have hp : e.symm (feature point) = color ↔ feature point = e color := by
    exact e.symm_apply_eq
  simp only [hp]

theorem component_color (e : C' ≃ C) (feature : Ω → C) (allowed : Finset C)
    (profile : Ω → ℚ) (point : Ω) :
    featureProjectionQ (e.symm ∘ feature) (allowed.map e.symm.toEmbedding) profile point =
      featureProjectionQ feature allowed profile point := by
  have hc : conditionalQ (e.symm ∘ feature) profile = conditionalQ feature profile ∘ e :=
    funext (conditional_color e feature profile)
  have hm : e.symm (feature point) ∈ allowed.map e.symm.toEmbedding ↔ feature point ∈ allowed := by simp
  change (if e.symm (feature point) ∈ allowed.map e.symm.toEmbedding then
    conditionalQ (e.symm ∘ feature) profile (e.symm (feature point)) -
      (∑ color ∈ allowed.map e.symm.toEmbedding, conditionalQ (e.symm ∘ feature) profile color) /
        (allowed.map e.symm.toEmbedding).card else 0) = _
  rw [hc]
  simp only [Finset.card_map, Finset.sum_map, Function.comp_apply, Equiv.toEmbedding_apply,
    Equiv.apply_symm_apply]
  change (if e.symm (feature point) ∈ allowed.map e.symm.toEmbedding then
    conditionalQ feature profile (feature point) -
      (∑ color ∈ allowed, conditionalQ feature profile color) / allowed.card else 0) = _
  simp only [hm]
  rfl

theorem projection_color (e : C' ≃ C) (features : I → Ω → C) (allowed : I → Finset C)
    (profile : Ω → ℚ) (point : Ω) :
    projectionQ (fun index => e.symm ∘ features index) (fun index => (allowed index).map e.symm.toEmbedding)
      profile point = projectionQ features allowed profile point := by
  simp only [projectionQ, LinearMap.coe_mk, AddHom.coe_mk, component_color]

theorem response_color (e : C' ≃ C) (features : I → Ω → C) (allowed : I → Finset C)
    (safe : Ω → Prop) (profile : Ω → ℚ) :
    responseQ (fun index => e.symm ∘ features index) (fun index => (allowed index).map e.symm.toEmbedding)
      safe profile = responseQ features allowed safe profile := by
  funext point
  simp only [responseQ, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
    Pi.sub_apply, projection_color]

theorem defect_color (e : C' ≃ C) (features : I → Ω → C) (allowed : I → Finset C)
    (line : I → Prop) (spike : Ω → ℚ) :
    offLineDefectQ (fun index => e.symm ∘ features index) (fun index => (allowed index).map e.symm.toEmbedding)
      line spike = offLineDefectQ features allowed line spike := by
  funext point
  simp only [offLineDefectQ, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro index _
  split_ifs <;> first | rfl | exact component_color e _ _ _ _

variable [DecidableEq Ω]

private theorem iterate_step (features : I → Ω → C) (allowed : I → Finset C)
    (safe : Ω → Prop) (target : Ω → ℚ) (steps : ℕ) :
    CurrentFlagIteration.iterate features allowed safe target (steps + 1) =
      target - (responseQ features allowed safe (CurrentFlagIteration.iterate features allowed safe target steps) -
        CurrentFlagIteration.iterate features allowed safe target steps) := by
  exact congrArg (fun value => target - value) (CurrentFlagIteration.matrixApply_eq features allowed safe _)

theorem iterate_color (e : C' ≃ C) (features : I → Ω → C) (allowed : I → Finset C)
    (safe : Ω → Prop) (target : Ω → ℚ) (steps : ℕ) :
    CurrentFlagIteration.iterate (fun index => e.symm ∘ features index)
      (fun index => (allowed index).map e.symm.toEmbedding) safe target steps =
      CurrentFlagIteration.iterate features allowed safe target steps := by
  induction steps with
  | zero => simp only [CurrentFlagIteration.iterate, AFT.RationalNumerics.linearIteration]
  | succ steps ih =>
    rw [iterate_step, iterate_step, ih, response_color e features allowed safe _]

theorem regular_color (e : C' ≃ C) (features : I → Ω → C) (allowed : I → Finset C)
    (line : I → Prop) (safe : Ω → Prop) (atom : ℚ) (spike : Ω → ℚ) (steps : ℕ) :
    regularIterate (fun index => e.symm ∘ features index) (fun index => (allowed index).map e.symm.toEmbedding)
      line safe atom spike steps = regularIterate features allowed line safe atom spike steps := by
  funext point
  simp only [regularIterate]
  rw [defect_color e features allowed line spike,
    iterate_color e features allowed safe _ steps]

omit [DecidableEq Ω] in
theorem projection_input (e : I' ≃ I) (features : I → Ω → C) (allowed : I → Finset C)
    (profile : Ω → ℚ) (point : Ω) :
    projectionQ (features ∘ e) (allowed ∘ e) profile point = projectionQ features allowed profile point := by
  simp only [projectionQ, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply]
  rw [Equiv.sum_comp e (fun index => featureProjectionQ (features index) (allowed index) profile point)]

omit [DecidableEq Ω] in
theorem response_input (e : I' ≃ I) (features : I → Ω → C) (allowed : I → Finset C)
    (safe : Ω → Prop) (profile : Ω → ℚ) :
    responseQ (features ∘ e) (allowed ∘ e) safe profile = responseQ features allowed safe profile := by
  funext point
  simp only [responseQ, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
    Pi.sub_apply, projection_input]

omit [DecidableEq Ω] in
theorem defect_input (e : I' ≃ I) (features : I → Ω → C) (allowed : I → Finset C)
    (line : I → Prop) (spike : Ω → ℚ) :
    offLineDefectQ (features ∘ e) (allowed ∘ e) (line ∘ e) spike = offLineDefectQ features allowed line spike := by
  funext point
  simp only [offLineDefectQ, Finset.sum_apply, Function.comp_apply, ite_apply, Pi.zero_apply]
  exact Equiv.sum_comp e (fun index => if line index then 0 else featureProjectionQ (features index) (allowed index) spike point)

theorem iterate_input (e : I' ≃ I) (features : I → Ω → C) (allowed : I → Finset C)
    (safe : Ω → Prop) (target : Ω → ℚ) (steps : ℕ) :
    CurrentFlagIteration.iterate (features ∘ e) (allowed ∘ e) safe target steps =
      CurrentFlagIteration.iterate features allowed safe target steps := by
  induction steps with
  | zero => simp only [CurrentFlagIteration.iterate, AFT.RationalNumerics.linearIteration]
  | succ steps ih =>
    rw [iterate_step, iterate_step, ih, response_input e features allowed safe _]

theorem regular_input (e : I' ≃ I) (features : I → Ω → C) (allowed : I → Finset C)
    (line : I → Prop) (safe : Ω → Prop) (atom : ℚ) (spike : Ω → ℚ) (steps : ℕ) :
    regularIterate (features ∘ e) (allowed ∘ e) (line ∘ e) safe atom spike steps =
      regularIterate features allowed line safe atom spike steps := by
  funext point
  simp only [regularIterate]
  rw [defect_input e features allowed line spike, iterate_input e features allowed safe _ steps]

end
end CurrentAFT.CurrentFlagReindex
