import CurrentAFT.RootLegCoefficientEvaluation
import CurrentAFT.LocalRaisingBounds

/-! Actual higher unselected-leg coefficient cost from the real same-scalar law. -/

namespace CurrentAFT.RootLegCoefficientBounds

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates GradedControlAlgebra
  GradedControlNorm GradedControlStability GradedInverseNorm RootLegCoefficientFamily RootLegCoefficientNorm
  RootLegCoefficientLinear RootTaggedLegHigher CycleRootExpansion BackgroundRates BackgroundLinear
  LocalReferenceEnergy
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw ActualControls.bodyReference rootReference

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

theorem pairBudget_nonneg (security : ℕ) : 0 ≤ pairBudget security := by
  have hmark := markMass_pos security
  unfold pairBudget primaryMaximum
  positivity

theorem rootMass_primary_energy (security : ℕ) (input : Root security → ℝ) :
    primaryMassEnergy security (massLinear security input) ≤
      (32 * pairBudget security) * (rootReference security).l2Sq input := by
  apply (primaryMassEnergy_uniform_le security _).trans
  exact (mul_le_mul_of_nonneg_left (massLinear_uniform_energy security input) (by norm_num : (0 : ℝ) ≤ 8)).trans_eq (by ring)

def normalizedFactor (security : ℕ) : ℝ := primaryFactor security * (8 / activation security)

theorem normalizedFactor_nonneg (security : ℕ) : 0 ≤ normalizedFactor security := by
  unfold normalizedFactor primaryFactor
  have := activation_pos security
  positivity

theorem normalizedFactor_decay (security : ℕ) : normalizedFactor security ≤ 32 / (Parameters.base security : ℝ) ^ 63 := by
  have hb := FirstResponse.base_pos security
  have ha := activation_pos security
  have hinv : 1 / activation security ≤ 4 * (Parameters.base security : ℝ) := by
    have h := one_div_le_one_div_of_le (by positivity : 0 < 1 / (4 * (Parameters.base security : ℝ)))
      (FirstResponse.activation_lower_simple security)
    simpa only [one_div_one_div] using h
  rw [normalizedFactor, primaryFactor_eq]
  calc
    _ = (1 / (Parameters.base security : ℝ) ^ 64) * 8 * (1 / activation security) := by ring
    _ ≤ (1 / (Parameters.base security : ℝ) ^ 64) * 8 * (4 * (Parameters.base security : ℝ)) := by gcongr
    _ = _ := by field_simp; norm_num

theorem normalizedFactor_le_one (security : ℕ) : normalizedFactor security ≤ 1 := by
  apply (normalizedFactor_decay security).trans
  have hb := FirstResponse.base_pos security
  have hpower : (32 : ℝ) ≤ (Parameters.base security : ℝ) ^ 63 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
      (show (2 : ℝ) ≤ (Parameters.base security : ℝ) by exact_mod_cast Parameters.base_ge_two security) 63
    exact (by norm_num : (32 : ℝ) ≤ 2 ^ 63).trans h
  exact (div_le_one (pow_pos hb _)).mpr hpower

theorem selected_rootFamily_norm (security order : ℕ) (input : Root security → ℝ) (selected : Finset (Fin 3)) :
    familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
      (selectedFamily security order (massLinear security input) selected) ≤
        normalizedFactor security ^ selected.card * Real.sqrt (32 * pairBudget security) *
          Real.sqrt ((rootReference security).l2Sq input) := by
  have hpositive : 0 ≤ primaryFactor security := by unfold primaryFactor; positivity
  have h := selectedFamily_norm security order (massLinear security input) selected
    (primaryFactor security) (bodyFactor security) hpositive
  have henergy := Real.sqrt_le_sqrt (rootMass_primary_energy security input)
  rw [Real.sqrt_mul (mul_nonneg (by norm_num) (pairBudget_nonneg security))] at henergy
  apply h.trans
  calc
    _ = normalizedFactor security ^ selected.card *
        Real.sqrt (primaryMassEnergy security (massLinear security input)) := by
      unfold normalizedFactor
      rw [show (8 : ℝ) = 2 * 4 by norm_num]
      simp only [mul_pow, div_pow]
      ring
    _ ≤ normalizedFactor security ^ selected.card *
        (Real.sqrt (32 * pairBudget security) * Real.sqrt ((rootReference security).l2Sq input)) :=
      mul_le_mul_of_nonneg_left henergy (pow_nonneg (normalizedFactor_nonneg security) selected.card)
    _ = _ := by ring

def higherCost (security : ℕ) : ℝ :=
  8 * normalizedFactor security ^ 2 * Real.sqrt (32 * pairBudget security)

theorem rootHigher_norm (security order : ℕ) (input : Root security → ℝ) :
    familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
      (rootHigherLinear security order input) ≤ higherCost security * Real.sqrt ((rootReference security).l2Sq input) := by
  rw [rootHigherLinear_apply]
  unfold rootHigherFamily higherFamily
  have hp : 0 ≤ primaryFactor security := by unfold primaryFactor; positivity
  have hb : 0 ≤ bodyFactor security := by unfold bodyFactor radius; positivity
  apply (familyNorm_sum_le _ _ _ _ _ hp hb _ _).trans
  have hpoint (selected : Finset (Fin 3)) (hselected : selected ∈
      (Finset.univ : Finset (Finset (Fin 3))).filter (fun selected => 2 ≤ selected.card)) :
      familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
        (selectedFamily security order (massLinear security input) selected) ≤
          normalizedFactor security ^ 2 * Real.sqrt (32 * pairBudget security) * Real.sqrt ((rootReference security).l2Sq input) := by
    apply (selected_rootFamily_norm security order input selected).trans
    have hpower := pow_le_pow_of_le_one (normalizedFactor_nonneg security) (normalizedFactor_le_one security)
      (Finset.mem_filter.mp hselected).2
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpower (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  apply (Finset.sum_le_sum hpoint).trans
  have hcard : (((Finset.univ : Finset (Finset (Fin 3))).filter (fun selected => 2 ≤ selected.card)).card : ℝ) ≤ 8 := by
    have h := Finset.card_filter_le (Finset.univ : Finset (Finset (Fin 3))) (fun selected => 2 ≤ selected.card)
    exact_mod_cast (by simpa using h : _ ≤ 8)
  rw [Finset.sum_const, nsmul_eq_mul]
  calc
    _ ≤ 8 * (normalizedFactor security ^ 2 * Real.sqrt (32 * pairBudget security) * Real.sqrt ((rootReference security).l2Sq input)) := by gcongr
    _ = _ := by unfold higherCost; ring

theorem sqrtBudget_polynomial (security : ℕ) :
    Real.sqrt (32 * pairBudget security) ≤ 6 * Real.sqrt LocalRaisingBounds.pairConstant * (Parameters.base security : ℝ) ^ 24 := by
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 32)]
  have hroot : Real.sqrt 32 ≤ (6 : ℝ) := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  exact (mul_le_mul hroot (LocalRaisingBounds.pairBudget_sqrt_polynomial security)
    (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)).trans_eq (by ring)

def higherConstant : ℝ := 49152 * Real.sqrt LocalRaisingBounds.pairConstant

theorem higherCost_decay (security : ℕ) : higherCost security ≤ higherConstant / (Parameters.base security : ℝ) ^ 102 := by
  have hb := FirstResponse.base_pos security
  unfold higherCost
  calc
    _ ≤ 8 * (32 / (Parameters.base security : ℝ) ^ 63) ^ 2 *
        (6 * Real.sqrt LocalRaisingBounds.pairConstant * (Parameters.base security : ℝ) ^ 24) := by
      gcongr
      · exact normalizedFactor_nonneg security
      · exact normalizedFactor_decay security
      · exact sqrtBudget_polynomial security
    _ = _ := by unfold higherConstant; field_simp; ring

end

end CurrentAFT.RootLegCoefficientBounds
