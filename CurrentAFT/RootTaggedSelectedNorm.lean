import CurrentAFT.RootTaggedSelected
import CurrentAFT.CompleteFirstCoefficient

/-! # Joint two-root selected-primary norm budgets from the current laws -/
namespace CurrentAFT.RootTaggedSelectedNorm

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct ControlNorm
  GradedControlAlgebra GradedControlNorm GradedControlStability LocalCoefficientFamily LocalCoefficientNorm
  LocalRaisingNorm LocalRaisingBounds CompleteFirstCoefficient RootTaggedSelected
open Filter
open scoped BigOperators Classical Topology
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
abbrev Palette (security : ℕ) := ActualControls.Palette security

def firstNormConstant : ℝ := 8 * Real.sqrt 2 * Real.sqrt RootTaggedSelected.firstConstant

def selectedConstant : ℝ := 2 * (firstNormConstant + LocalRaisingBounds.higherConstant)

theorem firstNormConstant_nonneg : 0 ≤ firstNormConstant := by unfold firstNormConstant; positivity

theorem selectedConstant_nonneg : 0 ≤ selectedConstant :=
  mul_nonneg (by norm_num) (add_nonneg firstNormConstant_nonneg higherConstant_nonneg)

private theorem primaryFactor_nonneg (security : ℕ) : 0 ≤ BackgroundRates.primaryFactor security := by
  unfold BackgroundRates.primaryFactor
  positivity

private theorem bodyFactor_nonneg (security : ℕ) : 0 ≤ BackgroundRates.bodyFactor security := by
  unfold BackgroundRates.bodyFactor BackgroundRates.radius
  positivity

private theorem base_ge_one (security : ℕ) : (1 : ℝ) ≤ Parameters.base security := by
  exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)

theorem first_energy_sqrt (security : ℕ) (score : RootPair security → Palette security → ℝ)
    (hcentered : ∀ roots, (primaryLaw security).expectation (score roots) = 0) :
    Real.sqrt (BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 4 => LocalReferenceEnergy.uniformReference security)
      (mass security score) 1)) ≤
      Real.sqrt RootTaggedSelected.firstConstant * (Parameters.base security : ℝ) ^ 16 * Real.sqrt (inputEnergy security score) := by
  have hc : 0 ≤ RootTaggedSelected.firstConstant := by unfold RootTaggedSelected.firstConstant; positivity
  have hpower : (Parameters.base security : ℝ) ^ 31 ≤ (Parameters.base security : ℝ) ^ 32 :=
    pow_le_pow_right₀ (base_ge_one security) (by omega)
  have h := (mass_first_energy security score hcentered).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpower hc) (inputEnergy_nonneg security score))
  apply (Real.sqrt_le_sqrt h).trans_eq
  rw [Real.sqrt_mul (mul_nonneg hc (pow_nonneg (FirstResponse.base_pos security).le _)), Real.sqrt_mul hc,
    show (32 : ℕ) = 16 * 2 by omega, pow_mul, Real.sqrt_sq (pow_nonneg (FirstResponse.base_pos security).le _)]

theorem firstFamily_norm (security order : ℕ) (horder : 1 ≤ order)
    (score : RootPair security → Palette security → ℝ)
    (hcentered : ∀ roots, (primaryLaw security).expectation (score roots) = 0) :
    LocalRaisingBounds.coefficientNorm security order (CompleteFirstCoefficient.firstFamily security order horder (mass security score)) ≤
      (firstNormConstant / (Parameters.base security : ℝ) ^ 47) * Real.sqrt (inputEnergy security score) := by
  have hb := FirstResponse.base_pos security
  have ha := activation_pos security
  have hinv : 2 / activation security ≤ 8 * (Parameters.base security : ℝ) := by
    have h := mul_le_mul_of_nonneg_left (FirstResponse.activation_inverse_le security) (show (0 : ℝ) ≤ 2 by norm_num)
    convert h using 1 <;> ring
  have h := CompleteFirstCoefficient.firstFamily_norm security order horder (mass security score)
    (mass_zero security score hcentered) (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security)
    (primaryFactor_nonneg security)
  apply h.trans
  calc
    _ ≤ ((1 / (Parameters.base security : ℝ) ^ 64) * (8 * (Parameters.base security : ℝ)) * Real.sqrt 2) *
        (Real.sqrt RootTaggedSelected.firstConstant * (Parameters.base security : ℝ) ^ 16 * Real.sqrt (inputEnergy security score)) := by
      apply mul_le_mul _ (first_energy_sqrt security score hcentered) (Real.sqrt_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hinv (primaryFactor_nonneg security)) (Real.sqrt_nonneg 2)
          |>.trans_eq (by rw [BackgroundRates.primaryFactor_eq])
    _ = _ := by
      unfold firstNormConstant
      rw [show (64 : ℕ) = 47 + 17 by omega, pow_add, show (17 : ℕ) = 1 + 16 by omega, pow_add, pow_one]
      field_simp [hb.ne']

theorem primaryMass_sqrt (security : ℕ) (score : RootPair security → Palette security → ℝ) :
    Real.sqrt (primaryMassEnergy security (mass security score)) ≤
      Real.sqrt 66048 * Real.sqrt LocalRaisingBounds.pairConstant * (Parameters.base security : ℝ) ^ 24 *
        Real.sqrt (inputEnergy security score) := by
  have hmass : primaryMassEnergy security (mass security score) ≤
      (66048 * LocalReferenceEnergy.pairBudget security) * inputEnergy security score :=
    (primaryMassEnergy_uniform_le security _).trans ((mul_le_mul_of_nonneg_left
      (mass_full_energy security score) (by norm_num : (0 : ℝ) ≤ 16)).trans_eq (by ring))
  calc
    _ ≤ Real.sqrt ((66048 * LocalReferenceEnergy.pairBudget security) * inputEnergy security score) := Real.sqrt_le_sqrt hmass
    _ = Real.sqrt 66048 * Real.sqrt (LocalReferenceEnergy.pairBudget security) * Real.sqrt (inputEnergy security score) := by
      rw [Real.sqrt_mul (mul_nonneg (by norm_num) (PairedReferenceEnergy.pairBudget_nonneg security)),
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 66048)]
    _ ≤ _ := (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pairBudget_sqrt_polynomial security)
      (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)).trans_eq (by ring)

theorem higherFamily_norm (security order : ℕ) (score : RootPair security → Palette security → ℝ) :
    LocalRaisingBounds.coefficientNorm security order (LocalCoefficientFamily.higherFamily security order (mass security score)) ≤
      (LocalRaisingBounds.higherConstant / (Parameters.base security : ℝ) ^ 102) * Real.sqrt (inputEnergy security score) := by
  have hb := FirstResponse.base_pos security
  have h := LocalRaisingNorm.higherFamily_norm security order (mass security score)
    (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security)
    (primaryFactor_nonneg security) (bodyFactor_nonneg security)
  apply h.trans
  apply (mul_le_mul (actual_higherEnvelope security) (primaryMass_sqrt security score) (Real.sqrt_nonneg _)
    (by positivity : (0 : ℝ) ≤ 16384 / (Parameters.base security : ℝ) ^ 126)).trans_eq
  unfold LocalRaisingBounds.higherConstant
  rw [show (126 : ℕ) = 102 + 24 by omega, pow_add]
  field_simp [hb.ne']

theorem completeFamily_norm (security order : ℕ) (horder : 1 ≤ order)
    (score : RootPair security → Palette security → ℝ)
    (hcentered : ∀ roots, (primaryLaw security).expectation (score roots) = 0) :
    LocalRaisingBounds.coefficientNorm security order (NormalizedLocalPolynomial.completeFamily security order (mass security score)) ≤
      ((firstNormConstant + LocalRaisingBounds.higherConstant) / (Parameters.base security : ℝ) ^ 47) *
        Real.sqrt (inputEnergy security score) := by
  rw [complete_eq_first_add_higher security order horder _ (mass_zero security score hcentered)]
  apply (familyNorm_add_le _ _ order _ _ (primaryFactor_nonneg security) (bodyFactor_nonneg security) _ _).trans
  have hpower : (Parameters.base security : ℝ) ^ 47 ≤ (Parameters.base security : ℝ) ^ 102 :=
    pow_le_pow_right₀ (base_ge_one security) (by omega)
  have hdiv := div_le_div_of_nonneg_left higherConstant_nonneg (pow_pos (FirstResponse.base_pos security) 47) hpower
  exact (add_le_add (firstFamily_norm security order horder score hcentered)
    ((higherFamily_norm security order score).trans (mul_le_mul_of_nonneg_right hdiv (Real.sqrt_nonneg _)))).trans_eq (by ring)

/-- A selected paired group consumes the norm of the original joint
root/control input once, even when both body roots carry tags. -/
theorem normalizedResponse_norm (security order : ℕ) (horder : 1 ≤ order)
    (hlarge : 2 * LocalRaisingBounds.positiveConstant ≤ (Parameters.base security : ℝ))
    (score : RootPair security → Palette security → ℝ)
    (hcentered : ∀ roots, (primaryLaw security).expectation (score roots) = 0) :
    LocalRaisingBounds.coefficientNorm security order (normalizedResponse security order score) ≤
      (selectedConstant / (Parameters.base security : ℝ) ^ 47) * Real.sqrt (inputEnergy security score) := by
  have hcomplete := completeFamily_norm security order horder score hcentered
  have hn : 0 ≤ LocalRaisingBounds.coefficientNorm security order
      (NormalizedLocalPolynomial.completeFamily security order (mass security score)) :=
    familyNorm_nonneg _ _ order _ _ (primaryFactor_nonneg security) (bodyFactor_nonneg security) _
  unfold normalizedResponse NormalizedLocalPolynomial.normalizedFamily
  apply (familyNorm_product_le _ _ order _ _ (primaryFactor_nonneg security) (bodyFactor_nonneg security) _ _).trans
  calc
    _ ≤ LocalRaisingBounds.coefficientNorm security order
        (NormalizedLocalPolynomial.completeFamily security order (mass security score)) * 2 :=
      mul_le_mul_of_nonneg_left (LocalRaisingBounds.positiveInverse_bounds security order hlarge).1 hn
    _ ≤ (((firstNormConstant + LocalRaisingBounds.higherConstant) / (Parameters.base security : ℝ) ^ 47) *
        Real.sqrt (inputEnergy security score)) * 2 := mul_le_mul_of_nonneg_right hcomplete (by norm_num)
    _ = _ := by unfold selectedConstant; ring

theorem normalizedResponse_norm_eventually (order : ℕ) (horder : 1 ≤ order) :
    ∀ᶠ security : ℕ in atTop, ∀ score : RootPair security → Palette security → ℝ,
      (∀ roots, (primaryLaw security).expectation (score roots) = 0) →
      LocalRaisingBounds.coefficientNorm security order (normalizedResponse security order score) ≤
        (selectedConstant / (Parameters.base security : ℝ) ^ 47) * Real.sqrt (inputEnergy security score) := by
  obtain ⟨threshold, hthreshold⟩ := exists_nat_ge (2 * LocalRaisingBounds.positiveConstant)
  filter_upwards [eventually_ge_atTop threshold] with security hsecurity score hcentered
  exact normalizedResponse_norm security order horder
    (hthreshold.trans (Nat.cast_le.mpr (show threshold ≤ Parameters.base security by unfold Parameters.base; omega))) score hcentered

end
end CurrentAFT.RootTaggedSelectedNorm
