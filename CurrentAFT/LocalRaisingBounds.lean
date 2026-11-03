import CurrentAFT.LocalRaisingNorm
import CurrentAFT.IndependentReferenceEnergy

/-!
# Current parameter bounds for the constructed local raising response

All budgets below are derived from the concrete four-output reference law,
its actual primary inverse, and the current two control populations. The
finite inverse is bounded after an explicit fixed-constant threshold. No
local norm estimate, response identity, or invertibility is a premise.
-/
namespace CurrentAFT.LocalRaisingBounds

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct ControlNorm
  GradedControlAlgebra GradedControlNorm GradedControlStability GradedInverse GradedInverseNorm
  LocalCoefficientFamily LocalCoefficientNorm NormalizedLocalPolynomial LocalRaisingFirst LocalRaisingNorm
  BackgroundFamilies LocalReferenceEnergy PairedReferenceEnergy IndependentReferenceEnergy
open Filter
open scoped BigOperators Classical Topology
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
abbrev Palette (security : ℕ) := ActualControls.Palette security

def coefficientNorm (security order : ℕ) (family : Family security order) : ℝ :=
  familyNorm (primaryLaw security) (bodyReference security) order
    (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security) family

def pairConstant : ℝ := 524288 + 17180131328 * Real.exp Real.pi

def higherConstant : ℝ := 16384 * Real.sqrt 66048 * Real.sqrt pairConstant

def positiveConstant : ℝ := 8192 * Real.sqrt pairConstant

def raisingConstant : ℝ := 2 * (higherConstant + positiveConstant)

theorem pairConstant_nonneg : 0 ≤ pairConstant := by unfold pairConstant; positivity

theorem higherConstant_nonneg : 0 ≤ higherConstant := by unfold higherConstant; positivity

theorem positiveConstant_nonneg : 0 ≤ positiveConstant := by unfold positiveConstant; positivity

private theorem primaryFactor_nonneg (security : ℕ) : 0 ≤ BackgroundRates.primaryFactor security := by
  unfold BackgroundRates.primaryFactor
  positivity

private theorem bodyFactor_nonneg (security : ℕ) : 0 ≤ BackgroundRates.bodyFactor security := by
  unfold BackgroundRates.bodyFactor BackgroundRates.radius
  positivity

private theorem base_ge_one (security : ℕ) : (1 : ℝ) ≤ Parameters.base security := by
  exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)

theorem pairBudget_sqrt_polynomial (security : ℕ) :
    Real.sqrt (pairBudget security) ≤ Real.sqrt pairConstant * (Parameters.base security : ℝ) ^ 24 := by
  have hpower : (Parameters.base security : ℝ) ^ 47 ≤ (Parameters.base security : ℝ) ^ 48 :=
    pow_le_pow_right₀ (base_ge_one security) (by omega)
  have hbudget : pairBudget security ≤ pairConstant * (Parameters.base security : ℝ) ^ 48 :=
    (pairBudget_polynomial security).trans (mul_le_mul_of_nonneg_left hpower pairConstant_nonneg)
  apply (Real.sqrt_le_sqrt hbudget).trans_eq
  rw [Real.sqrt_mul pairConstant_nonneg, show (48 : ℕ) = 24 * 2 by omega, pow_mul,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (pow_nonneg (FirstResponse.base_pos security).le _)]

theorem independentSigned_primaryMass_sqrt (security : ℕ) (score : Palette security → ℝ) :
    Real.sqrt (primaryMassEnergy security (IndependentPairedReference.independentSignedMass security score)) ≤
      Real.sqrt 66048 * Real.sqrt pairConstant * (Parameters.base security : ℝ) ^ 24 *
        Real.sqrt ((primaryLaw security).expectation (fun color => score color ^ 2)) := by
  have hinput := (primaryLaw security).l2Sq_nonneg score
  have hmass : primaryMassEnergy security (IndependentPairedReference.independentSignedMass security score) ≤
      (66048 * pairBudget security) * (primaryLaw security).expectation (fun color => score color ^ 2) :=
    (primaryMassEnergy_uniform_le security _).trans ((mul_le_mul_of_nonneg_left
      (independentSigned_energy security score) (by norm_num : (0 : ℝ) ≤ 16)).trans_eq (by ring))
  calc
    _ ≤ Real.sqrt ((66048 * pairBudget security) *
        (primaryLaw security).expectation (fun color => score color ^ 2)) := Real.sqrt_le_sqrt hmass
    _ = Real.sqrt 66048 * Real.sqrt (pairBudget security) *
        Real.sqrt ((primaryLaw security).expectation (fun color => score color ^ 2)) := by
      rw [Real.sqrt_mul (mul_nonneg (by norm_num) (pairBudget_nonneg security)), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 66048)]
    _ ≤ _ := by
      exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pairBudget_sqrt_polynomial security)
        (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)).trans_eq (by ring)

theorem independentHigher_norm (security order : ℕ) (score : Palette security → ℝ) :
    coefficientNorm security order
      (higherFamily security order (IndependentPairedReference.independentSignedMass security score)) ≤
        (higherConstant / (Parameters.base security : ℝ) ^ 102) *
          Real.sqrt ((primaryLaw security).expectation (fun color => score color ^ 2)) := by
  have hb := FirstResponse.base_pos security
  have h := higherFamily_norm security order (IndependentPairedReference.independentSignedMass security score)
    (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security)
    (primaryFactor_nonneg security) (bodyFactor_nonneg security)
  apply h.trans
  apply (mul_le_mul (actual_higherEnvelope security) (independentSigned_primaryMass_sqrt security score)
    (Real.sqrt_nonneg _) (by positivity : (0 : ℝ) ≤ 16384 / (Parameters.base security : ℝ) ^ 126)).trans_eq
  unfold higherConstant
  rw [show (126 : ℕ) = 102 + 24 by omega, pow_add]
  field_simp [hb.ne']

theorem independentPositive_primaryMass_sqrt (security : ℕ) :
    Real.sqrt (primaryMassEnergy security (independentPositiveLaw security).weight) ≤
      16 * Real.sqrt pairConstant * (Parameters.base security : ℝ) ^ 24 := by
  have hmass : primaryMassEnergy security (independentPositiveLaw security).weight ≤ 256 * pairBudget security :=
    (primaryMassEnergy_uniform_le security _).trans ((mul_le_mul_of_nonneg_left
      (independentPositive_energy security) (by norm_num : (0 : ℝ) ≤ 16)).trans_eq (by ring))
  calc
    _ ≤ Real.sqrt (256 * pairBudget security) := Real.sqrt_le_sqrt hmass
    _ = 16 * Real.sqrt (pairBudget security) := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 256)]; norm_num
    _ ≤ _ := (mul_le_mul_of_nonneg_left (pairBudget_sqrt_polynomial security)
      (by norm_num : (0 : ℝ) ≤ 16)).trans_eq (by ring)

theorem independentPositive_defect (security order : ℕ) :
    coefficientNorm security order (positiveFamily security order (independentPositiveLaw security) - 1) ≤
      positiveConstant / (Parameters.base security : ℝ) ^ 39 := by
  have hb := FirstResponse.base_pos security
  have h := positiveFamily_defect_norm security order (independentPositiveLaw security)
    (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security)
    (primaryFactor_nonneg security) (bodyFactor_nonneg security)
  apply h.trans
  apply (mul_le_mul (actual_nonemptyEnvelope security) (independentPositive_primaryMass_sqrt security)
    (Real.sqrt_nonneg _) (by positivity : (0 : ℝ) ≤ 512 / (Parameters.base security : ℝ) ^ 63)).trans_eq
  unfold positiveConstant
  rw [show (63 : ℕ) = 39 + 24 by omega, pow_add]
  field_simp [hb.ne']
  ring

def positiveInverse (security order : ℕ) : Family security order :=
  backgroundInverse (primaryLaw security) (bodyReference security) order
    (positiveFamily security order (independentPositiveLaw security))

theorem positiveInverse_bounds (security order : ℕ)
    (hlarge : 2 * positiveConstant ≤ (Parameters.base security : ℝ)) :
    coefficientNorm security order (positiveInverse security order) ≤ 2 ∧
      coefficientNorm security order (positiveInverse security order - 1) ≤
        2 * positiveConstant / (Parameters.base security : ℝ) ^ 39 := by
  let theta := positiveConstant / (Parameters.base security : ℝ) ^ 39
  have htheta : 0 ≤ theta := div_nonneg positiveConstant_nonneg (pow_nonneg (FirstResponse.base_pos security).le _)
  have hpower : (Parameters.base security : ℝ) ≤ (Parameters.base security : ℝ) ^ 39 := by
    simpa only [pow_one] using pow_le_pow_right₀ (base_ge_one security) (show 1 ≤ 39 by omega)
  have hhalf : theta ≤ 1 / 2 := by
    apply (div_le_iff₀ (pow_pos (FirstResponse.base_pos security) _)).mpr
    linarith
  have hgap : theta < 1 := by linarith
  have hdefect : coefficientNorm security order (1 - positiveFamily security order (independentPositiveLaw security)) ≤ theta := by
    have hequal : (1 - positiveFamily security order (independentPositiveLaw security) : Family security order) =
      -(positiveFamily security order (independentPositiveLaw security) - 1) := by abel
    rw [hequal, coefficientNorm, familyNorm_neg]
    exact independentPositive_defect security order
  constructor
  · apply (backgroundInverse_norm_le (primaryLaw security) (bodyReference security) order
      (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security)
      (primaryFactor_nonneg security) (bodyFactor_nonneg security) _ theta hgap hdefect).trans
    apply (div_le_iff₀ (sub_pos.mpr hgap)).mpr
    linarith
  · apply (backgroundInverse_correction_norm_le (primaryLaw security) (bodyReference security) order
      (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security)
      (primaryFactor_nonneg security) (bodyFactor_nonneg security) _ theta hgap hdefect).trans
    calc
      _ ≤ theta / (1 / 2) := div_le_div_of_nonneg_left htheta (by norm_num) (by linarith)
      _ = _ := by unfold theta; ring

theorem positiveInverse_bounds_eventually (order : ℕ) :
    ∀ᶠ security : ℕ in atTop,
      coefficientNorm security order (positiveInverse security order) ≤ 2 ∧
        coefficientNorm security order (positiveInverse security order - 1) ≤
          2 * positiveConstant / (Parameters.base security : ℝ) ^ 39 := by
  obtain ⟨threshold, hthreshold⟩ := exists_nat_ge (2 * positiveConstant)
  filter_upwards [eventually_ge_atTop threshold] with security hsecurity
  apply positiveInverse_bounds
  exact hthreshold.trans (Nat.cast_le.mpr (show threshold ≤ Parameters.base security by unfold Parameters.base; omega))

theorem localRaising_bound (security order : ℕ) (horder : 1 ≤ order)
    (hlarge : 2 * positiveConstant ≤ (Parameters.base security : ℝ))
    (score : Palette security → ℝ) (hcentered : (primaryLaw security).expectation score = 0) :
    coefficientNorm security order (localRaising security order horder score hcentered) ≤
      (raisingConstant / (Parameters.base security : ℝ) ^ 102) *
        Real.sqrt ((primaryLaw security).expectation (fun color => score color ^ 2)) := by
  let primary := primaryFamily (primaryLaw security) (bodyReference security) order horder score hcentered
  let higher := higherFamily security order (IndependentPairedReference.independentSignedMass security score)
  have hsplit : localRaising security order horder score hcentered =
      higher * positiveInverse security order + primary * (positiveInverse security order - 1) := by
    unfold localRaising independentNormalized normalizedFamily
    rw [independentComplete_eq_primary_add_higher security order horder score hcentered]
    change (primary + higher) * positiveInverse security order - primary = _
    rw [add_mul, mul_sub, mul_one]
    abel
  have hinverse := positiveInverse_bounds security order hlarge
  have hnormPrimary : coefficientNorm security order primary =
      BackgroundRates.primaryFactor security *
        Real.sqrt ((primaryLaw security).expectation (fun color => score color ^ 2)) :=
    primaryFamily_norm _ _ order horder _ _ score hcentered
  have hinput := Real.sqrt_nonneg ((primaryLaw security).expectation (fun color => score color ^ 2))
  have hprimaryNonneg := familyNorm_nonneg (primaryLaw security) (bodyReference security) order
    (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security)
    (primaryFactor_nonneg security) (bodyFactor_nonneg security) primary
  have hhigh := independentHigher_norm security order score
  have hnormInverseNonneg := familyNorm_nonneg (primaryLaw security) (bodyReference security) order
    (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security)
    (primaryFactor_nonneg security) (bodyFactor_nonneg security) (positiveInverse security order)
  have hhighBoundNonneg : 0 ≤ (higherConstant / (Parameters.base security : ℝ) ^ 102) *
      Real.sqrt ((primaryLaw security).expectation (fun color => score color ^ 2)) :=
    mul_nonneg (div_nonneg higherConstant_nonneg (pow_nonneg (FirstResponse.base_pos security).le _)) hinput
  have hpf : BackgroundRates.primaryFactor security ≤ 1 / (Parameters.base security : ℝ) ^ 63 := by
    rw [BackgroundRates.primaryFactor_eq]
    exact one_div_le_one_div_of_le (pow_pos (FirstResponse.base_pos security) _)
      (pow_le_pow_right₀ (base_ge_one security) (show 63 ≤ 64 by omega))
  have hcoef : (BackgroundRates.primaryFactor security *
        Real.sqrt ((primaryLaw security).expectation (fun color => score color ^ 2))) *
        (2 * positiveConstant / (Parameters.base security : ℝ) ^ 39) ≤
      (2 * positiveConstant / (Parameters.base security : ℝ) ^ 102) *
        Real.sqrt ((primaryLaw security).expectation (fun color => score color ^ 2)) := by
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpf hinput)
      (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) positiveConstant_nonneg)
        (pow_nonneg (FirstResponse.base_pos security).le 39))
    apply h.trans_eq
    rw [show (102 : ℕ) = 63 + 39 by omega, pow_add]
    ring
  rw [hsplit]
  calc
    _ ≤ coefficientNorm security order (higher * positiveInverse security order) +
        coefficientNorm security order (primary * (positiveInverse security order - 1)) :=
      familyNorm_add_le _ _ order _ _ (primaryFactor_nonneg security) (bodyFactor_nonneg security) _ _
    _ ≤ coefficientNorm security order higher * coefficientNorm security order (positiveInverse security order) +
        coefficientNorm security order primary * coefficientNorm security order (positiveInverse security order - 1) :=
      add_le_add (familyNorm_product_le _ _ order _ _ (primaryFactor_nonneg security) (bodyFactor_nonneg security) _ _)
        (familyNorm_product_le _ _ order _ _ (primaryFactor_nonneg security) (bodyFactor_nonneg security) _ _)
    _ ≤ ((higherConstant / (Parameters.base security : ℝ) ^ 102) *
        Real.sqrt ((primaryLaw security).expectation (fun color => score color ^ 2))) * 2 +
        coefficientNorm security order primary * (2 * positiveConstant / (Parameters.base security : ℝ) ^ 39) := by
      exact add_le_add (mul_le_mul hhigh hinverse.1 hnormInverseNonneg hhighBoundNonneg)
        (mul_le_mul_of_nonneg_left hinverse.2 hprimaryNonneg)
    _ ≤ ((higherConstant / (Parameters.base security : ℝ) ^ 102) *
        Real.sqrt ((primaryLaw security).expectation (fun color => score color ^ 2))) * 2 +
        (2 * positiveConstant / (Parameters.base security : ℝ) ^ 102) *
          Real.sqrt ((primaryLaw security).expectation (fun color => score color ^ 2)) := by
      rw [hnormPrimary]
      exact add_le_add le_rfl hcoef
    _ = _ := by unfold raisingConstant; ring

theorem localRaising_bound_eventually (order : ℕ) (horder : 1 ≤ order) :
    ∀ᶠ security : ℕ in atTop, ∀ (score : Palette security → ℝ)
      (hcentered : (primaryLaw security).expectation score = 0),
      coefficientNorm security order (localRaising security order horder score hcentered) ≤
        (raisingConstant / (Parameters.base security : ℝ) ^ 102) *
          Real.sqrt ((primaryLaw security).expectation (fun color => score color ^ 2)) := by
  obtain ⟨threshold, hthreshold⟩ := exists_nat_ge (2 * positiveConstant)
  filter_upwards [eventually_ge_atTop threshold] with security hsecurity score hcentered
  apply localRaising_bound security order horder _ score hcentered
  exact hthreshold.trans (Nat.cast_le.mpr (show threshold ≤ Parameters.base security by unfold Parameters.base; omega))

end
end CurrentAFT.LocalRaisingBounds
