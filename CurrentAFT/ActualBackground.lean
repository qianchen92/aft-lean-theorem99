import CurrentAFT.BackgroundPopulationBounds
import CurrentAFT.RoleProduct

/-!
# Closed stability bound for the actual complete same-queue background

All three role atoms and their populations are the concrete current
families. The only large-parameter condition below is an explicit numerical
threshold. No small-background or response-size hypothesis is supplied.
-/

namespace CurrentAFT.ActualBackground

open AFT GradedControlAlgebra GradedControlNorm GradedControlStability RoleProduct
  DiffuseProfiles ProposalPrimary ActualControls BackgroundRates BackgroundFamilies
  BackgroundLinear LegBackgroundFamilies BackgroundScalarZero BackgroundPopulationBounds
open Filter
open scoped BigOperators Classical Topology

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount ProposalPrimary.primaryLaw ActualControls.bodyReference
  BackgroundFamilies.freeCertificate BackgroundFamilies.translationCertificate LegBackgroundFamilies.completeLegAtom

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def numericalThreshold : ℕ := 10000000000000000

def budget (security : ℕ) : ℝ := (numericalThreshold : ℝ) / (Parameters.base security : ℝ) ^ 6

theorem budget_nonneg (security : ℕ) : 0 ≤ budget security := by unfold budget; positivity

theorem rate_le_budget (security : ℕ) (numerator : ℝ) (exponent : ℕ)
    (hnum : 0 ≤ numerator) (hupper : numerator ≤ numericalThreshold) (hexponent : 6 ≤ exponent) :
    numerator / (Parameters.base security : ℝ) ^ exponent ≤ budget security := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  exact (div_le_div_of_nonneg_left hnum (pow_pos hb _) (pow_le_pow_right₀ hb1 hexponent)).trans
    (div_le_div_of_nonneg_right hupper (pow_nonneg hb.le _))

theorem budget_le_one (security : ℕ) (hsecurity : numericalThreshold ≤ security) : budget security ≤ 1 := by
  have hb := FirstResponse.base_pos security
  have hbase : (numericalThreshold : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show numericalThreshold ≤ Parameters.base security by unfold Parameters.base; omega)
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  have hpower : (numericalThreshold : ℝ) ≤ (Parameters.base security : ℝ) ^ 6 :=
    hbase.trans (by simpa only [pow_one] using pow_le_pow_right₀ hb1 (show 1 ≤ 6 by omega))
  exact (div_le_one (pow_pos hb _)).mpr hpower

theorem role_count_lower (security order : ℕ) (horder : order ≤ security) :
    order ≤ freeCount security + Parameters.modulus security + Parameters.legCount security := by
  have hbase : order ≤ Parameters.base security := by unfold Parameters.base; omega
  have hleg : Parameters.base security ≤ Parameters.legCount security := by
    rw [Parameters.legCount_eq]
    exact Nat.le_self_pow (by omega : 128 ≠ 0) _
  omega

def fixedQueueBackground (security order : ℕ) (horder : 2 ≤ order) (queueShift : ℤ) : ActualFamily security order :=
  (1 + freeCertificate security order (by omega)) ^ freeCount security *
    (1 + translationCertificate security order (by omega) queueShift) ^ Parameters.modulus security *
    (1 + completeLegAtom security order horder) ^ Parameters.legCount security

def background (security order : ℕ) (horder : 2 ≤ order) : ActualFamily security order :=
  ∑ scalar, (scalarLaw security).weight scalar • fixedQueueBackground security order horder scalar.val

theorem nat_role_sum_eq (security order : ℕ) (horder : 2 ≤ order) (queueShift : ℤ) :
    freeCount security • freeCertificate security order (by omega) +
      Parameters.modulus security • translationCertificate security order (by omega) queueShift +
      Parameters.legCount security • completeLegAtom security order horder = combinedFirstSum security order horder queueShift := by
  unfold combinedFirstSum
  rw [← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ, freeCount_cast]

theorem fixedQueueBackground_norm (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : max order numericalThreshold ≤ security) (queueShift : ℤ) :
    certificateNorm security order (fixedQueueBackground security order horder queueShift - 1) ≤
      (order : ℝ) * budget security * ((order + 1 : ℕ) : ℝ) ^ order := by
  have hb := FirstResponse.base_pos security
  have hp : 0 ≤ primaryFactor security := by unfold primaryFactor; positivity
  have hbdy : 0 ≤ bodyFactor security := by unfold bodyFactor radius; positivity
  have hsmall := budget_le_one security ((le_max_right order numericalThreshold).trans hsecurity)
  have hfree : certificateNorm security order (freeCertificate security order (by omega)) ≤ budget security :=
    (freeCertificate_norm_decay security order (by omega)).trans
      (rate_le_budget security 84 110 (by norm_num) (by norm_num [numericalThreshold]) (by omega))
  have hqueue : certificateNorm security order (translationCertificate security order (by omega) queueShift) ≤ budget security :=
    (translationCertificate_norm_decay security order (by omega) queueShift).trans
      (rate_le_budget security 56 79 (by norm_num) (by norm_num [numericalThreshold]) (by omega))
  have hleg : certificateNorm security order (completeLegAtom security order horder) ≤ budget security :=
    (completeLegAtom_norm security order horder).trans
      (rate_le_budget security 43377248 78 (by norm_num) (by norm_num [numericalThreshold]) (by omega))
  have hfirst : certificateNorm security order
      (freeCount security • freeCertificate security order (by omega) +
        Parameters.modulus security • translationCertificate security order (by omega) queueShift +
        Parameters.legCount security • completeLegAtom security order horder) ≤ budget security := by
    rw [nat_role_sum_eq]
    exact (combinedFirstSum_norm security order horder queueShift).trans
      (rate_le_budget security 39707232 6 (by norm_num) (by norm_num [numericalThreshold]) (by omega))
  have hsquares : (freeCount security : ℝ) * certificateNorm security order (freeCertificate security order (by omega)) ^ 2 +
      (Parameters.modulus security : ℝ) * certificateNorm security order (translationCertificate security order (by omega) queueShift) ^ 2 +
      (Parameters.legCount security : ℝ) * certificateNorm security order (completeLegAtom security order horder) ^ 2 ≤ budget security :=
    (square_population security order horder queueShift).trans
      (rate_le_budget security 1881586979939328 28 (by norm_num) (by norm_num [numericalThreshold]) (by omega))
  exact complete_role_product_norm_le (primaryLaw security) (bodyReference security) order
    (primaryFactor security) (bodyFactor security) hp hbdy (freeCount security) (Parameters.modulus security) (Parameters.legCount security)
    (role_count_lower security order ((le_max_left order numericalThreshold).trans hsecurity))
    (freeCertificate security order (by omega)) (translationCertificate security order (by omega) queueShift) (completeLegAtom security order horder)
    (freeCertificate_zero security order (by omega)) (translationCertificate_zero security order (by omega) queueShift)
    (completeLegAtom_zero security order horder) (budget security) (budget_nonneg security) hsmall hfirst hsquares
    (hfree.trans hsmall) (hqueue.trans hsmall) (hleg.trans hsmall)

theorem background_sub_one (security order : ℕ) (horder : 2 ≤ order) :
    background security order horder - 1 =
      ∑ scalar, (scalarLaw security).weight scalar • (fixedQueueBackground security order horder scalar.val - 1) := by
  simp only [background, smul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_smul, FiniteDist.sum_one, one_smul]

theorem background_norm (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : max order numericalThreshold ≤ security) :
    certificateNorm security order (background security order horder - 1) ≤
      (order : ℝ) * budget security * ((order + 1 : ℕ) : ℝ) ^ order := by
  rw [background_sub_one]
  exact certificateNorm_average_le security order (scalarLaw security) _ _
    (fun scalar => fixedQueueBackground_norm security order horder hsecurity scalar.val)

def stabilityConstant (order : ℕ) : ℝ :=
  (order : ℝ) * ((order + 1 : ℕ) : ℝ) ^ order * numericalThreshold

theorem background_norm_decay (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : max order numericalThreshold ≤ security) :
    certificateNorm security order (background security order horder - 1) ≤
      stabilityConstant order / (Parameters.base security : ℝ) ^ 6 := by
  apply (background_norm security order horder hsecurity).trans_eq
  unfold budget stabilityConstant
  ring

theorem background_norm_decay_eventually (order : ℕ) (horder : 2 ≤ order) :
    ∀ᶠ security : ℕ in atTop, certificateNorm security order (background security order horder - 1) ≤
      stabilityConstant order / (Parameters.base security : ℝ) ^ 6 := by
  filter_upwards [eventually_ge_atTop (max order numericalThreshold)] with security hsecurity
  exact background_norm_decay security order horder hsecurity

end

end CurrentAFT.ActualBackground
