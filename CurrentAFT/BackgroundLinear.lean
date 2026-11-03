import CurrentAFT.BackgroundFamilies

/-!
# The actual leg linear certificate and cancellation of the shared queue

The queue scalar is averaged only after the complete fixed-queue linear
coefficient is formed. Its law is the same clipped Gaussian law as the leg
scalar. All coefficients below are elements of the genuine truncated family
algebra with the actual positive safe-control reference.
-/

namespace CurrentAFT.BackgroundLinear

open AFT ControlCoordinates GradedControlAlgebra GradedControlNorm
  GradedControlStability DiffuseProfiles ProposalPrimary ActualControls
  BackgroundCertificates BackgroundRates BackgroundFamilies
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
  ProposalPrimary.primaryLaw ProposalPrimary.centerLaw ActualControls.bodyReference
  BackgroundFamilies.freeCertificate BackgroundFamilies.translationCertificate
  BackgroundRates.primaryFactor BackgroundRates.bodyFactor

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def certificateNorm (security order : ℕ) (family : ActualFamily security order) : ℝ :=
  familyNorm (primaryLaw security) (bodyReference security) order
    (primaryFactor security) (bodyFactor security) family

theorem certificateNorm_nonneg (security order : ℕ) (family : ActualFamily security order) :
    0 ≤ certificateNorm security order family := by
  apply familyNorm_nonneg
  · unfold primaryFactor
    positivity
  · unfold bodyFactor radius
    positivity

theorem certificateNorm_add (security order : ℕ) (first second : ActualFamily security order) :
    certificateNorm security order (first + second) ≤
      certificateNorm security order first + certificateNorm security order second := by
  apply familyNorm_add_le
  · unfold primaryFactor
    positivity
  · unfold bodyFactor radius
    positivity

theorem certificateNorm_smul (security order : ℕ) (scalar : ℝ) (family : ActualFamily security order) :
    certificateNorm security order (scalar • family) = |scalar| * certificateNorm security order family :=
  familyNorm_smul _ _ _ _ _ _ _

theorem certificateNorm_sum_le {Index : Type*} (security order : ℕ)
    (indices : Finset Index) (families : Index → ActualFamily security order) :
    certificateNorm security order (∑ index ∈ indices, families index) ≤
      ∑ index ∈ indices, certificateNorm security order (families index) := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, certificateNorm, familyNorm_zero, le_refl]
  | @insert index indices hnot ih =>
    simp only [Finset.sum_insert hnot]
    exact (certificateNorm_add security order _ _).trans (add_le_add le_rfl ih)

theorem certificateNorm_average_le {Index : Type*} [Fintype Index] (security order : ℕ)
    (law : FiniteDist Index) (families : Index → ActualFamily security order) (bound : ℝ)
    (hbound : ∀ index, certificateNorm security order (families index) ≤ bound) :
    certificateNorm security order (∑ index, law.weight index • families index) ≤ bound := by
  calc
    _ ≤ ∑ index, certificateNorm security order (law.weight index • families index) :=
      certificateNorm_sum_le security order _ _
    _ = ∑ index, law.weight index * certificateNorm security order (families index) := by
      apply Finset.sum_congr rfl
      intro index _
      rw [certificateNorm_smul, abs_of_nonneg (law.nonneg index)]
    _ ≤ ∑ index, law.weight index * bound :=
      Finset.sum_le_sum fun index _ => mul_le_mul_of_nonneg_left (hbound index) (law.nonneg index)
    _ = bound := by rw [← Finset.sum_mul, law.sum_one, one_mul]

def meanTranslation (security order : ℕ) (horder : 1 ≤ order) : ActualFamily security order :=
  ∑ scalar, (scalarLaw security).weight scalar •
    translationCertificate security order horder scalar.val

def legLinearCertificate (security order : ℕ) (horder : 1 ≤ order) : ActualFamily security order :=
  -(Parameters.legCount security : ℝ)⁻¹ •
    (freeMass security • freeCertificate security order horder +
      (Parameters.modulus security : ℝ) • meanTranslation security order horder)

def fixedQueueLinear (security order : ℕ) (horder : 1 ≤ order) (queueScalar : ℤ) :
    ActualFamily security order :=
  freeMass security • freeCertificate security order horder +
    (Parameters.modulus security : ℝ) • translationCertificate security order horder queueScalar +
    (Parameters.legCount security : ℝ) • legLinearCertificate security order horder

theorem legCount_pos (security : ℕ) : (0 : ℝ) < Parameters.legCount security := by
  rw [Parameters.legCount_eq, Nat.cast_pow]
  exact pow_pos (FirstResponse.base_pos security) _

theorem fixedQueueLinear_eq (security order : ℕ) (horder : 1 ≤ order) (queueScalar : ℤ) :
    fixedQueueLinear security order horder queueScalar =
      (Parameters.modulus security : ℝ) •
        (translationCertificate security order horder queueScalar - meanTranslation security order horder) := by
  have hl := (legCount_pos security).ne'
  unfold fixedQueueLinear legLinearCertificate
  rw [smul_smul, mul_neg, mul_inv_cancel₀ hl, neg_one_smul]
  rw [smul_sub]
  abel

/-- The random queue scalar is not copied independently for each factor.
This cancellation averages the complete same-queue linear coefficient. -/
theorem fixedQueueLinear_average (security order : ℕ) (horder : 1 ≤ order) :
    (∑ scalar, (scalarLaw security).weight scalar •
      fixedQueueLinear security order horder scalar.val) = 0 := by
  simp only [fixedQueueLinear_eq, smul_sub, Finset.sum_sub_distrib]
  have hfirst : (∑ scalar, (scalarLaw security).weight scalar •
      ((Parameters.modulus security : ℝ) • translationCertificate security order horder scalar.val)) =
      (Parameters.modulus security : ℝ) • meanTranslation security order horder := by
    simp only [meanTranslation, Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro scalar _
    rw [mul_comm]
  have hsecond : (∑ scalar, (scalarLaw security).weight scalar •
      ((Parameters.modulus security : ℝ) • meanTranslation security order horder)) =
      (Parameters.modulus security : ℝ) • meanTranslation security order horder := by
    rw [← Finset.sum_smul, FiniteDist.sum_one, one_smul]
  rw [hfirst, hsecond, sub_self]

theorem meanTranslation_norm (security order : ℕ) (horder : 1 ≤ order) :
    certificateNorm security order (meanTranslation security order horder) ≤
      56 / (Parameters.base security : ℝ) ^ 79 :=
  certificateNorm_average_le security order (scalarLaw security) _ _
    (fun scalar => translationCertificate_norm_decay security order horder scalar.val)

theorem legLinearCertificate_norm (security order : ℕ) (horder : 1 ≤ order) :
    certificateNorm security order (legLinearCertificate security order horder) ≤
      (freeMass security * freeAtomEnvelope security +
        (Parameters.modulus security : ℝ) * (56 / (Parameters.base security : ℝ) ^ 79)) /
          Parameters.legCount security := by
  have hl := legCount_pos security
  rw [legLinearCertificate, certificateNorm_smul,
    abs_neg, abs_inv, abs_of_pos hl]
  calc
    _ ≤ (Parameters.legCount security : ℝ)⁻¹ *
        (certificateNorm security order (freeMass security • freeCertificate security order horder) +
          certificateNorm security order ((Parameters.modulus security : ℝ) • meanTranslation security order horder)) :=
      mul_le_mul_of_nonneg_left (certificateNorm_add security order _ _) (inv_nonneg.mpr hl.le)
    _ = (Parameters.legCount security : ℝ)⁻¹ *
        (freeMass security * certificateNorm security order (freeCertificate security order horder) +
          (Parameters.modulus security : ℝ) * certificateNorm security order (meanTranslation security order horder)) := by
      rw [certificateNorm_smul, certificateNorm_smul, abs_of_nonneg (freeMass_nonneg security),
        abs_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ (Parameters.legCount security : ℝ)⁻¹ *
        (freeMass security * freeAtomEnvelope security +
          (Parameters.modulus security : ℝ) * (56 / (Parameters.base security : ℝ) ^ 79)) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hl.le)
      exact add_le_add
        (mul_le_mul_of_nonneg_left (freeCertificate_norm security order horder) (freeMass_nonneg security))
        (mul_le_mul_of_nonneg_left (meanTranslation_norm security order horder) (Nat.cast_nonneg _))
    _ = _ := by ring

theorem bodySize_upper (security : ℕ) :
    (Parameters.bodySize security : ℝ) ≤ 131072 * (Parameters.base security : ℝ) ^ 160 := by
  have h := Nat.mul_le_mul_right (Parameters.base security ^ 96) (Parameters.modulus_bounds security).2
  exact_mod_cast (by simpa only [Parameters.bodySize_eq, mul_assoc, ← pow_add] using h)

theorem legLinearCertificate_norm_decay (security order : ℕ) (horder : 1 ≤ order) :
    certificateNorm security order (legLinearCertificate security order horder) ≤
      18350080 / (Parameters.base security : ℝ) ^ 78 := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  have hfree : freeMass security ≤ 131072 * (Parameters.base security : ℝ) ^ 160 := by
    apply le_trans _ (bodySize_upper security)
    unfold freeMass
    have hl : (0 : ℝ) ≤ Parameters.legCount security := Nat.cast_nonneg _
    have hq : (0 : ℝ) ≤ Parameters.modulus security := Nat.cast_nonneg _
    linarith
  have hq : (Parameters.modulus security : ℝ) ≤ 131072 * (Parameters.base security : ℝ) ^ 64 := by
    exact_mod_cast (Parameters.modulus_bounds security).2
  have hp : (Parameters.base security : ℝ) ^ 78 ≤ (Parameters.base security : ℝ) ^ 143 :=
    pow_le_pow_right₀ hb1 (by omega)
  calc
    _ ≤ (freeMass security * freeAtomEnvelope security +
        (Parameters.modulus security : ℝ) * (56 / (Parameters.base security : ℝ) ^ 79)) /
          Parameters.legCount security := legLinearCertificate_norm security order horder
    _ ≤ ((131072 * (Parameters.base security : ℝ) ^ 160) *
        (84 / (Parameters.base security : ℝ) ^ 110) +
        (131072 * (Parameters.base security : ℝ) ^ 64) *
        (56 / (Parameters.base security : ℝ) ^ 79)) / Parameters.legCount security := by
      apply div_le_div_of_nonneg_right _ (legCount_pos security).le
      exact add_le_add
        (mul_le_mul hfree (freeAtomEnvelope_decay security) (freeAtomEnvelope_nonneg security) (by positivity))
        (mul_le_mul_of_nonneg_right hq (by positivity))
    _ = 11010048 / (Parameters.base security : ℝ) ^ 78 +
        7340032 / (Parameters.base security : ℝ) ^ 143 := by
      rw [Parameters.legCount_eq, Nat.cast_pow]
      field_simp
      ring
    _ ≤ 11010048 / (Parameters.base security : ℝ) ^ 78 +
        7340032 / (Parameters.base security : ℝ) ^ 78 :=
      add_le_add le_rfl (div_le_div_of_nonneg_left (by norm_num) (pow_pos hb _) hp)
    _ = _ := by ring

theorem leg_population_linear_quadratic_budget (security order : ℕ) (horder : 1 ≤ order) :
    (Parameters.legCount security : ℝ) *
      certificateNorm security order (legLinearCertificate security order horder) ^ 2 ≤
        336725436006400 / (Parameters.base security : ℝ) ^ 28 := by
  have hb := FirstResponse.base_pos security
  have hs := pow_le_pow_left₀ (certificateNorm_nonneg security order _) (legLinearCertificate_norm_decay security order horder) 2
  calc
    _ ≤ (Parameters.legCount security : ℝ) * (18350080 / (Parameters.base security : ℝ) ^ 78) ^ 2 :=
      mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)
    _ = _ := by
      rw [Parameters.legCount_eq, Nat.cast_pow]
      field_simp
      ring

end

end CurrentAFT.BackgroundLinear
