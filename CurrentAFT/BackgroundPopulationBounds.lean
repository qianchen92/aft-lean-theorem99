import CurrentAFT.BackgroundScalarZero

/-! Actual full-background first-sum and square-population budgets. -/

namespace CurrentAFT.BackgroundPopulationBounds

open AFT GradedControlAlgebra GradedControlNorm GradedControlStability
  DiffuseProfiles ProposalPrimary ActualControls BackgroundRates BackgroundFamilies
  BackgroundLinear LegBackgroundFamilies
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount ProposalPrimary.primaryLaw ActualControls.bodyReference
  BackgroundFamilies.freeCertificate BackgroundFamilies.translationCertificate BackgroundLinear.legLinearCertificate
  LegBackgroundFamilies.completeLegAtom LegBackgroundFamilies.legQuadratic LegBackgroundFamilies.legCubic

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def freeCount (security : ℕ) : ℕ := Parameters.bodySize security - Parameters.legCount security - Parameters.modulus security

theorem freeCount_cast (security : ℕ) : (freeCount security : ℝ) = freeMass security := by
  have hroom := population_room security
  unfold freeCount freeMass
  rw [Nat.cast_sub (by omega : Parameters.modulus security ≤ Parameters.bodySize security - Parameters.legCount security),
    Nat.cast_sub (by omega : Parameters.legCount security ≤ Parameters.bodySize security)]

theorem fixedQueueLinear_norm (security order : ℕ) (horder : 1 ≤ order) (queueShift : ℤ) :
    certificateNorm security order (fixedQueueLinear security order horder queueShift) ≤
      14680064 / (Parameters.base security : ℝ) ^ 15 := by
  have hb := FirstResponse.base_pos security
  have hq : (0 : ℝ) ≤ Parameters.modulus security := Nat.cast_nonneg _
  have hqu : (Parameters.modulus security : ℝ) ≤ 131072 * (Parameters.base security : ℝ) ^ 64 := by
    exact_mod_cast (Parameters.modulus_bounds security).2
  have hsub := certificateNorm_add security order (translationCertificate security order horder queueShift)
    (-meanTranslation security order horder)
  have hneg : certificateNorm security order (-meanTranslation security order horder) =
      certificateNorm security order (meanTranslation security order horder) := familyNorm_neg _ _ _ _ _ _
  rw [hneg] at hsub
  rw [fixedQueueLinear_eq, certificateNorm_smul, abs_of_nonneg hq]
  calc
    _ ≤ (Parameters.modulus security : ℝ) *
        (certificateNorm security order (translationCertificate security order horder queueShift) +
          certificateNorm security order (meanTranslation security order horder)) :=
      mul_le_mul_of_nonneg_left hsub hq
    _ ≤ (131072 * (Parameters.base security : ℝ) ^ 64) *
        (56 / (Parameters.base security : ℝ) ^ 79 + 56 / (Parameters.base security : ℝ) ^ 79) :=
      mul_le_mul hqu (add_le_add (translationCertificate_norm_decay security order horder queueShift)
        (meanTranslation_norm security order horder))
        (add_nonneg (certificateNorm_nonneg security order _) (certificateNorm_nonneg security order _)) (by positivity)
    _ = _ := by field_simp; ring

def combinedFirstSum (security order : ℕ) (horder : 2 ≤ order) (queueShift : ℤ) : ActualFamily security order :=
  freeMass security • freeCertificate security order (by omega) +
    (Parameters.modulus security : ℝ) • translationCertificate security order (by omega) queueShift +
    (Parameters.legCount security : ℝ) • completeLegAtom security order horder

theorem combinedFirstSum_eq (security order : ℕ) (horder : 2 ≤ order) (queueShift : ℤ) :
    combinedFirstSum security order horder queueShift =
      fixedQueueLinear security order (by omega) queueShift +
        (Parameters.legCount security : ℝ) • legQuadratic security order horder +
        (Parameters.legCount security : ℝ) • legCubic security order horder := by
  unfold combinedFirstSum fixedQueueLinear completeLegAtom
  rw [smul_add, smul_add]
  abel

theorem combinedFirstSum_norm (security order : ℕ) (horder : 2 ≤ order) (queueShift : ℤ) :
    certificateNorm security order (combinedFirstSum security order horder queueShift) ≤
      39707232 / (Parameters.base security : ℝ) ^ 6 := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  rw [combinedFirstSum_eq]
  calc
    _ ≤ certificateNorm security order
          (fixedQueueLinear security order (by omega) queueShift + (Parameters.legCount security : ℝ) • legQuadratic security order horder) +
        certificateNorm security order ((Parameters.legCount security : ℝ) • legCubic security order horder) := certificateNorm_add security order _ _
    _ ≤ certificateNorm security order (fixedQueueLinear security order (by omega) queueShift) +
        certificateNorm security order ((Parameters.legCount security : ℝ) • legQuadratic security order horder) +
        certificateNorm security order ((Parameters.legCount security : ℝ) • legCubic security order horder) :=
      add_le_add (certificateNorm_add security order _ _) le_rfl
    _ = certificateNorm security order (fixedQueueLinear security order (by omega) queueShift) +
        (Parameters.legCount security : ℝ) * certificateNorm security order (legQuadratic security order horder) +
        (Parameters.legCount security : ℝ) * certificateNorm security order (legCubic security order horder) := by
      rw [certificateNorm_smul, certificateNorm_smul, abs_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ 14680064 / (Parameters.base security : ℝ) ^ 15 + 2241888 / (Parameters.base security : ℝ) ^ 6 +
        22785280 / (Parameters.base security : ℝ) ^ 85 :=
      add_le_add (add_le_add (fixedQueueLinear_norm security order (by omega) queueShift)
        (legQuadratic_population_bound security order horder)) (legCubic_population_bound security order horder)
    _ ≤ 14680064 / (Parameters.base security : ℝ) ^ 6 + 2241888 / (Parameters.base security : ℝ) ^ 6 +
        22785280 / (Parameters.base security : ℝ) ^ 6 := by
      exact add_le_add (add_le_add (div_le_div_of_nonneg_left (by norm_num) (pow_pos hb _)
        (pow_le_pow_right₀ hb1 (by omega))) le_rfl) (div_le_div_of_nonneg_left (by norm_num) (pow_pos hb _)
          (pow_le_pow_right₀ hb1 (by omega)))
    _ = _ := by ring

theorem free_square_population (security order : ℕ) (horder : 1 ≤ order) :
    (freeCount security : ℝ) * certificateNorm security order (freeCertificate security order horder) ^ 2 ≤
      924844032 / (Parameters.base security : ℝ) ^ 60 := by
  have hcount : (freeCount security : ℝ) ≤ Parameters.bodySize security := by
    rw [freeCount_cast]
    unfold freeMass
    have hl : (0 : ℝ) ≤ Parameters.legCount security := Nat.cast_nonneg _
    have hq : (0 : ℝ) ≤ Parameters.modulus security := Nat.cast_nonneg _
    linarith
  have hsquare := pow_le_pow_left₀ (certificateNorm_nonneg security order _) (freeCertificate_norm security order horder) 2
  calc
    _ ≤ (Parameters.bodySize security : ℝ) * freeAtomEnvelope security ^ 2 :=
      mul_le_mul hcount hsquare (sq_nonneg _) (Nat.cast_nonneg _)
    _ ≤ _ := free_population_quadratic_budget security

theorem queue_square_population (security order : ℕ) (horder : 1 ≤ order) (queueShift : ℤ) :
    (Parameters.modulus security : ℝ) * certificateNorm security order (translationCertificate security order horder queueShift) ^ 2 ≤
      411041792 / (Parameters.base security : ℝ) ^ 94 := by
  have hsquare := pow_le_pow_left₀ (certificateNorm_nonneg security order _) (translationCertificate_norm security order horder queueShift) 2
  exact (mul_le_mul_of_nonneg_left hsquare (Nat.cast_nonneg _)).trans (queue_population_quadratic_budget security queueShift)

theorem square_population (security order : ℕ) (horder : 2 ≤ order) (queueShift : ℤ) :
    (freeCount security : ℝ) * certificateNorm security order (freeCertificate security order (by omega)) ^ 2 +
      (Parameters.modulus security : ℝ) * certificateNorm security order (translationCertificate security order (by omega) queueShift) ^ 2 +
      (Parameters.legCount security : ℝ) * certificateNorm security order (completeLegAtom security order horder) ^ 2 ≤
        1881586979939328 / (Parameters.base security : ℝ) ^ 28 := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  calc
    _ ≤ 924844032 / (Parameters.base security : ℝ) ^ 60 + 411041792 / (Parameters.base security : ℝ) ^ 94 +
        1881585644053504 / (Parameters.base security : ℝ) ^ 28 :=
      add_le_add (add_le_add (free_square_population security order (by omega))
        (queue_square_population security order (by omega) queueShift)) (completeLegAtom_square_population security order horder)
    _ ≤ 924844032 / (Parameters.base security : ℝ) ^ 28 + 411041792 / (Parameters.base security : ℝ) ^ 28 +
        1881585644053504 / (Parameters.base security : ℝ) ^ 28 := by
      exact add_le_add (add_le_add (div_le_div_of_nonneg_left (by norm_num) (pow_pos hb _)
        (pow_le_pow_right₀ hb1 (by omega))) (div_le_div_of_nonneg_left (by norm_num) (pow_pos hb _)
          (pow_le_pow_right₀ hb1 (by omega)))) le_rfl
    _ = _ := by ring

end

end CurrentAFT.BackgroundPopulationBounds
