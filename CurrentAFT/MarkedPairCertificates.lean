import CurrentAFT.MarkedPairSeed
import CurrentAFT.BackgroundFamilies

/-! The actual fixed-scalar marked seed in one primary and one safe-body fiber. -/

namespace CurrentAFT.MarkedPairCertificates

open AFT ControlCoordinates ControlNorm GradedControlAlgebra GradedControlNorm
  DiffuseProfiles ProposalPrimary ActualControls FirstResponse PrimaryTensorInverse
  BackgroundRates BackgroundFamilies MarkedPairSeed
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth ProposalPrimary.primaryLaw ActualControls.bodyReference
  BackgroundRates.primaryFactor BackgroundRates.bodyFactor MarkedPairSeed.seedDensity

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

def mixedEnergy (primary : FiniteDist Primary) (body : FiniteDist Body) (density : Primary → Body → ℝ) : ℝ :=
  ∑ color, ∑ center, primary.weight color * body.weight center * density color center ^ 2

theorem mixedEnergy_fibers (primary : FiniteDist Primary) (body : FiniteDist Body) (density : Primary → Body → ℝ) :
    mixedEnergy primary body density = ∑ center, body.weight center * primary.l2Sq (fun color => density color center) := by
  unfold mixedEnergy FiniteDist.l2Sq FiniteDist.expectation
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro center _
  apply Finset.sum_congr rfl
  intro color _
  ring

def mixedKernel (primary : FiniteDist Primary) (body : FiniteDist Body) (density : Primary → Body → ℝ)
    (hprimary : ∀ center, primary.expectation (fun color => density color center) = 0)
    (hbody : ∀ color, body.expectation (density color) = 0) : canonicalKernels primary body 1 1 := by
  refine ⟨fun colors centers => density (colors 0) (centers 0), ?_, ?_, ?_⟩
  · intro index colors centers
    have hi : index = 0 := Subsingleton.elim _ _
    subst index
    simpa only [Function.update_self] using hprimary (centers 0)
  · intro index colors centers
    have hi : index = 0 := Subsingleton.elim _ _
    subst index
    simpa only [Function.update_self] using hbody (colors 0)
  · intro primaryOrder bodyOrder colors centers
    have hp : primaryOrder 0 = 0 := Subsingleton.elim _ _
    have hb : bodyOrder 0 = 0 := Subsingleton.elim _ _
    simp only [Function.comp_apply, hp, hb]

theorem mixedKernel_blockL2 (primary : FiniteDist Primary) (body : FiniteDist Body) (density : Primary → Body → ℝ)
    (hprimary : ∀ center, primary.expectation (fun color => density color center) = 0)
    (hbody : ∀ color, body.expectation (density color) = 0) :
    blockL2 primary body (mixedKernel primary body density hprimary hbody).val = Real.sqrt (mixedEnergy primary body density) := by
  unfold blockL2
  congr 1
  rw [blockEnergy_apply]
  simp only [mixedKernel, Fin.prod_univ_one]
  rw [← (Equiv.funUnique (Fin 1) Primary).symm.sum_comp]
  simp only [Equiv.funUnique_symm_apply, uniqueElim_const]
  apply Finset.sum_congr rfl
  intro color _
  exact ((Equiv.funUnique (Fin 1) Body).symm.sum_comp (fun centers : Fin 1 → Body =>
    primary.weight color * body.weight (centers 0) * density color (centers 0) ^ 2)).symm

def inverseDensity (security : ℕ) (scalar : MarkedPairSeed.Scalar security)
    (primary : ActualControls.Palette security) (center : SafePalette security) : ℝ :=
  densityInverse security (fun color => seedDensity security scalar color center) primary

theorem inverseDensity_centered_primary (security : ℕ) (scalar : MarkedPairSeed.Scalar security) (center : SafePalette security) :
    (primaryLaw security).expectation (fun primary => inverseDensity security scalar primary center) = 0 := by
  rw [show (fun primary => inverseDensity security scalar primary center) =
    densityInverse security (fun color => seedDensity security scalar color center) from rfl,
    densityInverse_mean, seedDensity_centered_primary, mul_zero]

theorem inverseDensity_centered_body (security : ℕ) (scalar : MarkedPairSeed.Scalar security) (primary : ActualControls.Palette security) :
    (bodyReference security).expectation (inverseDensity security scalar primary) = 0 := by
  have hsum : (∑ center, (bodyReference security).weight center •
      (fun color => seedDensity security scalar color center)) = 0 := by
    funext color
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using seedDensity_centered_body security scalar color
  have heq : (bodyReference security).expectation (inverseDensity security scalar primary) =
      densityInverse security (∑ center, (bodyReference security).weight center •
        (fun color => seedDensity security scalar color center)) primary := by
    simp only [FiniteDist.expectation, inverseDensity, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [heq, hsum, map_zero]
  rfl

theorem inverseDensity_primary_response (security : ℕ) (scalar : MarkedPairSeed.Scalar security) (center : SafePalette security) :
    densityResponse security (fun primary => inverseDensity security scalar primary center) =
      fun primary => seedDensity security scalar primary center := densityResponse_inverse security _

theorem inverseDensity_energy (security : ℕ) (scalar : MarkedPairSeed.Scalar security) :
    mixedEnergy (primaryLaw security) (bodyReference security) (inverseDensity security scalar) ≤
      (2 / activation security) ^ 2 * (12 * (Parameters.modulus security : ℝ) / Parameters.anchorWidth security) := by
  rw [mixedEnergy_fibers]
  calc
    _ ≤ ∑ center, (bodyReference security).weight center *
        ((2 / activation security) ^ 2 * (primaryLaw security).l2Sq (fun primary => seedDensity security scalar primary center)) :=
      Finset.sum_le_sum fun center _ => mul_le_mul_of_nonneg_left
        (densityInverse_energy security _) ((bodyReference security).nonneg center)
    _ = (2 / activation security) ^ 2 * mixedEnergy (primaryLaw security) (bodyReference security) (seedDensity security scalar) := by
      rw [mixedEnergy_fibers]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro center _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (seedDensity_energy security scalar) (sq_nonneg _)

theorem inverseDensity_norm_growth (security : ℕ) (scalar : MarkedPairSeed.Scalar security) :
    Real.sqrt (mixedEnergy (primaryLaw security) (bodyReference security) (inverseDensity security scalar)) ≤
      16384 * (Parameters.base security : ℝ) ^ 9 := by
  have hb := FirstResponse.base_pos security
  have ha := activation_pos security
  have hA : (0 : ℝ) < Parameters.anchorWidth security := Nat.cast_pos.mpr (InwardAnchor.anchorWidth_pos security)
  have hq : (Parameters.modulus security : ℝ) ≤ 131072 * (Parameters.base security : ℝ) ^ 64 := by
    exact_mod_cast (Parameters.modulus_bounds security).2
  have hinv : 2 / activation security ≤ 8 * (Parameters.base security : ℝ) := by
    have h := mul_le_mul_of_nonneg_left (activation_inverse_le security) (show (0 : ℝ) ≤ 2 by norm_num)
    convert h using 1 <;> ring
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ (2 / activation security) ^ 2 * (12 * (Parameters.modulus security : ℝ) / Parameters.anchorWidth security) :=
      inverseDensity_energy security scalar
    _ ≤ (8 * (Parameters.base security : ℝ)) ^ 2 *
        (12 * (131072 * (Parameters.base security : ℝ) ^ 64) / Parameters.anchorWidth security) :=
      mul_le_mul (pow_le_pow_left₀ (by positivity) hinv 2)
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hq (by norm_num)) hA.le)
        (by positivity) (by positivity)
    _ = 100663296 * (Parameters.base security : ℝ) ^ 18 := by
      rw [anchorWidth_eq, Nat.cast_pow]
      field_simp
      ring
    _ ≤ _ := by
      have hh : (0 : ℝ) ≤ (Parameters.base security : ℝ) ^ 18 := pow_nonneg hb.le _
      nlinarith

def mixedArity (order : ℕ) (horder : 2 ≤ order) : TruncatedArity order :=
  ⟨(⟨1, by omega⟩, ⟨1, by omega⟩), by simpa⟩

def markedMixedCertificate (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) : ActualFamily security order :=
  Pi.single (mixedArity order horder) (mixedKernel (primaryLaw security) (bodyReference security) (inverseDensity security scalar)
    (inverseDensity_centered_primary security scalar) (inverseDensity_centered_body security scalar))

theorem markedMixedCertificate_norm (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
      (markedMixedCertificate security order horder scalar) ≤ 16384 / (Parameters.base security : ℝ) ^ 134 := by
  have hb := FirstResponse.base_pos security
  have hpf : 0 ≤ primaryFactor security := by unfold primaryFactor; positivity
  have hbf : 0 ≤ bodyFactor security := by unfold bodyFactor radius; positivity
  rw [markedMixedCertificate, familyNorm_single, mixedKernel_blockL2]
  simp only [mixedArity, gradeWeight, pow_one]
  calc
    _ ≤ (1 / (Parameters.base security : ℝ) ^ 64) * (1 / (Parameters.base security : ℝ) ^ 79) *
        (16384 * (Parameters.base security : ℝ) ^ 9) :=
      mul_le_mul (mul_le_mul (le_of_eq (primaryFactor_eq security)) (bodyFactor_le security) hbf (by positivity))
        (inverseDensity_norm_growth security scalar) (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by field_simp

theorem markedMixedCertificate_population_bound (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    (Parameters.legCount security : ℝ) *
      familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
        (markedMixedCertificate security order horder scalar) ≤ 16384 / (Parameters.base security : ℝ) ^ 6 := by
  have hb := FirstResponse.base_pos security
  calc
    _ ≤ (Parameters.legCount security : ℝ) * (16384 / (Parameters.base security : ℝ) ^ 134) :=
      mul_le_mul_of_nonneg_left (markedMixedCertificate_norm security order horder scalar) (Nat.cast_nonneg _)
    _ = _ := by rw [Parameters.legCount_eq, Nat.cast_pow]; field_simp

end

end CurrentAFT.MarkedPairCertificates
