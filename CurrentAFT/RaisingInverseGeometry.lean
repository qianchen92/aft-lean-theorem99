import CurrentAFT.CompleteRaisingInverse
import CurrentAFT.LocalRaisingBounds

/-! # Finite geometric norm bounds used for the constructed raising inverse -/
namespace CurrentAFT.RaisingInverseGeometry

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct
  GradedControlAlgebra GradedControlNorm GradedControlStability GradedInverseNorm
  LocalCoefficientFamily LocalRaisingBounds
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

private theorem primaryFactor_nonneg (security : ℕ) : 0 ≤ BackgroundRates.primaryFactor security := by
  unfold BackgroundRates.primaryFactor
  positivity

private theorem bodyFactor_nonneg (security : ℕ) : 0 ≤ BackgroundRates.bodyFactor security := by
  unfold BackgroundRates.bodyFactor BackgroundRates.radius
  positivity

private theorem norm_nonneg (security order : ℕ) (family : Family security order) :
    0 ≤ LocalRaisingBounds.coefficientNorm security order family :=
  familyNorm_nonneg _ _ order _ _ (primaryFactor_nonneg security) (bodyFactor_nonneg security) family

private theorem norm_sum_le {Index : Type*} (security order : ℕ) (terms : Finset Index)
    (family : Index → Family security order) :
    LocalRaisingBounds.coefficientNorm security order (∑ index ∈ terms, family index) ≤
      ∑ index ∈ terms, LocalRaisingBounds.coefficientNorm security order (family index) :=
  familyNorm_sum_le _ _ order _ _ (primaryFactor_nonneg security) (bodyFactor_nonneg security) terms family

theorem neg_pow_norm (security order : ℕ) (upper : Module.End ℝ (Family security order))
    (theta : ℝ) (htheta : 0 ≤ theta)
    (hupper : ∀ family, LocalRaisingBounds.coefficientNorm security order (upper family) ≤
      theta * LocalRaisingBounds.coefficientNorm security order family) (power : ℕ) (family : Family security order) :
    LocalRaisingBounds.coefficientNorm security order (((-upper) ^ power) family) ≤
      theta ^ power * LocalRaisingBounds.coefficientNorm security order family := by
  induction power with
  | zero => simp only [pow_zero, Module.End.one_apply, one_mul, le_refl]
  | succ power ih =>
    rw [pow_succ']
    change LocalRaisingBounds.coefficientNorm security order (-upper (((-upper) ^ power) family)) ≤ _
    rw [LocalRaisingBounds.coefficientNorm, familyNorm_neg]
    apply (hupper _).trans
    exact (mul_le_mul_of_nonneg_left ih htheta).trans_eq (by rw [pow_succ]; ring)

private theorem geometric_le (theta : ℝ) (htheta : 0 ≤ theta) (hgap : theta < 1) (terms : ℕ) :
    (∑ power ∈ Finset.range terms, theta ^ power) ≤ 1 / (1 - theta) := by
  apply (le_div_iff₀ (sub_pos.mpr hgap)).mpr
  rw [geom_sum_mul_neg]
  linarith [pow_nonneg htheta terms]

def finiteInverse (security order : ℕ) (upper : Module.End ℝ (Family security order)) : Module.End ℝ (Family security order) :=
  ∑ power ∈ Finset.range (order + 1), (-upper) ^ power

theorem finiteInverse_norm (security order : ℕ) (upper : Module.End ℝ (Family security order))
    (theta : ℝ) (htheta : 0 ≤ theta) (hgap : theta < 1)
    (hupper : ∀ family, LocalRaisingBounds.coefficientNorm security order (upper family) ≤
      theta * LocalRaisingBounds.coefficientNorm security order family) (family : Family security order) :
    LocalRaisingBounds.coefficientNorm security order (finiteInverse security order upper family) ≤
      (1 / (1 - theta)) * LocalRaisingBounds.coefficientNorm security order family := by
  unfold finiteInverse
  simp only [LinearMap.sum_apply]
  apply (norm_sum_le security order _ _).trans
  calc
    _ ≤ ∑ power ∈ Finset.range (order + 1), theta ^ power * LocalRaisingBounds.coefficientNorm security order family :=
      Finset.sum_le_sum (fun power _ => neg_pow_norm security order upper theta htheta hupper power family)
    _ = (∑ power ∈ Finset.range (order + 1), theta ^ power) * LocalRaisingBounds.coefficientNorm security order family :=
      (Finset.sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (geometric_le theta htheta hgap _) (norm_nonneg security order family)

theorem finiteInverse_correction (security order : ℕ) (upper : Module.End ℝ (Family security order))
    (theta : ℝ) (htheta : 0 ≤ theta) (hgap : theta < 1)
    (hupper : ∀ family, LocalRaisingBounds.coefficientNorm security order (upper family) ≤
      theta * LocalRaisingBounds.coefficientNorm security order family) (family : Family security order) :
    LocalRaisingBounds.coefficientNorm security order (finiteInverse security order upper family - family) ≤
      (theta / (1 - theta)) * LocalRaisingBounds.coefficientNorm security order family := by
  have hequal : finiteInverse security order upper family - family =
      ∑ power ∈ Finset.range order, (((-upper) ^ (power + 1)) family) := by
    unfold finiteInverse
    rw [Finset.sum_range_succ']
    simp only [LinearMap.add_apply, LinearMap.sum_apply, pow_zero, Module.End.one_apply]
    abel
  rw [hequal]
  apply (norm_sum_le security order _ _).trans
  calc
    _ ≤ ∑ power ∈ Finset.range order, theta ^ (power + 1) * LocalRaisingBounds.coefficientNorm security order family :=
      Finset.sum_le_sum (fun power _ => neg_pow_norm security order upper theta htheta hupper (power + 1) family)
    _ = theta * (∑ power ∈ Finset.range order, theta ^ power) * LocalRaisingBounds.coefficientNorm security order family := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro power _
      rw [pow_succ]
      ring
    _ ≤ theta * (1 / (1 - theta)) * LocalRaisingBounds.coefficientNorm security order family :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (geometric_le theta htheta hgap _) htheta)
        (norm_nonneg security order family)
    _ = _ := by ring

end
end CurrentAFT.RaisingInverseGeometry
