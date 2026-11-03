import CurrentAFT.GradedControlStability
import CurrentAFT.GradedInverse

/-!
# Quantitative bounds for the actual finite background inverse

The inverse is the finite polynomial in `1 - background` constructed in
`GradedInverse`. Its bounds follow from the proved graded norm triangle and
submultiplicativity, with finite geometric identities. No analytic inverse,
normed-algebra structure, or assumed inverse bound is used.
-/

namespace CurrentAFT.GradedInverseNorm

open AFT ControlCoordinates ControlProduct ControlNorm GradedControlAlgebra GradedControlNorm
open GradedControlStability GradedInverse
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

theorem familyNorm_one (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (primaryFactor bodyFactor : ℝ) :
    familyNorm primary body order primaryFactor bodyFactor (1 : KernelFamily primary body order) = 1 := by
  unfold familyNorm
  change (∑ arity : TruncatedArity order,
    gradeWeight primaryFactor bodyFactor arity.val.1.val arity.val.2.val *
      blockL2 primary body ((familyUnit primary body order) arity).val) = 1
  unfold familyUnit
  rw [Finset.sum_eq_single (zeroArity order)]
  · rw [Pi.single_eq_same]
    change gradeWeight primaryFactor bodyFactor 0 0 * blockL2 primary body (scalarUnit primary body).val = 1
    have hscalar : (scalarUnit primary body).val = (scalarKernel primary body 1).val := rfl
    rw [hscalar, blockL2_scalarKernel]
    simp only [gradeWeight, pow_zero, mul_one, abs_one]
  · intro arity _ hnot
    rw [Pi.single_eq_of_ne (M := fun arity : TruncatedArity order =>
      canonicalKernels primary body arity.val.1.val arity.val.2.val) hnot]
    simp only [Submodule.coe_zero, blockL2, blockEnergy_apply, Pi.zero_apply,
      zero_pow (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero, Real.sqrt_zero]
  · simp

theorem familyNorm_sum_le {Index : Type*} (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (primaryFactor bodyFactor : ℝ) (hprimary : 0 ≤ primaryFactor) (hbody : 0 ≤ bodyFactor)
    (terms : Finset Index) (family : Index → KernelFamily primary body order) :
    familyNorm primary body order primaryFactor bodyFactor (∑ index ∈ terms, family index) ≤
      ∑ index ∈ terms, familyNorm primary body order primaryFactor bodyFactor (family index) := by
  induction terms using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, familyNorm_zero, le_refl]
  | @insert index terms hnot ih =>
    rw [Finset.sum_insert hnot, Finset.sum_insert hnot]
    exact (familyNorm_add_le primary body order primaryFactor bodyFactor hprimary hbody _ _).trans
      (add_le_add le_rfl ih)

theorem familyNorm_pow_le (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (primaryFactor bodyFactor : ℝ) (hprimary : 0 ≤ primaryFactor) (hbody : 0 ≤ bodyFactor)
    (family : KernelFamily primary body order) (power : ℕ) :
    familyNorm primary body order primaryFactor bodyFactor (family ^ power) ≤
      familyNorm primary body order primaryFactor bodyFactor family ^ power := by
  induction power with
  | zero => rw [pow_zero, pow_zero, familyNorm_one]
  | succ power ih =>
    rw [pow_succ, pow_succ]
    exact (familyNorm_product_le primary body order primaryFactor bodyFactor hprimary hbody _ _).trans
      (mul_le_mul_of_nonneg_right ih (familyNorm_nonneg primary body order primaryFactor bodyFactor hprimary hbody _))

private theorem finite_geometric_le (theta : ℝ) (htheta : 0 ≤ theta) (hgap : theta < 1) (terms : ℕ) :
    (∑ power ∈ Finset.range terms, theta ^ power) ≤ 1 / (1 - theta) := by
  apply (le_div_iff₀ (sub_pos.mpr hgap)).mpr
  rw [geom_sum_mul_neg]
  linarith [pow_nonneg htheta terms]

theorem backgroundInverse_norm_le (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (primaryFactor bodyFactor : ℝ) (hprimary : 0 ≤ primaryFactor) (hbody : 0 ≤ bodyFactor)
    (background : KernelFamily primary body order) (theta : ℝ) (hgap : theta < 1)
    (hdefect : familyNorm primary body order primaryFactor bodyFactor (1 - background) ≤ theta) :
    familyNorm primary body order primaryFactor bodyFactor (backgroundInverse primary body order background) ≤
      1 / (1 - theta) := by
  have htheta : 0 ≤ theta :=
    (familyNorm_nonneg primary body order primaryFactor bodyFactor hprimary hbody _).trans hdefect
  unfold backgroundInverse
  calc
    _ ≤ ∑ power ∈ Finset.range (order + 1),
        familyNorm primary body order primaryFactor bodyFactor ((1 - background) ^ power) :=
      familyNorm_sum_le primary body order primaryFactor bodyFactor hprimary hbody _ _
    _ ≤ ∑ power ∈ Finset.range (order + 1), theta ^ power := by
      apply Finset.sum_le_sum
      intro power _
      exact (familyNorm_pow_le primary body order primaryFactor bodyFactor hprimary hbody _ power).trans
        (pow_le_pow_left₀ (familyNorm_nonneg primary body order primaryFactor bodyFactor hprimary hbody _) hdefect power)
    _ ≤ _ := finite_geometric_le theta htheta hgap (order + 1)

theorem backgroundInverse_sub_one (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (background : KernelFamily primary body order) :
    backgroundInverse primary body order background - 1 =
      ∑ power ∈ Finset.range order, (1 - background) ^ (power + 1) := by
  unfold backgroundInverse
  rw [Finset.sum_range_succ']
  simp only [pow_zero]
  abel

theorem backgroundInverse_correction_norm_le (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (primaryFactor bodyFactor : ℝ) (hprimary : 0 ≤ primaryFactor) (hbody : 0 ≤ bodyFactor)
    (background : KernelFamily primary body order) (theta : ℝ) (hgap : theta < 1)
    (hdefect : familyNorm primary body order primaryFactor bodyFactor (1 - background) ≤ theta) :
    familyNorm primary body order primaryFactor bodyFactor (backgroundInverse primary body order background - 1) ≤
      theta / (1 - theta) := by
  have htheta : 0 ≤ theta :=
    (familyNorm_nonneg primary body order primaryFactor bodyFactor hprimary hbody _).trans hdefect
  rw [backgroundInverse_sub_one]
  calc
    _ ≤ ∑ power ∈ Finset.range order,
        familyNorm primary body order primaryFactor bodyFactor ((1 - background) ^ (power + 1)) :=
      familyNorm_sum_le primary body order primaryFactor bodyFactor hprimary hbody _ _
    _ ≤ ∑ power ∈ Finset.range order, theta ^ (power + 1) := by
      apply Finset.sum_le_sum
      intro power _
      exact (familyNorm_pow_le primary body order primaryFactor bodyFactor hprimary hbody _ (power + 1)).trans
        (pow_le_pow_left₀ (familyNorm_nonneg primary body order primaryFactor bodyFactor hprimary hbody _) hdefect _)
    _ = theta * ∑ power ∈ Finset.range order, theta ^ power := by
      simp only [pow_succ]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro power _
      ring
    _ ≤ theta * (1 / (1 - theta)) := mul_le_mul_of_nonneg_left (finite_geometric_le theta htheta hgap order) htheta
    _ = _ := by ring

/-- Both exact inverse identities and both quantitative budgets concern the
same explicit finite polynomial in the same averaged background. -/
theorem bounded_background_inverse (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (primaryFactor bodyFactor : ℝ) (hprimary : 0 ≤ primaryFactor) (hbody : 0 ≤ bodyFactor)
    (background : KernelFamily primary body order)
    (hscalar : background (zeroArity order) = (1 : KernelFamily primary body order) (zeroArity order))
    (theta : ℝ) (hgap : theta < 1)
    (hdefect : familyNorm primary body order primaryFactor bodyFactor (1 - background) ≤ theta) :
    backgroundInverse primary body order background * background = 1 ∧
      background * backgroundInverse primary body order background = 1 ∧
      familyNorm primary body order primaryFactor bodyFactor (backgroundInverse primary body order background) ≤ 1 / (1 - theta) ∧
      familyNorm primary body order primaryFactor bodyFactor (backgroundInverse primary body order background - 1) ≤ theta / (1 - theta) := by
  exact ⟨backgroundInverse_mul primary body order background hscalar,
    mul_backgroundInverse primary body order background hscalar,
    backgroundInverse_norm_le primary body order primaryFactor bodyFactor hprimary hbody background theta hgap hdefect,
    backgroundInverse_correction_norm_le primary body order primaryFactor bodyFactor hprimary hbody background theta hgap hdefect⟩

/-- Multiplication by this same finite inverse has the required pointwise
operator bound in the actual graded norm. -/
theorem backgroundInverse_mul_norm_le (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (primaryFactor bodyFactor : ℝ) (hprimary : 0 ≤ primaryFactor) (hbody : 0 ≤ bodyFactor)
    (background : KernelFamily primary body order) (theta : ℝ) (hgap : theta < 1)
    (hdefect : familyNorm primary body order primaryFactor bodyFactor (1 - background) ≤ theta)
    (family : KernelFamily primary body order) :
    familyNorm primary body order primaryFactor bodyFactor
        (backgroundInverse primary body order background * family) ≤
      familyNorm primary body order primaryFactor bodyFactor family / (1 - theta) := by
  calc
    _ ≤ familyNorm primary body order primaryFactor bodyFactor (backgroundInverse primary body order background) *
        familyNorm primary body order primaryFactor bodyFactor family :=
      familyNorm_product_le primary body order primaryFactor bodyFactor hprimary hbody _ _
    _ ≤ (1 / (1 - theta)) * familyNorm primary body order primaryFactor bodyFactor family :=
      mul_le_mul_of_nonneg_right
        (backgroundInverse_norm_le primary body order primaryFactor bodyFactor hprimary hbody background theta hgap hdefect)
        (familyNorm_nonneg primary body order primaryFactor bodyFactor hprimary hbody _)
    _ = _ := by ring

theorem backgroundInverse_mul_correction_norm_le (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (primaryFactor bodyFactor : ℝ) (hprimary : 0 ≤ primaryFactor) (hbody : 0 ≤ bodyFactor)
    (background : KernelFamily primary body order) (theta : ℝ) (hgap : theta < 1)
    (hdefect : familyNorm primary body order primaryFactor bodyFactor (1 - background) ≤ theta)
    (family : KernelFamily primary body order) :
    familyNorm primary body order primaryFactor bodyFactor
        (backgroundInverse primary body order background * family - family) ≤
      theta * familyNorm primary body order primaryFactor bodyFactor family / (1 - theta) := by
  have hidentity : backgroundInverse primary body order background * family - family =
      (backgroundInverse primary body order background - 1) * family := by rw [sub_mul, one_mul]
  rw [hidentity]
  calc
    _ ≤ familyNorm primary body order primaryFactor bodyFactor (backgroundInverse primary body order background - 1) *
        familyNorm primary body order primaryFactor bodyFactor family :=
      familyNorm_product_le primary body order primaryFactor bodyFactor hprimary hbody _ _
    _ ≤ (theta / (1 - theta)) * familyNorm primary body order primaryFactor bodyFactor family :=
      mul_le_mul_of_nonneg_right
        (backgroundInverse_correction_norm_le primary body order primaryFactor bodyFactor hprimary hbody background theta hgap hdefect)
        (familyNorm_nonneg primary body order primaryFactor bodyFactor hprimary hbody _)
    _ = _ := by ring

end

end CurrentAFT.GradedInverseNorm
