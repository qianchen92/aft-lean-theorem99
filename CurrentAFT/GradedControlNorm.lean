import CurrentAFT.GradedControlAlgebra

/-!
# Submultiplicativity of the actual finite graded coefficient norm

The proof sums the already verified Hilbert block inequalities over the
actual arity convolution. Each pair of input arities has at most one output
arity. The proof therefore introduces no dimension or palette factor.
The scalar-plus-positive coefficient norm is identified with this finite
family norm by an explicit split of the zero and positive arities.
-/

namespace CurrentAFT.GradedControlNorm

open AFT ControlCoordinates ControlProduct ControlNorm GradedControlAlgebra
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

private theorem blockL2_zero (primary : FiniteDist Primary) (body : FiniteDist Body)
    (r s : ℕ) :
    blockL2 primary body (0 : DensityKernel (Primary := Primary) (Body := Body) r s) = 0 := by
  simp only [blockL2, blockEnergy_apply, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0),
    mul_zero, Finset.sum_const_zero, Real.sqrt_zero]

private theorem canonical_sum_l2_le {Index : Type*} (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s : ℕ} (terms : Finset Index) (kernels : Index → canonicalKernels primary body r s) :
    blockL2 primary body (∑ index ∈ terms, kernels index).val ≤
      ∑ index ∈ terms, blockL2 primary body (kernels index).val := by
  induction terms using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Submodule.coe_zero, blockL2_zero, le_refl]
  | @insert index terms hnot ih =>
    simp only [Finset.sum_insert hnot, Submodule.coe_add]
    exact (blockL2_add_le primary body _ _).trans (add_le_add le_rfl ih)

theorem transportKernel_blockL2 (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s r' s' : ℕ} (hr : r = r') (hs : s = s') (kernel : canonicalKernels primary body r s) :
    blockL2 primary body (transportKernel primary body hr hs kernel).val =
      blockL2 primary body kernel.val := by
  subst r'
  subst s'
  rfl

/-- The full finite weighted l1 sum of the genuine Hilbert block norms. -/
def familyNorm (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (primaryFactor bodyFactor : ℝ) (family : KernelFamily primary body order) : ℝ :=
  ∑ arity : TruncatedArity order,
    gradeWeight primaryFactor bodyFactor arity.val.1.val arity.val.2.val *
      blockL2 primary body (family arity).val

theorem familyNorm_nonneg (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (primaryFactor bodyFactor : ℝ) (hprimary : 0 ≤ primaryFactor) (hbody : 0 ≤ bodyFactor)
    (family : KernelFamily primary body order) : 0 ≤ familyNorm primary body order primaryFactor bodyFactor family := by
  apply Finset.sum_nonneg
  intro arity _
  exact mul_nonneg (gradeWeight_nonneg primaryFactor bodyFactor hprimary hbody _ _) (blockL2_nonneg primary body _)

private theorem sum_cycle {First Second Third : Type*}
    [Fintype First] [Fintype Second] [Fintype Third] (term : First → Second → Third → ℝ) :
    (∑ first, ∑ second, ∑ third, term first second third) =
      ∑ second, ∑ third, ∑ first, term first second third := by
  calc
    _ = ∑ second, ∑ first, ∑ third, term first second third := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro second _
      exact Finset.sum_comm

/-- Submultiplicativity for the actual truncated convolution. The sums are
over every legal arity, and pairs whose total degree is too large contribute
nothing rather than producing a multiplicity loss. -/
theorem familyNorm_product_le (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (primaryFactor bodyFactor : ℝ) (hprimary : 0 ≤ primaryFactor) (hbody : 0 ≤ bodyFactor)
    (first second : KernelFamily primary body order) :
    familyNorm primary body order primaryFactor bodyFactor (familyProduct primary body order first second) ≤
      familyNorm primary body order primaryFactor bodyFactor first *
        familyNorm primary body order primaryFactor bodyFactor second := by
  let inputBound (left right : TruncatedArity order) : ℝ :=
    (gradeWeight primaryFactor bodyFactor left.val.1.val left.val.2.val * blockL2 primary body (first left).val) *
      (gradeWeight primaryFactor bodyFactor right.val.1.val right.val.2.val * blockL2 primary body (second right).val)
  let term (output left right : TruncatedArity order) :
      canonicalKernels primary body output.val.1.val output.val.2.val :=
    if hmatch : left.val.1.val + right.val.1.val = output.val.1.val ∧
        left.val.2.val + right.val.2.val = output.val.2.val then
      transportKernel primary body hmatch.1 hmatch.2 (homogeneousProduct primary body (first left) (second right))
    else 0
  let bound (output left right : TruncatedArity order) : ℝ :=
    if left.val.1.val + right.val.1.val = output.val.1.val ∧
        left.val.2.val + right.val.2.val = output.val.2.val then inputBound left right else 0
  have hterm (output left right : TruncatedArity order) :
      gradeWeight primaryFactor bodyFactor output.val.1.val output.val.2.val *
        blockL2 primary body (term output left right).val ≤ bound output left right := by
    dsimp only [term, bound]
    split_ifs with hmatch
    · rw [transportKernel_blockL2, ← hmatch.1, ← hmatch.2]
      exact weighted_homogeneousProduct_le primary body primaryFactor bodyFactor hprimary hbody _ _
    · simp only [Submodule.coe_zero, blockL2_zero, mul_zero, le_refl]
  have houtput (output : TruncatedArity order) :
      gradeWeight primaryFactor bodyFactor output.val.1.val output.val.2.val *
        blockL2 primary body ((familyProduct primary body order first second) output).val ≤
      ∑ left, ∑ right, bound output left right := by
    have hweight := gradeWeight_nonneg primaryFactor bodyFactor hprimary hbody output.val.1.val output.val.2.val
    change gradeWeight primaryFactor bodyFactor output.val.1.val output.val.2.val *
      blockL2 primary body (∑ left, ∑ right, term output left right).val ≤ _
    calc
      _ ≤ gradeWeight primaryFactor bodyFactor output.val.1.val output.val.2.val *
          ∑ left, blockL2 primary body (∑ right, term output left right).val :=
        mul_le_mul_of_nonneg_left (canonical_sum_l2_le primary body _ _) hweight
      _ ≤ gradeWeight primaryFactor bodyFactor output.val.1.val output.val.2.val *
          ∑ left, ∑ right, blockL2 primary body (term output left right).val := by
        apply mul_le_mul_of_nonneg_left _ hweight
        apply Finset.sum_le_sum
        intro left _
        exact canonical_sum_l2_le primary body _ _
      _ = ∑ left, ∑ right,
          gradeWeight primaryFactor bodyFactor output.val.1.val output.val.2.val *
            blockL2 primary body (term output left right).val := by simp only [Finset.mul_sum]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro left _
        apply Finset.sum_le_sum
        intro right _
        exact hterm output left right
  have hpair (left right : TruncatedArity order) : (∑ output, bound output left right) ≤ inputBound left right := by
    have hnonneg : 0 ≤ inputBound left right := mul_nonneg
      (mul_nonneg (gradeWeight_nonneg primaryFactor bodyFactor hprimary hbody _ _) (blockL2_nonneg primary body _))
      (mul_nonneg (gradeWeight_nonneg primaryFactor bodyFactor hprimary hbody _ _) (blockL2_nonneg primary body _))
    by_cases hexists : ∃ output : TruncatedArity order,
        left.val.1.val + right.val.1.val = output.val.1.val ∧
          left.val.2.val + right.val.2.val = output.val.2.val
    · obtain ⟨chosen, hchosen⟩ := hexists
      have hequal (output : TruncatedArity order) :
          (left.val.1.val + right.val.1.val = output.val.1.val ∧
            left.val.2.val + right.val.2.val = output.val.2.val) ↔ output = chosen := by
        constructor
        · intro hmatch
          apply Subtype.ext
          apply Prod.ext <;> apply Fin.ext
          · exact hmatch.1.symm.trans hchosen.1
          · exact hmatch.2.symm.trans hchosen.2
        · intro hmatch
          subst output
          exact hchosen
      simp only [bound, hequal, Finset.sum_ite_eq', Finset.mem_univ, if_true, le_refl]
    · have hnone (output : TruncatedArity order) :
          ¬(left.val.1.val + right.val.1.val = output.val.1.val ∧
            left.val.2.val + right.val.2.val = output.val.2.val) := fun h => hexists ⟨output, h⟩
      simpa only [bound, if_neg (hnone _), Finset.sum_const_zero] using hnonneg
  calc
    _ ≤ ∑ output, ∑ left, ∑ right, bound output left right :=
      Finset.sum_le_sum fun output _ => houtput output
    _ = ∑ left, ∑ right, ∑ output, bound output left right := sum_cycle bound
    _ ≤ ∑ left, ∑ right, inputBound left right := by
      apply Finset.sum_le_sum
      intro left _
      apply Finset.sum_le_sum
      intro right _
      exact hpair left right
    _ = _ := by simp only [inputBound, familyNorm, Finset.sum_mul_sum]

private theorem arity_eq_zero_iff (order : ℕ) (arity : TruncatedArity order) :
    arity = zeroArity order ↔ arity.val.1.val + arity.val.2.val = 0 := by
  constructor
  · intro hequal
    subst arity
    rfl
  · intro hzero
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · change arity.val.1.val = 0
      omega
    · change arity.val.2.val = 0
      omega

private theorem positiveArity_ne_zero (order : ℕ) (arity : PositiveArity order) :
    positiveArity order arity ≠ zeroArity order := by
  intro hequal
  have hzero := (arity_eq_zero_iff order (positiveArity order arity)).mp hequal
  change arity.val.1.val + arity.val.2.val = 0 at hzero
  have hpositive := arity.property.1
  omega

/-- A literal finite split into the unique scalar arity and all positive
arities, used to compare the two actual coefficient representations. -/
def aritySplit (order : ℕ) : Unit ⊕ PositiveArity order ≃ TruncatedArity order :=
  Equiv.ofBijective (Sum.elim (fun _ : Unit => zeroArity order) (positiveArity order)) (by
    constructor
    · intro first second hequal
      cases first with
      | inl first =>
        cases second with
        | inl second => cases first; cases second; rfl
        | inr second => exact False.elim ((positiveArity_ne_zero order second) hequal.symm)
      | inr first =>
        cases second with
        | inl second => exact False.elim ((positiveArity_ne_zero order first) hequal)
        | inr second =>
          apply congrArg Sum.inr
          apply Subtype.ext
          exact congrArg (fun arity : TruncatedArity order => arity.val) hequal
    · intro arity
      by_cases hzero : arity.val.1.val + arity.val.2.val = 0
      · exact ⟨Sum.inl (), ((arity_eq_zero_iff order arity).mpr hzero).symm⟩
      · exact ⟨Sum.inr ⟨arity.val, ⟨by omega, arity.property⟩⟩, rfl⟩)

theorem blockL2_scalarKernel (primary : FiniteDist Primary) (body : FiniteDist Body) (scalar : ℝ) :
    blockL2 primary body (scalarKernel primary body scalar).val = |scalar| := by
  simp only [blockL2, blockEnergy, scalarKernel, FiniteDist.l2Sq, FiniteDist.expectation,
    ← Finset.sum_mul, FiniteDist.sum_one, one_mul, Real.sqrt_sq_eq_abs]

/-- The family norm exactly equals the scalar-plus-positive graded norm of
the reconstructed current coefficient vector. -/
theorem familyNorm_coefficientsToFamily (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (primaryFactor bodyFactor : ℝ) (coefficient : CoefficientSpace primary body order) :
    familyNorm primary body order primaryFactor bodyFactor (coefficientsToFamily primary body order coefficient) =
      coefficientNorm primary body order primaryFactor bodyFactor coefficient := by
  unfold familyNorm
  rw [← (aritySplit order).sum_comp, Fintype.sum_sum_type, Fintype.sum_unique]
  change gradeWeight primaryFactor bodyFactor 0 0 *
      blockL2 primary body (coefficientsToFamily primary body order coefficient (zeroArity order)).val +
      (∑ arity : PositiveArity order,
        gradeWeight primaryFactor bodyFactor arity.val.1.val arity.val.2.val *
          blockL2 primary body (coefficientsToFamily primary body order coefficient (positiveArity order arity)).val) = _
  simp only [coefficientsToFamily_zero, coefficientsToFamily_positive,
    gradeWeight, pow_zero, one_mul, coefficientNorm]
  rw [blockL2_scalarKernel]

theorem coefficientsToFamily_inverse (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (family : KernelFamily primary body order) :
    coefficientsToFamily primary body order (familyCoefficientEquiv primary body order family) = family := by
  apply familyToCoefficients_injective primary body order
  apply Prod.ext
  · change scalarAt primary body
        (coefficientsToFamily primary body order (familyCoefficientEquiv primary body order family) (zeroArity order)) =
      scalarAt primary body (family (zeroArity order))
    rw [coefficientsToFamily_zero]
    rfl
  · funext arity
    exact coefficientsToFamily_positive primary body order _ arity

theorem familyNorm_eq_coefficientNorm (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (primaryFactor bodyFactor : ℝ) (family : KernelFamily primary body order) :
    familyNorm primary body order primaryFactor bodyFactor family =
      coefficientNorm primary body order primaryFactor bodyFactor (familyCoefficientEquiv primary body order family) := by
  rw [← familyNorm_coefficientsToFamily, coefficientsToFamily_inverse]

/-- Submultiplicativity in the manuscript's original coefficient space, after
the proved actual linear equivalence. It applies to the same finite square
sums, with no assumption that a normed algebra has already been constructed. -/
theorem coefficientNorm_product_le (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (primaryFactor bodyFactor : ℝ) (hprimary : 0 ≤ primaryFactor) (hbody : 0 ≤ bodyFactor)
    (first second : CoefficientSpace primary body order) :
    coefficientNorm primary body order primaryFactor bodyFactor (coefficientProduct primary body order first second) ≤
      coefficientNorm primary body order primaryFactor bodyFactor first *
        coefficientNorm primary body order primaryFactor bodyFactor second := by
  unfold coefficientProduct
  rw [← familyNorm_eq_coefficientNorm]
  have h := familyNorm_product_le primary body order primaryFactor bodyFactor hprimary hbody
    ((familyCoefficientEquiv primary body order).symm first)
    ((familyCoefficientEquiv primary body order).symm second)
  simpa only [familyNorm_eq_coefficientNorm, LinearEquiv.apply_symm_apply] using h

end

end CurrentAFT.GradedControlNorm
