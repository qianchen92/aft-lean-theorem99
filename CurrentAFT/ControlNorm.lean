import CurrentAFT.ControlProduct

/-!
# Actual Hilbert block energy and graded coefficient size

The block energy is the finite sum of squared density values weighted by
the true primary/body product reference. No pre-existing normed-algebra
structure is assumed. Disjoint tensor multiplication, slot relabeling, and
permutation averaging are verified on these finite sums before any graded
coefficient bound is formed.

The finite coefficient size uses the manuscript's sum of block L2 norms,
with degree-zero absolute value and multiplicative arity weights. This file
does not yet install a normed-algebra instance or assume an unproved product
law for complete truncated coefficient families.
-/

namespace CurrentAFT.ControlNorm

open AFT ControlCoordinates ControlProduct
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) :=
  Classical.decEq _

variable {Primary Body PS BS PT BT : Type*}
  [Fintype Primary] [Fintype Body] [Fintype PS] [Fintype BS] [Fintype PT] [Fintype BT]

/-- The genuine square L2 norm under the two product reference laws. -/
def blockEnergy (primary : FiniteDist Primary) (body : FiniteDist Body)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) : ℝ :=
  ((FiniteDist.independent (fun _ : PS => primary)).prod
    (FiniteDist.independent (fun _ : BS => body))).l2Sq (fun inputs => kernel inputs.1 inputs.2)

theorem blockEnergy_apply (primary : FiniteDist Primary) (body : FiniteDist Body)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) :
    blockEnergy primary body kernel = ∑ colors : PS → Primary, ∑ centers : BS → Body,
      (∏ index, primary.weight (colors index)) * (∏ index, body.weight (centers index)) *
        kernel colors centers ^ 2 := by
  simp only [blockEnergy, FiniteDist.l2Sq, FiniteDist.expectation, FiniteDist.prod_weight,
    FiniteDist.independent, Fintype.sum_prod_type]

theorem blockEnergy_nonneg (primary : FiniteDist Primary) (body : FiniteDist Body)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) : 0 ≤ blockEnergy primary body kernel :=
  FiniteDist.l2Sq_nonneg _ _

def blockL2 (primary : FiniteDist Primary) (body : FiniteDist Body)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) : ℝ :=
  Real.sqrt (blockEnergy primary body kernel)

theorem blockL2_nonneg (primary : FiniteDist Primary) (body : FiniteDist Body)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) : 0 ≤ blockL2 primary body kernel :=
  Real.sqrt_nonneg _

theorem blockL2_sq (primary : FiniteDist Primary) (body : FiniteDist Body)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) :
    blockL2 primary body kernel ^ 2 = blockEnergy primary body kernel :=
  Real.sq_sqrt (blockEnergy_nonneg primary body kernel)

private theorem finite_l2_triangle {State : Type*} [Fintype State]
    (law : FiniteDist State) (first second : State → ℝ) :
    Real.sqrt (law.l2Sq (fun state => first state + second state)) ≤
      Real.sqrt (law.l2Sq first) + Real.sqrt (law.l2Sq second) := by
  have hadd : law.l2Sq (fun state => first state + second state) =
      law.l2Sq first + 2 * law.expectation (fun state => first state * second state) + law.l2Sq second := by
    calc
      _ = ∑ state, (law.weight state * first state ^ 2 +
          2 * (law.weight state * (first state * second state)) + law.weight state * second state ^ 2) := by
        apply Finset.sum_congr rfl
        intro state _
        ring
      _ = _ := by
        simp only [FiniteDist.l2Sq, FiniteDist.expectation,
          Finset.sum_add_distrib, ← Finset.mul_sum]
  have hfirst := Real.sq_sqrt (FiniteDist.l2Sq_nonneg law first)
  have hsecond := Real.sq_sqrt (FiniteDist.l2Sq_nonneg law second)
  have hsum := Real.sq_sqrt (FiniteDist.l2Sq_nonneg law (fun state => first state + second state))
  have hcs := CanonicalMoments.expectation_mul_sq_le law first second
  have hinner : law.expectation (fun state => first state * second state) ≤
      Real.sqrt (law.l2Sq first) * Real.sqrt (law.l2Sq second) := by
    apply le_of_sq_le_sq _ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    calc
      _ ≤ law.l2Sq first * law.l2Sq second := hcs
      _ = _ := by rw [mul_pow, hfirst, hsecond]
  apply le_of_sq_le_sq _ (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  rw [hsum, hadd, add_sq, hfirst, hsecond]
  linarith

/-- The block triangle inequality is proved on the actual weighted finite
sum by Cauchy--Schwarz, rather than obtained from a normed-algebra premise. -/
theorem blockL2_add_le (primary : FiniteDist Primary) (body : FiniteDist Body)
    (first second : Kernel (Primary := Primary) (Body := Body) PS BS) :
    blockL2 primary body (first + second) ≤ blockL2 primary body first + blockL2 primary body second := by
  exact finite_l2_triangle
    ((FiniteDist.independent (fun _ : PS => primary)).prod (FiniteDist.independent (fun _ : BS => body)))
    (fun inputs => first inputs.1 inputs.2) (fun inputs => second inputs.1 inputs.2)

theorem blockEnergy_smul (primary : FiniteDist Primary) (body : FiniteDist Body)
    (scalar : ℝ) (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) :
    blockEnergy primary body (scalar • kernel) = scalar ^ 2 * blockEnergy primary body kernel := by
  rw [blockEnergy_apply, blockEnergy_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro colors _
  apply Finset.sum_congr rfl
  intro centers _
  ring

theorem blockL2_smul (primary : FiniteDist Primary) (body : FiniteDist Body)
    (scalar : ℝ) (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) :
    blockL2 primary body (scalar • kernel) = |scalar| * blockL2 primary body kernel := by
  rw [blockL2, blockEnergy_smul, Real.sqrt_mul (sq_nonneg scalar), Real.sqrt_sq_eq_abs]
  rfl

/-- Positive reference atoms make this genuine L2 norm separate every density
array, including nonsymmetric arrays. -/
theorem blockEnergy_eq_zero_iff (primary : FiniteDist Primary) (body : FiniteDist Body)
    (hprimary : ∀ color, 0 < primary.weight color) (hbody : ∀ center, 0 < body.weight center)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) :
    blockEnergy primary body kernel = 0 ↔ kernel = 0 := by
  constructor
  · intro hzero
    rw [blockEnergy_apply] at hzero
    have hrows := (Finset.sum_eq_zero_iff_of_nonneg (fun colors _ =>
      Finset.sum_nonneg fun centers _ => mul_nonneg
        (mul_nonneg (Finset.prod_nonneg fun index _ => primary.nonneg _)
          (Finset.prod_nonneg fun index _ => body.nonneg _)) (sq_nonneg _))).mp hzero
    funext colors centers
    have hentry := (Finset.sum_eq_zero_iff_of_nonneg (fun centers _ => mul_nonneg
      (mul_nonneg (Finset.prod_nonneg fun index _ => primary.nonneg _)
        (Finset.prod_nonneg fun index _ => body.nonneg _)) (sq_nonneg _))).mp
          (hrows colors (Finset.mem_univ _)) centers (Finset.mem_univ _)
    have hweight : 0 < (∏ index : PS, primary.weight (colors index)) *
        (∏ index : BS, body.weight (centers index)) :=
      mul_pos (Finset.prod_pos fun index _ => hprimary _) (Finset.prod_pos fun index _ => hbody _)
    have hsquare : kernel colors centers ^ 2 = 0 :=
      (mul_eq_zero.mp hentry).resolve_left (ne_of_gt hweight)
    exact sq_eq_zero_iff.mp hsquare
  · intro hzero
    simp only [hzero, blockEnergy_apply, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0),
      mul_zero, Finset.sum_const_zero]

theorem blockL2_eq_zero_iff (primary : FiniteDist Primary) (body : FiniteDist Body)
    (hprimary : ∀ color, 0 < primary.weight color) (hbody : ∀ center, 0 < body.weight center)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) :
    blockL2 primary body kernel = 0 ↔ kernel = 0 := by
  constructor
  · intro hzero
    apply (blockEnergy_eq_zero_iff primary body hprimary hbody kernel).mp
    have hsquare := blockL2_sq primary body kernel
    rw [hzero, zero_pow (by decide : 2 ≠ 0)] at hsquare
    exact hsquare.symm
  · intro hzero
    rw [blockL2, (blockEnergy_eq_zero_iff primary body hprimary hbody kernel).mpr hzero, Real.sqrt_zero]

/-- The word equivalence used to reindex the full finite product reference. -/
def slotWordEquiv (equiv : PS ≃ PT) : (PS → Primary) ≃ (PT → Primary) where
  toFun colors := colors ∘ equiv.symm
  invFun colors := colors ∘ equiv
  left_inv colors := by funext index; simp
  right_inv colors := by funext index; simp

theorem blockEnergy_reindex (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryEquiv : PS ≃ PT) (bodyEquiv : BS ≃ BT)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) :
    blockEnergy primary body (reindexKernel primaryEquiv bodyEquiv kernel) =
      blockEnergy primary body kernel := by
  rw [blockEnergy_apply, blockEnergy_apply]
  rw [← (slotWordEquiv primaryEquiv).sum_comp]
  apply Finset.sum_congr rfl
  intro colors _
  rw [← (slotWordEquiv (Primary := Body) bodyEquiv).sum_comp]
  apply Finset.sum_congr rfl
  intro centers _
  have hp : (∏ index : PT, primary.weight (colors (primaryEquiv.symm index))) =
      ∏ index : PS, primary.weight (colors index) :=
    primaryEquiv.symm.prod_comp (fun index => primary.weight (colors index))
  have hb : (∏ index : BT, body.weight (centers (bodyEquiv.symm index))) =
      ∏ index : BS, body.weight (centers index) :=
    bodyEquiv.symm.prod_comp (fun index => body.weight (centers index))
  simp only [slotWordEquiv, Equiv.coe_fn_mk, Function.comp_def, reindexKernel,
    Equiv.symm_apply_apply, hp, hb]

theorem blockL2_reindex (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryEquiv : PS ≃ PT) (bodyEquiv : BS ≃ BT)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) :
    blockL2 primary body (reindexKernel primaryEquiv bodyEquiv kernel) =
      blockL2 primary body kernel := by
  simp only [blockL2, blockEnergy_reindex]

/-- Exact tensor factorization for arbitrary joint kernels in each factor.
The two types of product-reference weights are both retained. -/
theorem blockEnergy_disjointTensor (primary : FiniteDist Primary) (body : FiniteDist Body)
    (first : Kernel (Primary := Primary) (Body := Body) PS BS)
    (second : Kernel (Primary := Primary) (Body := Body) PT BT) :
    blockEnergy primary body (disjointTensor first second) =
      blockEnergy primary body first * blockEnergy primary body second := by
  rw [blockEnergy_apply, blockEnergy_apply, blockEnergy_apply]
  rw [← (Equiv.sumArrowEquivProdArrow PS PT Primary).symm.sum_comp, Fintype.sum_prod_type]
  simp_rw [← (Equiv.sumArrowEquivProdArrow BS BT Body).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.sumArrowEquivProdArrow, Equiv.coe_fn_symm_mk,
    Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
    disjointTensor, Function.comp_def]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro firstColors _
  apply Finset.sum_congr rfl
  intro secondColors _
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro firstCenters _
  apply Finset.sum_congr rfl
  intro secondCenters _
  ring

theorem blockL2_disjointTensor (primary : FiniteDist Primary) (body : FiniteDist Body)
    (first : Kernel (Primary := Primary) (Body := Body) PS BS)
    (second : Kernel (Primary := Primary) (Body := Body) PT BT) :
    blockL2 primary body (disjointTensor first second) =
      blockL2 primary body first * blockL2 primary body second := by
  rw [blockL2, blockEnergy_disjointTensor, Real.sqrt_mul (blockEnergy_nonneg primary body first)]
  rfl

private theorem finite_expectation_square_le {State : Type*} [Fintype State]
    (law : FiniteDist State) (value : State → ℝ) :
    law.expectation value ^ 2 ≤ law.expectation (fun state => value state ^ 2) := by
  let mean := law.expectation value
  have hnonneg : 0 ≤ ∑ state, law.weight state * (value state - mean) ^ 2 :=
    Finset.sum_nonneg fun state _ => mul_nonneg (law.nonneg state) (sq_nonneg _)
  have hterm state : law.weight state * (value state - mean) ^ 2 =
      law.weight state * value state ^ 2 - 2 * mean * (law.weight state * value state) +
        mean ^ 2 * law.weight state := by ring
  simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, law.sum_one, mul_one] at hnonneg
  change 0 ≤ law.expectation (fun state => value state ^ 2) - 2 * mean * mean + mean ^ 2 at hnonneg
  dsimp only [mean] at hnonneg
  nlinarith

private theorem sum_rotate {First Second Third : Type*}
    [Fintype First] [Fintype Second] [Fintype Third] (term : First → Second → Third → ℝ) :
    (∑ first, ∑ second, ∑ third, term first second third) =
      ∑ third, ∑ first, ∑ second, term first second third := by
  calc
    _ = ∑ first, ∑ third, ∑ second, term first second third := by
      apply Finset.sum_congr rfl
      intro first _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Averaging actual density arrays contracts their square L2 energy. This
is finite Jensen, proved above from a nonnegative variance sum. -/
theorem blockEnergy_average_le {Choice : Type*} [Fintype Choice]
    (primary : FiniteDist Primary) (body : FiniteDist Body) (law : FiniteDist Choice)
    (family : Choice → Kernel (Primary := Primary) (Body := Body) PS BS) :
    blockEnergy primary body (fun colors centers => law.expectation (fun choice => family choice colors centers)) ≤
      law.expectation (fun choice => blockEnergy primary body (family choice)) := by
  rw [blockEnergy_apply]
  calc
    _ ≤ ∑ colors : PS → Primary, ∑ centers : BS → Body,
        (∏ index, primary.weight (colors index)) * (∏ index, body.weight (centers index)) *
          law.expectation (fun choice => family choice colors centers ^ 2) := by
      apply Finset.sum_le_sum
      intro colors _
      apply Finset.sum_le_sum
      intro centers _
      exact mul_le_mul_of_nonneg_left (finite_expectation_square_le law _)
        (mul_nonneg (Finset.prod_nonneg fun index _ => primary.nonneg _)
          (Finset.prod_nonneg fun index _ => body.nonneg _))
    _ = _ := by
      simp only [FiniteDist.expectation, Finset.mul_sum, blockEnergy_apply]
      rw [sum_rotate]
      apply Finset.sum_congr rfl
      intro choice _
      apply Finset.sum_congr rfl
      intro colors _
      apply Finset.sum_congr rfl
      intro centers _
      ring

omit [Fintype Primary] [Fintype Body] in
theorem symmetrize_eq_expectation (kernel : Kernel (Primary := Primary) (Body := Body) PS BS)
    (colors : PS → Primary) (centers : BS → Body) :
    symmetrize kernel colors centers =
      ((FiniteDist.uniform (Equiv.Perm PS)).prod (FiniteDist.uniform (Equiv.Perm BS))).expectation
        (fun orders => kernel (colors ∘ orders.1) (centers ∘ orders.2)) := by
  rw [symmetrize_apply]
  simp only [FiniteDist.expectation, FiniteDist.prod_weight, FiniteDist.uniform_weight,
    Fintype.sum_prod_type, ← Finset.mul_sum, mul_assoc]

theorem blockEnergy_symmetrize_le (primary : FiniteDist Primary) (body : FiniteDist Body)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) :
    blockEnergy primary body (symmetrize kernel) ≤ blockEnergy primary body kernel := by
  have hkernel : symmetrize kernel = fun colors centers =>
      ((FiniteDist.uniform (Equiv.Perm PS)).prod (FiniteDist.uniform (Equiv.Perm BS))).expectation
        (fun orders => (reindexKernel orders.1 orders.2 kernel) colors centers) := by
    funext colors centers
    exact symmetrize_eq_expectation kernel colors centers
  rw [hkernel]
  apply (blockEnergy_average_le primary body _
    (fun orders : Equiv.Perm PS × Equiv.Perm BS => reindexKernel orders.1 orders.2 kernel)).trans
  simp only [blockEnergy_reindex, FiniteDist.expectation, ← Finset.sum_mul,
    FiniteDist.sum_one, one_mul]
  exact le_rfl

theorem blockL2_symmetrize_le (primary : FiniteDist Primary) (body : FiniteDist Body)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) :
    blockL2 primary body (symmetrize kernel) ≤ blockL2 primary body kernel :=
  Real.sqrt_le_sqrt (blockEnergy_symmetrize_le primary body kernel)

/-- The manuscript's homogeneous star product is submultiplicative for the
actual Hilbert block norm, with no palette or population loss. -/
theorem homogeneousProduct_blockL2_le (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s r' s' : ℕ} (first : canonicalKernels primary body r s)
    (second : canonicalKernels primary body r' s') :
    blockL2 primary body (homogeneousProduct primary body first second).val ≤
      blockL2 primary body first.val * blockL2 primary body second.val := by
  change blockL2 primary body (symmetrize (finDisjointTensor first.val second.val)) ≤ _
  calc
    _ ≤ blockL2 primary body (finDisjointTensor first.val second.val) :=
      blockL2_symmetrize_le primary body _
    _ = _ := by
      unfold finDisjointTensor
      rw [blockL2_reindex, blockL2_disjointTensor]

/-- Multiplicative arity weights in factor form, avoiding any rounding of
the half powers of the two population sizes. -/
def gradeWeight (primaryFactor bodyFactor : ℝ) (r s : ℕ) : ℝ :=
  primaryFactor ^ r * bodyFactor ^ s

theorem gradeWeight_nonneg (primaryFactor bodyFactor : ℝ)
    (hprimary : 0 ≤ primaryFactor) (hbody : 0 ≤ bodyFactor) (r s : ℕ) :
    0 ≤ gradeWeight primaryFactor bodyFactor r s := by
  exact mul_nonneg (pow_nonneg hprimary _) (pow_nonneg hbody _)

theorem gradeWeight_add (primaryFactor bodyFactor : ℝ) (r s r' s' : ℕ) :
    gradeWeight primaryFactor bodyFactor (r + r') (s + s') =
      gradeWeight primaryFactor bodyFactor r s * gradeWeight primaryFactor bodyFactor r' s' := by
  simp only [gradeWeight, pow_add]
  ring

/-- The current population/radius choice: the body factor absorbs the radius
and the primary factor retains its separate population. -/
def publicGradeWeight (radius : ℝ) (primaryPool bodyPool r s : ℕ) : ℝ :=
  gradeWeight (Real.sqrt (primaryPool : ℝ))⁻¹ (radius * (Real.sqrt (bodyPool : ℝ))⁻¹) r s

theorem publicGradeWeight_add (radius : ℝ) (primaryPool bodyPool r s r' s' : ℕ) :
    publicGradeWeight radius primaryPool bodyPool (r + r') (s + s') =
      publicGradeWeight radius primaryPool bodyPool r s * publicGradeWeight radius primaryPool bodyPool r' s' :=
  gradeWeight_add _ _ _ _ _ _

theorem weighted_homogeneousProduct_le (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryFactor bodyFactor : ℝ) (hprimary : 0 ≤ primaryFactor) (hbody : 0 ≤ bodyFactor)
    {r s r' s' : ℕ} (first : canonicalKernels primary body r s)
    (second : canonicalKernels primary body r' s') :
    gradeWeight primaryFactor bodyFactor (r + r') (s + s') *
        blockL2 primary body (homogeneousProduct primary body first second).val ≤
      (gradeWeight primaryFactor bodyFactor r s * blockL2 primary body first.val) *
        (gradeWeight primaryFactor bodyFactor r' s' * blockL2 primary body second.val) := by
  apply (mul_le_mul_of_nonneg_left (homogeneousProduct_blockL2_le primary body first second)
    (gradeWeight_nonneg primaryFactor bodyFactor hprimary hbody _ _)).trans_eq
  rw [gradeWeight_add]
  ring

/-- The actual graded l1 sum of Hilbert block norms, with the scalar absolute
value in degree zero. This is not a pointwise bound on the public weight. -/
def coefficientNorm (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (primaryFactor bodyFactor : ℝ) (coefficient : CoefficientSpace primary body order) : ℝ :=
  |coefficient.1| + ∑ arity : PositiveArity order,
    gradeWeight primaryFactor bodyFactor arity.val.1.val arity.val.2.val *
      blockL2 primary body (coefficient.2 arity).val

theorem coefficientNorm_nonneg (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (primaryFactor bodyFactor : ℝ) (hprimary : 0 ≤ primaryFactor) (hbody : 0 ≤ bodyFactor)
    (coefficient : CoefficientSpace primary body order) :
    0 ≤ coefficientNorm primary body order primaryFactor bodyFactor coefficient := by
  apply add_nonneg (abs_nonneg _)
  apply Finset.sum_nonneg
  intro arity _
  exact mul_nonneg (gradeWeight_nonneg primaryFactor bodyFactor hprimary hbody _ _)
    (blockL2_nonneg primary body _)

end

end CurrentAFT.ControlNorm
