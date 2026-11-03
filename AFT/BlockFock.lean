import AFT.FiniteProbability

/-!
# Concrete finite symmetric tensors for the block Fock estimate

Tensors are coordinate arrays in an orthonormal basis, indexed by actual
finite tuples. Tensor products and symmetrization are defined explicitly.
Their Hilbert contraction and factorial estimates are proved from finite sums.
-/

namespace AFT
namespace BlockFock

open scoped BigOperators Classical

variable {State Index Index₁ Index₂ Color : Type*}

/-- Jensen's square inequality for an actual finite probability law. -/
theorem mean_square_le [Fintype State] (law : FiniteDist State) (value : State → ℝ) :
    (∑ state, law.weight state * value state) ^ 2 ≤
      ∑ state, law.weight state * value state ^ 2 := by
  let mean := ∑ state, law.weight state * value state
  have hvariance : 0 ≤ ∑ state, law.weight state * (value state - mean) ^ 2 :=
    Finset.sum_nonneg fun state _ => mul_nonneg (law.nonneg state) (sq_nonneg _)
  have hexpand : (∑ state, law.weight state * (value state - mean) ^ 2) =
      (∑ state, law.weight state * value state ^ 2) - mean ^ 2 := by
    calc
      _ = ∑ state, (law.weight state * value state ^ 2 -
          2 * mean * (law.weight state * value state) + law.weight state * mean ^ 2) := by
        apply Finset.sum_congr rfl
        intro state _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          ← Finset.sum_mul, law.sum_one]
        change _ - 2 * mean * mean + 1 * mean ^ 2 = _
        ring
  rw [hexpand] at hvariance
  exact sub_nonneg.mp hvariance

/-- A finite coordinate array for a tensor with slots indexed by `Index`. -/
abbrev Tensor (Index Color : Type*) := (Index → Color) → ℝ

/-- Squared Hilbert norm in the orthonormal tensor basis. -/
noncomputable def tensorEnergy [Fintype Index] [Fintype Color]
    (tensor : Tensor Index Color) : ℝ := ∑ point, tensor point ^ 2

/-- The actual uniform average over slot permutations. -/
noncomputable def symmetrize [Fintype Index] (tensor : Tensor Index Color) :
    Tensor Index Color := fun point =>
  ∑ permutation : Equiv.Perm Index,
    (FiniteDist.uniform (Equiv.Perm Index)).weight permutation * tensor (point ∘ permutation)

/-- Slot permutations merely reorder the orthonormal coordinate basis. -/
theorem permute_energy [Fintype Index] [Fintype Color]
    (tensor : Tensor Index Color) (permutation : Equiv.Perm Index) :
    (∑ point, tensor (point ∘ permutation) ^ 2) = tensorEnergy tensor := by
  let permutationEquiv : (Index → Color) ≃ (Index → Color) :=
    { toFun := fun point => point ∘ permutation
      invFun := fun point => point ∘ permutation.symm
      left_inv := by intro point; ext i; simp
      right_inv := by intro point; ext i; simp }
  exact permutationEquiv.sum_comp (fun point => tensor point ^ 2)

/-- Symmetrization is a contraction in the actual finite tensor Hilbert norm. -/
theorem symmetrize_energy_le [Fintype Index] [Fintype Color]
    (tensor : Tensor Index Color) : tensorEnergy (symmetrize tensor) ≤ tensorEnergy tensor := by
  calc
    tensorEnergy (symmetrize tensor) ≤ ∑ point, ∑ permutation : Equiv.Perm Index,
        (FiniteDist.uniform (Equiv.Perm Index)).weight permutation *
          tensor (point ∘ permutation) ^ 2 := by
      apply Finset.sum_le_sum
      intro point _
      exact mean_square_le _ _
    _ = ∑ permutation : Equiv.Perm Index,
        (FiniteDist.uniform (Equiv.Perm Index)).weight permutation * tensorEnergy tensor := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro permutation _
      rw [← Finset.mul_sum, permute_energy]
    _ = tensorEnergy tensor := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

/-- Tensor multiplication before projection onto symmetric arrays. -/
def tensorProduct (first : Tensor Index₁ Color) (second : Tensor Index₂ Color) :
    Tensor (Index₁ ⊕ Index₂) Color :=
  fun point => first (point ∘ Sum.inl) * second (point ∘ Sum.inr)

/-- The Hilbert norm of the concrete tensor product is multiplicative. -/
theorem tensorProduct_energy [Fintype Index₁] [Fintype Index₂] [Fintype Color]
    (first : Tensor Index₁ Color) (second : Tensor Index₂ Color) :
    tensorEnergy (tensorProduct first second) = tensorEnergy first * tensorEnergy second := by
  letI : DecidableEq (Index₁ ⊕ Index₂) := Classical.decEq _
  unfold tensorEnergy tensorProduct
  have hequiv := (Equiv.sumArrowEquivProdArrow Index₁ Index₂ Color).sum_comp
    (fun point => (first point.1 * second point.2) ^ 2)
  calc
    (∑ point : Index₁ ⊕ Index₂ → Color,
        (first (point ∘ Sum.inl) * second (point ∘ Sum.inr)) ^ 2) =
      ∑ point : (Index₁ → Color) × (Index₂ → Color),
        (first point.1 * second point.2) ^ 2 := hequiv
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp_rw [mul_pow]
      rw [Finset.sum_mul_sum]

/-- Multiplication of homogeneous polynomials is tensor product followed by
symmetrization, and therefore does not enlarge the product Hilbert norm. -/
theorem symmetric_product_energy_le [Fintype Index₁] [Fintype Index₂] [Fintype Color]
    (first : Tensor Index₁ Color) (second : Tensor Index₂ Color) :
    tensorEnergy (symmetrize (tensorProduct first second)) ≤
      tensorEnergy first * tensorEnergy second := by
  exact (symmetrize_energy_le _).trans_eq (tensorProduct_energy first second)

/-- The factorial inequality responsible for the radius enlargement by sqrt 2. -/
theorem factorial_add_le (firstDegree secondDegree : ℕ) :
    (firstDegree + secondDegree).factorial ≤
      2 ^ (firstDegree + secondDegree) * firstDegree.factorial * secondDegree.factorial := by
  rw [← Nat.add_choose_mul_factorial_mul_factorial firstDegree secondDegree]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.choose_le_two_pow _ _))

/-- The squared homogeneous Fock norm at radius `sqrt radiusSquared`. -/
noncomputable def homogeneousFockEnergy [Fintype Index] [Fintype Color]
    (radiusSquared : ℝ) (tensor : Tensor Index Color) : ℝ :=
  (Fintype.card Index).factorial * radiusSquared ^ Fintype.card Index * tensorEnergy tensor

/-- Concrete homogeneous Fock multiplication: enlarge each input's squared
radius by two. This follows from the actual tensor product and its averaging
projection, rather than an assumed multiplication-norm interface. -/
theorem homogeneous_product_fock_le [Fintype Index₁] [Fintype Index₂] [Fintype Color]
    (radiusSquared : ℝ) (hradius : 0 ≤ radiusSquared)
    (first : Tensor Index₁ Color) (second : Tensor Index₂ Color) :
    homogeneousFockEnergy radiusSquared (symmetrize (tensorProduct first second)) ≤
      homogeneousFockEnergy (2 * radiusSquared) first *
        homogeneousFockEnergy (2 * radiusSquared) second := by
  have hfirst : 0 ≤ tensorEnergy first := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hsecond : 0 ≤ tensorEnergy second := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hfactorial : ((Fintype.card Index₁ + Fintype.card Index₂).factorial : ℝ) ≤
      2 ^ (Fintype.card Index₁ + Fintype.card Index₂) *
        (Fintype.card Index₁).factorial * (Fintype.card Index₂).factorial := by
    exact_mod_cast factorial_add_le (Fintype.card Index₁) (Fintype.card Index₂)
  unfold homogeneousFockEnergy
  rw [Fintype.card_sum]
  calc
    _ ≤ (((Fintype.card Index₁ + Fintype.card Index₂).factorial : ℝ) *
        radiusSquared ^ (Fintype.card Index₁ + Fintype.card Index₂)) *
        (tensorEnergy first * tensorEnergy second) :=
      mul_le_mul_of_nonneg_left (symmetric_product_energy_le first second) (by positivity)
    _ ≤ (2 ^ (Fintype.card Index₁ + Fintype.card Index₂) *
        (Fintype.card Index₁).factorial * (Fintype.card Index₂).factorial *
        radiusSquared ^ (Fintype.card Index₁ + Fintype.card Index₂)) *
        (tensorEnergy first * tensorEnergy second) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hfactorial (pow_nonneg hradius _))
        (mul_nonneg hfirst hsecond)
    _ = _ := by simp only [mul_pow, pow_add]; ring

/-- A homogeneous factor times a complete finite polynomial. The sum contains
every homogeneous term of the second input, with no restriction on its degree. -/
theorem homogeneous_times_finite_fock_le [Fintype Index] [Fintype Color]
    (radiusSquared : ℝ) (hradius : 0 ≤ radiusSquared) (maxDegree : ℕ)
    (first : Tensor Index Color)
    (second : (degree : Fin (maxDegree + 1)) → Tensor (Fin degree.val) Color) :
    (∑ degree : Fin (maxDegree + 1),
      homogeneousFockEnergy radiusSquared
        (symmetrize (tensorProduct first (second degree)))) ≤
      homogeneousFockEnergy (2 * radiusSquared) first *
        ∑ degree : Fin (maxDegree + 1),
          homogeneousFockEnergy (2 * radiusSquared) (second degree) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun degree _ =>
    homogeneous_product_fock_le radiusSquared hradius first (second degree))

/-- Concrete factorial estimate for selecting quadratic and cubic blocks.
The cubic selection count is charged only a factor `M` in the squared norm,
which becomes `sqrt M` per cubic selection after taking square roots. -/
theorem nonlinear_selection_factorial_bound (pairCount tripleCount blocks : ℕ)
    (hblocks : pairCount + tripleCount ≤ blocks) :
    (2 * pairCount + 3 * tripleCount).factorial ≤
      64 ^ (pairCount + tripleCount) * blocks ^ tripleCount *
        (pairCount.factorial * tripleCount.factorial) ^ 2 := by
  let count := pairCount + tripleCount
  have hcount : count ≤ blocks := hblocks
  have ht : tripleCount ≤ count := by dsimp [count]; omega
  have hdegree : 2 * pairCount + 3 * tripleCount = 2 * count + tripleCount := by
    dsimp [count]; ring
  have hbase : (2 * count + tripleCount).factorial ≤
      (2 * count).factorial * (3 * count) ^ tripleCount := by
    rw [← Nat.factorial_mul_ascFactorial]
    apply Nat.mul_le_mul_left
    exact (Nat.ascFactorial_le_pow_add (2 * count) tripleCount).trans
      (Nat.pow_le_pow_left (by omega) tripleCount)
  have hcentral : (2 * count).factorial ≤ 2 ^ (2 * count) * count.factorial ^ 2 := by
    have h := factorial_add_le count count
    rw [← Nat.two_mul] at h
    simpa only [pow_two, Nat.mul_assoc] using h
  have hsplit : count.factorial ^ 2 ≤
      (2 ^ count * (pairCount.factorial * tripleCount.factorial)) ^ 2 := by
    apply Nat.pow_le_pow_left
    simpa [count, Nat.mul_assoc] using factorial_add_le pairCount tripleCount
  have hcubic : (3 * count) ^ tripleCount ≤ 4 ^ count * blocks ^ tripleCount := by
    rw [mul_pow]
    apply Nat.mul_le_mul
    · exact (Nat.pow_le_pow_left (by omega : 3 ≤ 4) tripleCount).trans
        (Nat.pow_le_pow_right (by omega : 0 < 4) ht)
    · exact Nat.pow_le_pow_left hcount tripleCount
  rw [hdegree]
  calc
    _ ≤ (2 * count).factorial * (3 * count) ^ tripleCount := hbase
    _ ≤ (2 ^ (2 * count) * count.factorial ^ 2) *
        (4 ^ count * blocks ^ tripleCount) := Nat.mul_le_mul hcentral hcubic
    _ ≤ (2 ^ (2 * count) *
        (2 ^ count * (pairCount.factorial * tripleCount.factorial)) ^ 2) *
          (4 ^ count * blocks ^ tripleCount) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hsplit)
    _ = _ := by
      have h64 : (64 : ℕ) ^ count = 4 ^ count * 4 ^ count * 4 ^ count := by
        rw [← mul_pow, ← mul_pow]
        norm_num
      change _ = 64 ^ count * blocks ^ tripleCount * _
      rw [h64, mul_pow, ← pow_mul, Nat.mul_comm count 2, pow_mul]
      norm_num
      ring

/-- The elementary quadratic-exponential majorant for one complex linear
factor. This is the only pointwise exponential estimate needed for the
linear-block argument. -/
theorem linear_factor_exp_bound (value : ℂ) :
    Complex.normSq (1 + value) ≤ Real.exp (2 * value.re + Complex.normSq value) := by
  have heq : Complex.normSq (1 + value) = 1 + 2 * value.re + Complex.normSq value := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re, Complex.add_im,
      Complex.one_im]
    ring
  rw [heq]
  linarith [Real.add_one_le_exp (2 * value.re + Complex.normSq value)]

/-- The actual entire finite linear product is bounded by a quadratic
exponential with its aggregate mean retained, including mean cancellation. -/
theorem linear_product_exp_bound [Fintype Index] (value : Index → ℂ) :
    (∏ index, Complex.normSq (1 + value index)) ≤
      Real.exp (2 * (∑ index, value index).re + ∑ index, Complex.normSq (value index)) := by
  have hprod := Finset.prod_le_prod (s := Finset.univ)
    (fun index _ => Complex.normSq_nonneg (1 + value index))
    (fun index _ => linear_factor_exp_bound (value index))
  rw [← Real.exp_sum] at hprod
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, Complex.re_sum] using hprod

section GaussianSquare

open MeasureTheory ProbabilityTheory
open scoped NNReal

set_option backward.isDefEq.respectTransparency false in
/-- Exact exponential-square moment of one real component of a standard
circular complex Gaussian. The variance is one half. -/
theorem gaussian_square_exp_integral (parameter : ℝ) :
    (∫ value : ℝ, Real.exp (parameter * value ^ 2)
      ∂(gaussianReal 0 (1 / 2))) = (Real.sqrt (1 - parameter))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 / 2 : ℝ≥0) ≠ 0)]
  have hpoint (value : ℝ) : gaussianPDFReal 0 (1 / 2) value •
      Real.exp (parameter * value ^ 2) =
        (Real.sqrt Real.pi)⁻¹ * Real.exp (-(1 - parameter) * value ^ 2) := by
    simp only [gaussianPDFReal, smul_eq_mul]
    have hn : (2 * Real.pi * (1 / 2 : ℝ)) = Real.pi := by ring
    norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat, sub_zero]
    rw [hn]
    norm_num only [mul_one_div_cancel, OfNat.ofNat_ne_zero, div_one, inv_one]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp_rw [hpoint]
  rw [MeasureTheory.integral_const_mul ((Real.sqrt Real.pi)⁻¹)
    (fun value : ℝ => Real.exp (-(1 - parameter) * value ^ 2)), integral_gaussian,
    Real.sqrt_div Real.pi_nonneg]
  have hp : Real.sqrt Real.pi ≠ 0 := Real.sqrt_ne_zero'.mpr Real.pi_pos
  field_simp

/-- The same square exponential is integrable precisely in the range needed
by the block argument; this follows from the nonzero exact integral. -/
theorem gaussian_square_exp_integrable (parameter : ℝ) (hparameter : parameter < 1) :
    Integrable (fun value : ℝ => Real.exp (parameter * value ^ 2))
      (gaussianReal 0 (1 / 2)) := by
  by_contra hnot
  have hzero := integral_undef hnot
  rw [gaussian_square_exp_integral] at hzero
  exact (inv_ne_zero (Real.sqrt_ne_zero'.mpr (sub_pos.mpr hparameter))) hzero

/-- Actual independent Gaussian coordinates used in the Fock representation. -/
noncomputable def realGaussianField [Fintype Index] : Measure (Index → ℝ) :=
  Measure.pi (fun _ : Index => gaussianReal 0 (1 / 2))

set_option backward.isDefEq.respectTransparency false in
/-- Every finite real linear projection of the concrete product Gaussian is
Gaussian with its computed variance. -/
theorem realGaussianField_projection [Fintype Index] (coefficient : Index → ℝ) :
    (realGaussianField (Index := Index)).map
      (fun point => ∑ index, coefficient index * point index) =
      gaussianReal 0 ⟨(∑ index, coefficient index ^ 2) / 2, by positivity⟩ := by
  letI : IsProbabilityMeasure (realGaussianField (Index := Index)) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Index => gaussianReal 0 (1 / 2))))
  apply Measure.ext_of_charFun
  funext argument
  have hm : Measurable (fun point : Index → ℝ => ∑ index, coefficient index * point index) := by fun_prop
  rw [charFun_apply_real, integral_map hm.aemeasurable (by fun_prop)]
  have hpoint (point : Index → ℝ) :
      Complex.exp ((argument : ℂ) * (∑ index, coefficient index * point index) * Complex.I) =
        ∏ index, Complex.exp (((argument * coefficient index : ℝ) : ℂ) *
          (point index : ℂ) * Complex.I) := by
    rw [← Complex.exp_sum]
    congr 1
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro index _
    ring
  simp_rw [hpoint]
  rw [realGaussianField, integral_fintype_prod_eq_prod
    (fun index (value : ℝ) => Complex.exp (((argument * coefficient index : ℝ) : ℂ) * (value : ℂ) * Complex.I))]
  simp_rw [← charFun_apply_real, charFun_gaussianReal]
  rw [← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub, Complex.ofReal_mul,
    NNReal.coe_mk, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_sum,
    Complex.ofReal_pow]
  simp only [mul_pow, Finset.sum_neg_distrib, Finset.sum_div]
  norm_num
  simp only [Finset.sum_mul]
  rw [← Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro index _
  ring

instance realGaussianField_probability [Fintype Index] :
    IsProbabilityMeasure (realGaussianField (Index := Index)) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Index => gaussianReal 0 (1 / 2))))

/-- A unit direction in the concrete Gaussian field has variance one half. -/
theorem realGaussianField_unit_projection [Fintype Index] (direction : Index → ℝ)
    (hunit : ∑ index, direction index ^ 2 = 1) :
    (realGaussianField (Index := Index)).map
      (fun point => ∑ index, direction index * point index) = gaussianReal 0 (1 / 2) := by
  simpa [hunit] using realGaussianField_projection direction

set_option backward.isDefEq.respectTransparency false in
/-- Exact square-exponential integral along a unit direction, uniformly in
both the number of coordinates and the direction. -/
theorem unit_projection_square_exp_integral [Fintype Index] (direction : Index → ℝ)
    (hunit : ∑ index, direction index ^ 2 = 1) (parameter : ℝ) :
    (∫ point, Real.exp (parameter * (∑ index, direction index * point index) ^ 2)
      ∂(realGaussianField (Index := Index))) = (Real.sqrt (1 - parameter))⁻¹ := by
  rw [← gaussian_square_exp_integral parameter,
    ← realGaussianField_unit_projection direction hunit,
    integral_map (show AEMeasurable
      (fun point : Index → ℝ => ∑ index, direction index * point index)
      (realGaussianField (Index := Index)) from (by fun_prop : Measurable _).aemeasurable)
      (by fun_prop)]

set_option backward.isDefEq.respectTransparency false in
/-- Integrability of the same projected square exponential. -/
theorem unit_projection_square_exp_integrable [Fintype Index] (direction : Index → ℝ)
    (hunit : ∑ index, direction index ^ 2 = 1) (parameter : ℝ) (hparameter : parameter < 1) :
    Integrable
      (fun point => Real.exp (parameter * (∑ index, direction index * point index) ^ 2))
      (realGaussianField (Index := Index)) := by
  have h := gaussian_square_exp_integrable parameter hparameter
  rw [← realGaussianField_unit_projection direction hunit] at h
  exact h.comp_measurable (by fun_prop)

set_option backward.isDefEq.respectTransparency false in
/-- A dimension-independent quadratic-exponential estimate for any finite
convex combination of unit projections of the actual Gaussian field.
This is the trace-only estimate used in the linear block argument. -/
theorem weighted_projection_exp_bound [Fintype State] [Fintype Index]
    (law : FiniteDist State) (direction : State → Index → ℝ)
    (hunit : ∀ state, ∑ index, direction state index ^ 2 = 1)
    (parameter : ℝ) (hparameter : parameter < 1) :
    Integrable (fun point => Real.exp (parameter *
      ∑ state, law.weight state * (∑ index, direction state index * point index) ^ 2))
      (realGaussianField (Index := Index)) ∧
    (∫ point, Real.exp (parameter *
      ∑ state, law.weight state * (∑ index, direction state index * point index) ^ 2)
      ∂(realGaussianField (Index := Index))) ≤ (Real.sqrt (1 - parameter))⁻¹ := by
  let projection (state : State) (point : Index → ℝ) :=
    ∑ index, direction state index * point index
  have hint (state : State) : Integrable
      (fun point => law.weight state * Real.exp (parameter * projection state point ^ 2))
      (realGaussianField (Index := Index)) :=
    (unit_projection_square_exp_integrable (direction state) (hunit state) parameter hparameter).const_mul _
  have hsumint : Integrable (fun point => ∑ state,
      law.weight state * Real.exp (parameter * projection state point ^ 2))
      (realGaussianField (Index := Index)) := integrable_finset_sum _ (fun state _ => hint state)
  have hpoint (point : Index → ℝ) :
      Real.exp (parameter * ∑ state, law.weight state * projection state point ^ 2) ≤
        ∑ state, law.weight state * Real.exp (parameter * projection state point ^ 2) := by
    have h := convexOn_exp.map_sum_le (t := Finset.univ)
      (w := law.weight) (p := fun state => parameter * projection state point ^ 2)
      (fun state _ => law.nonneg state) law.sum_one (fun _ _ => Set.mem_univ _)
    simpa only [smul_eq_mul, Finset.mul_sum, mul_left_comm] using h
  constructor
  · apply integrable_of_le_of_le (g₁ := 0) (g₂ := fun point => ∑ state,
        law.weight state * Real.exp (parameter * projection state point ^ 2))
      (by dsimp [projection]; exact (by fun_prop : Measurable _).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun point => (Real.exp_pos _).le))
      (Filter.Eventually.of_forall hpoint) (integrable_const 0)
    exact hsumint
  · calc
      _ ≤ ∫ point, ∑ state,
          law.weight state * Real.exp (parameter * projection state point ^ 2)
          ∂(realGaussianField (Index := Index)) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall (fun point => (Real.exp_pos _).le))
          hsumint (Filter.Eventually.of_forall hpoint)
      _ = ∑ state, law.weight state * (Real.sqrt (1 - parameter))⁻¹ := by
        rw [integral_finset_sum _ (fun state _ => hint state)]
        apply Finset.sum_congr rfl
        intro state _
        rw [integral_const_mul]
        congr 1
        exact unit_projection_square_exp_integral (direction state) (hunit state) parameter
      _ = _ := by rw [← Finset.sum_mul, law.sum_one, one_mul]

set_option backward.isDefEq.respectTransparency false in
/-- Exact moment-generating function of an arbitrary projection, including
zero projections. -/
theorem projection_linear_exp_integral [Fintype Index] (coefficient : Index → ℝ)
    (parameter : ℝ) :
    (∫ point, Real.exp (parameter * ∑ index, coefficient index * point index)
      ∂(realGaussianField (Index := Index))) =
      Real.exp (parameter ^ 2 * (∑ index, coefficient index ^ 2) / 4) := by
  have h := mgf_gaussianReal (realGaussianField_projection coefficient) parameter
  simpa only [mgf, NNReal.coe_mk, zero_mul, zero_add,
    show ((∑ index, coefficient index ^ 2) / 2) * parameter ^ 2 / 2 =
      parameter ^ 2 * (∑ index, coefficient index ^ 2) / 4 by ring] using h

set_option backward.isDefEq.respectTransparency false in
/-- Integrability of the linear Gaussian exponential, established for the
actual finite Gaussian product law. -/
theorem projection_linear_exp_integrable [Fintype Index] (coefficient : Index → ℝ)
    (parameter : ℝ) :
    Integrable (fun point => Real.exp (parameter * ∑ index, coefficient index * point index))
      (realGaussianField (Index := Index)) := by
  have h := integrable_exp_mul_gaussianReal (μ := 0)
    (v := ⟨(∑ index, coefficient index ^ 2) / 2, by positivity⟩) parameter
  rw [← realGaussianField_projection coefficient] at h
  exact h.comp_measurable (by fun_prop)

/-- Uniform numerical consequence of the exact Gaussian square moment. -/
theorem weighted_projection_exp_le_two [Fintype State] [Fintype Index]
    (law : FiniteDist State) (direction : State → Index → ℝ)
    (hunit : ∀ state, ∑ index, direction state index ^ 2 = 1)
    (parameter : ℝ) (hparameter : parameter ≤ 1 / 2) :
    (∫ point, Real.exp (parameter *
      ∑ state, law.weight state * (∑ index, direction state index * point index) ^ 2)
      ∂(realGaussianField (Index := Index))) ≤ 2 := by
  have h := (weighted_projection_exp_bound law direction hunit parameter (by linarith)).2
  apply h.trans
  have hsqrt : (1 / 2 : ℝ) ≤ Real.sqrt (1 - parameter) := by
    have hmono := Real.sqrt_le_sqrt (show (1 / 4 : ℝ) ≤ 1 - parameter by linarith)
    norm_num at hmono
    exact hmono
  have hpositive : 0 < Real.sqrt (1 - parameter) := by linarith
  apply (inv_le_iff_one_le_mul₀ hpositive).mpr
  linarith

set_option backward.isDefEq.respectTransparency false in
/-- Cauchy--Schwarz in square-integral form, retaining integrability of the
product needed when a Gaussian majorant is applied. -/
theorem nonnegative_integral_cauchy_schwarz {Sample : Type*} [MeasurableSpace Sample]
    (measure : Measure Sample) (first second : Sample → ℝ)
    (hfirst : AEStronglyMeasurable first measure)
    (hsecond : AEStronglyMeasurable second measure)
    (hfirst0 : ∀ sample, 0 ≤ first sample) (hsecond0 : ∀ sample, 0 ≤ second sample)
    (hfirstsq : Integrable (fun sample => first sample ^ 2) measure)
    (hsecondsq : Integrable (fun sample => second sample ^ 2) measure) :
    Integrable (fun sample => first sample * second sample) measure ∧
      (∫ sample, first sample * second sample ∂measure) ≤
        Real.sqrt (∫ sample, first sample ^ 2 ∂measure) *
          Real.sqrt (∫ sample, second sample ^ 2 ∂measure) := by
  have hf := (memLp_two_iff_integrable_sq hfirst).mpr hfirstsq
  have hg := (memLp_two_iff_integrable_sq hsecond).mpr hsecondsq
  refine ⟨hf.integrable_mul hg, ?_⟩
  have hholder : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr (by norm_num)
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hholder
    (Filter.Eventually.of_forall hfirst0) (Filter.Eventually.of_forall hsecond0)
    (by simpa using hf) (by simpa using hg)
  simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow] using h

set_option backward.isDefEq.respectTransparency false in
/-- A mean linear exponential and a trace-controlled quadratic exponential in
the actual Gaussian field. The bound has no dependence on the dimension. -/
theorem gaussian_linear_quadratic_bound [Fintype State] [Fintype Index]
    (law : FiniteDist State) (direction : State → Index → ℝ)
    (hunit : ∀ state, ∑ index, direction state index ^ 2 = 1)
    (mean : Index → ℝ) (energy : ℝ) (henergy : energy ≤ 1 / 4) :
    Integrable (fun point => Real.exp
      (2 * (∑ index, mean index * point index) + energy *
        ∑ state, law.weight state * (∑ index, direction state index * point index) ^ 2))
      (realGaussianField (Index := Index)) ∧
    (∫ point, Real.exp
      (2 * (∑ index, mean index * point index) + energy *
        ∑ state, law.weight state * (∑ index, direction state index * point index) ^ 2)
      ∂(realGaussianField (Index := Index))) ≤
        2 * Real.exp (2 * ∑ index, mean index ^ 2) := by
  let first (point : Index → ℝ) := Real.exp (2 * ∑ index, mean index * point index)
  let second (point : Index → ℝ) := Real.exp (energy *
    ∑ state, law.weight state * (∑ index, direction state index * point index) ^ 2)
  have hfirstsq : (fun point => first point ^ 2) =
      (fun point => Real.exp (4 * ∑ index, mean index * point index)) := by
    funext point
    dsimp [first]
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hsecondsq : (fun point => second point ^ 2) =
      (fun point => Real.exp ((2 * energy) *
        ∑ state, law.weight state * (∑ index, direction state index * point index) ^ 2)) := by
    funext point
    dsimp [second]
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hintfirst : Integrable (fun point => first point ^ 2) realGaussianField := by
    rw [hfirstsq]
    exact projection_linear_exp_integrable mean 4
  have hintsecond : Integrable (fun point => second point ^ 2) realGaussianField := by
    rw [hsecondsq]
    exact (weighted_projection_exp_bound law direction hunit (2 * energy) (by linarith)).1
  have hcs := nonnegative_integral_cauchy_schwarz realGaussianField first second
    (by dsimp [first]; exact (by fun_prop : Measurable _).aestronglyMeasurable)
    (by dsimp [second]; exact (by fun_prop : Measurable _).aestronglyMeasurable)
    (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le) hintfirst hintsecond
  have hproduct : (fun point => first point * second point) =
      (fun point => Real.exp
        (2 * (∑ index, mean index * point index) + energy *
          ∑ state, law.weight state * (∑ index, direction state index * point index) ^ 2)) := by
    funext point
    exact (Real.exp_add _ _).symm
  refine ⟨hproduct ▸ hcs.1, ?_⟩
  rw [hproduct, hfirstsq, hsecondsq, projection_linear_exp_integral] at hcs
  have hquad := weighted_projection_exp_le_two law direction hunit (2 * energy) (by linarith)
  have hsqrtexp : Real.sqrt (Real.exp ((4 : ℝ) ^ 2 * (∑ index, mean index ^ 2) / 4)) =
      Real.exp (2 * ∑ index, mean index ^ 2) := by
    have heq : (4 : ℝ) ^ 2 * (∑ index, mean index ^ 2) / 4 =
        (2 : ℕ) * (2 * ∑ index, mean index ^ 2) := by norm_num; ring
    rw [heq, Real.exp_nat_mul, Real.sqrt_sq (Real.exp_pos _).le]
  apply hcs.2.trans
  rw [hsqrtexp]
  have hsqrt := Real.sqrt_le_sqrt hquad
  have htwo : Real.sqrt 2 ≤ (2 : ℝ) := by
    apply (Real.sqrt_le_iff).mpr
    norm_num
  nlinarith [mul_le_mul_of_nonneg_left (hsqrt.trans htwo)
    (Real.exp_pos (2 * ∑ index, mean index ^ 2)).le]

/-- A linear factor whose squared coefficient norm is `energy * law.weight`.
The two actual independent real Gaussian fields form the circular field. -/
noncomputable def normalizedLinearValue [Fintype Index] [Fintype State]
    (law : FiniteDist State) (direction : State → Index → ℝ) (energy : ℝ)
    (state : State) (point : (Index → ℝ) × (Index → ℝ)) : ℂ :=
  (Real.sqrt (energy * law.weight state) : ℂ) *
    (((∑ index, direction state index * point.1 index : ℝ) : ℂ) +
      ((∑ index, direction state index * point.2 index : ℝ) : ℂ) * Complex.I)

/-- The aggregate mean vector, with its cancellations preserved. -/
noncomputable def normalizedLinearMean [Fintype State]
    (law : FiniteDist State) (direction : State → Index → ℝ) (energy : ℝ) (index : Index) : ℝ :=
  ∑ state, Real.sqrt (energy * law.weight state) * direction state index

set_option backward.isDefEq.respectTransparency false in
/-- Complete finite linear-block Gaussian estimate. It is dimension independent
and retains the actual aggregate mean rather than summing individual means.
This is the Gaussian-integral part of V7's linear Fock argument. -/
theorem normalized_linear_product_gaussian_bound [Fintype State] [Fintype Index]
    (law : FiniteDist State) (direction : State → Index → ℝ)
    (hunit : ∀ state, ∑ index, direction state index ^ 2 = 1)
    (energy : ℝ) (henergy0 : 0 ≤ energy) (henergy : energy ≤ 1 / 4) :
    (∫ point, ∏ state, Complex.normSq
        (1 + normalizedLinearValue law direction energy state point)
      ∂((realGaussianField (Index := Index)).prod realGaussianField)) ≤
        4 * Real.exp (2 * ∑ index, normalizedLinearMean law direction energy index ^ 2) := by
  let mean := normalizedLinearMean law direction energy
  let majorant₁ (point : Index → ℝ) := Real.exp
    (2 * (∑ index, mean index * point index) + energy *
      ∑ state, law.weight state * (∑ index, direction state index * point index) ^ 2)
  let majorant₂ (point : Index → ℝ) := Real.exp
    (energy * ∑ state, law.weight state * (∑ index, direction state index * point index) ^ 2)
  have hfirst := gaussian_linear_quadratic_bound law direction hunit mean energy henergy
  have hsecond := weighted_projection_exp_bound law direction hunit energy (by linarith)
  have hsecondbound := weighted_projection_exp_le_two law direction hunit energy (by linarith)
  have hmajorantInt : Integrable (fun point => majorant₁ point.1 * majorant₂ point.2)
      ((realGaussianField (Index := Index)).prod realGaussianField) := hfirst.1.mul_prod hsecond.1
  have hre (point : (Index → ℝ) × (Index → ℝ)) :
      (∑ state, normalizedLinearValue law direction energy state point).re =
        ∑ index, mean index * point.1 index := by
    simp only [normalizedLinearValue, Complex.re_sum, Complex.mul_re, Complex.add_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, add_zero]
    dsimp [mean, normalizedLinearMean]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro index _
    apply Finset.sum_congr rfl
    intro state _
    ring
  have hnorm (state : State) (point : (Index → ℝ) × (Index → ℝ)) :
      Complex.normSq (normalizedLinearValue law direction energy state point) =
        energy * law.weight state *
          ((∑ index, direction state index * point.1 index) ^ 2 +
            (∑ index, direction state index * point.2 index) ^ 2) := by
    dsimp [normalizedLinearValue]
    rw [map_mul, Complex.normSq_ofReal, Complex.normSq_add_mul_I]
    rw [Real.mul_self_sqrt (mul_nonneg henergy0 (law.nonneg state))]
  have hpoint (point : (Index → ℝ) × (Index → ℝ)) :
      (∏ state, Complex.normSq (1 + normalizedLinearValue law direction energy state point)) ≤
        majorant₁ point.1 * majorant₂ point.2 := by
    have h := linear_product_exp_bound (fun state => normalizedLinearValue law direction energy state point)
    rw [hre] at h
    simp_rw [hnorm] at h
    apply h.trans_eq
    dsimp [majorant₁, majorant₂]
    rw [← Real.exp_add]
    congr 1
    simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib, mul_assoc, add_assoc]
  calc
    _ ≤ ∫ point, majorant₁ point.1 * majorant₂ point.2
        ∂((realGaussianField (Index := Index)).prod realGaussianField) :=
      integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun _ => Finset.prod_nonneg
          (fun _ _ => Complex.normSq_nonneg _)))
        hmajorantInt (Filter.Eventually.of_forall hpoint)
    _ = (∫ point, majorant₁ point ∂(realGaussianField (Index := Index))) *
        (∫ point, majorant₂ point ∂(realGaussianField (Index := Index))) := integral_prod_mul _ _
    _ ≤ (2 * Real.exp (2 * ∑ index, mean index ^ 2)) * 2 :=
      mul_le_mul hfirst.2 hsecondbound
        (integral_nonneg (fun _ => (Real.exp_pos _).le)) (by positivity)
    _ = _ := by ring

end GaussianSquare

end BlockFock
end AFT
