import AFT.BlockFock

/-! # Exact circular Gaussian moments for the finite Fock isometry -/

namespace AFT
namespace FockGaussian

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

noncomputable def component : Measure ℝ := gaussianReal 0 (1 / 2)
noncomputable def plane : Measure (ℝ × ℝ) := component.prod component
noncomputable def circular : Measure ℂ :=
  plane.map (fun point => (point.1 : ℂ) + (point.2 : ℂ) * Complex.I)

instance component_probability : IsProbabilityMeasure component :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 (1 / 2)))
instance plane_probability : IsProbabilityMeasure plane :=
  inferInstanceAs (IsProbabilityMeasure (component.prod component))
instance circular_probability : IsProbabilityMeasure circular := by
  unfold circular
  exact Measure.isProbabilityMeasure_map (by fun_prop)

set_option backward.isDefEq.respectTransparency false in
/-- Exact moment-generating function of the squared circular radius. -/
theorem radial_mgf (parameter : ℝ) (hparameter : parameter < 1) :
    mgf (fun point : ℝ × ℝ => point.1 ^ 2 + point.2 ^ 2) plane parameter =
      1 / (1 - parameter) := by
  unfold mgf plane
  simp only [mul_add, Real.exp_add]
  rw [integral_prod_mul (fun value : ℝ => Real.exp (parameter * value ^ 2))
    (fun value : ℝ => Real.exp (parameter * value ^ 2)), component,
    BlockFock.gaussian_square_exp_integral]
  rw [← mul_inv, Real.mul_self_sqrt (by linarith : 0 ≤ 1 - parameter)]
  simp only [one_div]

/-- Integrability of the squared-radius exponential on the full required half line. -/
theorem radial_exp_integrable (parameter : ℝ) (hparameter : parameter < 1) :
    Integrable (fun point : ℝ × ℝ => Real.exp (parameter * (point.1 ^ 2 + point.2 ^ 2))) plane := by
  have h := (BlockFock.gaussian_square_exp_integrable parameter hparameter).mul_prod
    (BlockFock.gaussian_square_exp_integrable parameter hparameter)
  simpa only [mul_add, Real.exp_add, plane, component] using h

/-- The radius MGF is defined on a neighborhood of zero. -/
theorem zero_mem_radial_mgf_interior :
    0 ∈ interior (integrableExpSet (fun point : ℝ × ℝ => point.1 ^ 2 + point.2 ^ 2) plane) := by
  apply mem_interior.mpr
  refine ⟨Set.Iio 1, ?_, isOpen_Iio, by norm_num⟩
  intro parameter hparameter
  exact radial_exp_integrable parameter hparameter

set_option backward.isDefEq.respectTransparency false in
/-- The n-th derivative of the geometric-series generating function at zero. -/
theorem iteratedDeriv_geometric_zero (degree : ℕ) :
    iteratedDeriv degree (fun parameter : ℝ => 1 / (1 - parameter)) 0 = degree.factorial := by
  rw [iteratedDeriv_comp_const_sub degree (fun parameter : ℝ => 1 / parameter) 1]
  simp only [sub_zero, smul_eq_mul]
  have h := iteratedDerivWithin_one_div (𝕜 := ℝ) degree isOpen_univ (show (1 : ℝ) ∈ Set.univ from Set.mem_univ _)
  simp only [iteratedDerivWithin_univ, one_zpow, mul_one] at h
  rw [h]
  have hsign : (-1 : ℝ) ^ degree * (-1 : ℝ) ^ degree = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    (-1 : ℝ) ^ degree * ((-1 : ℝ) ^ degree * (degree.factorial : ℝ)) =
        ((-1 : ℝ) ^ degree * (-1 : ℝ) ^ degree) * (degree.factorial : ℝ) := by ring
    _ = _ := by rw [hsign, one_mul]

set_option backward.isDefEq.respectTransparency false in
/-- Every exact radial moment is the corresponding factorial. -/
theorem radial_moment (degree : ℕ) :
    (∫ point : ℝ × ℝ, (point.1 ^ 2 + point.2 ^ 2) ^ degree ∂plane) = degree.factorial := by
  have hm := iteratedDeriv_mgf_zero zero_mem_radial_mgf_interior degree
  simp only [Pi.pow_apply] at hm
  rw [← hm]
  have heq : mgf (fun point : ℝ × ℝ => point.1 ^ 2 + point.2 ^ 2) plane =ᶠ[nhds 0]
      (fun parameter => 1 / (1 - parameter)) := by
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with parameter hparameter
    exact radial_mgf parameter hparameter
  rw [Filter.EventuallyEq.iteratedDeriv_eq degree heq, iteratedDeriv_geometric_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The concrete circular Gaussian has the isotropic characteristic function. -/
theorem circular_charFun (argument : ℂ) :
    charFun circular argument = Complex.exp (-(Complex.normSq argument : ℂ) / 4) := by
  rw [circular, charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  have hpoint (point : ℝ × ℝ) :
      Complex.exp ((inner ℝ ((point.1 : ℂ) + (point.2 : ℂ) * Complex.I) argument : ℝ) * Complex.I) =
        Complex.exp ((argument.re * point.1 : ℝ) * Complex.I) *
          Complex.exp ((argument.im * point.2 : ℝ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply]
    change ((argument * (starRingEnd ℂ) ((point.1 : ℂ) + (point.2 : ℂ) * Complex.I)).re : ℂ) *
      Complex.I = _
    simp [Complex.mul_re, Complex.mul_im]
    ring
  simp_rw [hpoint]
  rw [plane, integral_prod_mul (fun value : ℝ => Complex.exp ((argument.re * value : ℝ) * Complex.I))
    (fun value : ℝ => Complex.exp ((argument.im * value : ℝ) * Complex.I))]
  simp_rw [Complex.ofReal_mul, ← charFun_apply_real, component, charFun_gaussianReal]
  rw [← Complex.exp_add]
  congr 1
  norm_num [Complex.normSq_apply]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- Exact rotation invariance, proved for the actual product Gaussian source. -/
theorem circular_rotation (rotation : ℂ) (hrotation : Complex.normSq rotation = 1) :
    circular.map (fun value => rotation * value) = circular := by
  apply Measure.ext_of_charFun
  funext argument
  rw [charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  have hinner (value : ℂ) : inner ℝ (rotation * value) argument =
      inner ℝ value ((starRingEnd ℂ) rotation * argument) := by
    rw [real_inner_eq_re_inner ℂ, real_inner_eq_re_inner ℂ,
      RCLike.inner_apply, RCLike.inner_apply]
    congr 1
    rw [map_mul]
    ring
  simp_rw [hinner]
  change charFun circular ((starRingEnd ℂ) rotation * argument) = _
  rw [circular_charFun, circular_charFun, Complex.normSq_mul,
    Complex.normSq_conj, hrotation, one_mul]

set_option backward.isDefEq.respectTransparency false in
/-- The diagonal mixed moment, using the exact factorial radius moment. -/
theorem diagonal_mixed_moment (degree : ℕ) :
    (∫ value : ℂ, value ^ degree * ((starRingEnd ℂ) value) ^ degree ∂circular) = degree.factorial := by
  rw [circular, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [← mul_pow, Complex.mul_conj, Complex.normSq_add_mul_I, ← Complex.ofReal_pow]
  rw [integral_complex_ofReal (f := fun point : ℝ × ℝ => (point.1 ^ 2 + point.2 ^ 2) ^ degree), radial_moment]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Rotation of an off-diagonal mixed moment multiplies it by its nontrivial
character. This is the exact orthogonality step, without an integrability
assumption hidden in a coefficient norm. -/
theorem mixed_moment_eq_zero_of_rotation (firstDegree secondDegree : ℕ)
    (rotation : ℂ) (hrotation : Complex.normSq rotation = 1)
    (hcharacter : rotation ^ firstDegree * ((starRingEnd ℂ) rotation) ^ secondDegree ≠ 1) :
    (∫ value : ℂ, value ^ firstDegree * ((starRingEnd ℂ) value) ^ secondDegree ∂circular) = 0 := by
  have h := congrArg (fun measure : Measure ℂ =>
    ∫ value, value ^ firstDegree * ((starRingEnd ℂ) value) ^ secondDegree ∂measure)
    (circular_rotation rotation hrotation)
  dsimp only at h
  rw [integral_map (by fun_prop) (by fun_prop)] at h
  have hfactor (value : ℂ) : (rotation * value) ^ firstDegree *
      ((starRingEnd ℂ) (rotation * value)) ^ secondDegree =
      (rotation ^ firstDegree * ((starRingEnd ℂ) rotation) ^ secondDegree) *
        (value ^ firstDegree * ((starRingEnd ℂ) value) ^ secondDegree) := by
    rw [map_mul, mul_pow, mul_pow]
    ring
  simp_rw [hfactor] at h
  rw [integral_const_mul] at h
  by_contra hne
  exact hcharacter ((mul_eq_right₀ hne).mp h)

set_option backward.isDefEq.respectTransparency false in
/-- An explicit unit rotation negates any prescribed off-diagonal character. -/
theorem offDiagonal_rotation (firstDegree secondDegree : ℕ) (hne : firstDegree ≠ secondDegree) :
    ∃ rotation : ℂ, Complex.normSq rotation = 1 ∧
      rotation ^ firstDegree * ((starRingEnd ℂ) rotation) ^ secondDegree = -1 := by
  let angle : ℝ := Real.pi / ((firstDegree : ℝ) - (secondDegree : ℝ))
  let rotation := Complex.exp ((angle : ℂ) * Complex.I)
  have hdiff : (firstDegree : ℝ) - (secondDegree : ℝ) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hne)
  refine ⟨rotation, ?_, ?_⟩
  · simp [rotation, Complex.normSq_eq_norm_sq, Complex.norm_exp, Complex.mul_re]
  · dsimp [rotation]
    rw [← Complex.exp_conj, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    have heq : (firstDegree : ℂ) * ((angle : ℂ) * Complex.I) +
        (secondDegree : ℂ) * (starRingEnd ℂ) ((angle : ℂ) * Complex.I) =
        (Real.pi : ℂ) * Complex.I := by
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
      have ha : ((firstDegree : ℝ) - (secondDegree : ℝ)) * angle = Real.pi := by
        dsimp [angle]
        field_simp
      have hac := congrArg Complex.ofReal ha
      push_cast at hac
      linear_combination Complex.I * hac
    rw [heq, Complex.exp_pi_mul_I]

/-- Exact mixed monomial moments of the actual circular Gaussian. -/
theorem mixed_moment (firstDegree secondDegree : ℕ) :
    (∫ value : ℂ, value ^ firstDegree * ((starRingEnd ℂ) value) ^ secondDegree ∂circular) =
      if firstDegree = secondDegree then (firstDegree.factorial : ℂ) else 0 := by
  split_ifs with heq
  · subst secondDegree
    exact diagonal_mixed_moment firstDegree
  · obtain ⟨rotation, hnorm, hcharacter⟩ := offDiagonal_rotation firstDegree secondDegree heq
    apply mixed_moment_eq_zero_of_rotation firstDegree secondDegree rotation hnorm
    rw [hcharacter]
    norm_num

set_option backward.isDefEq.respectTransparency false in
/-- Exact real radial moment under the circular pushforward. -/
theorem normSq_moment (degree : ℕ) :
    (∫ value : ℂ, Complex.normSq value ^ degree ∂circular) = degree.factorial := by
  rw [circular, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [Complex.normSq_add_mul_I]
  exact radial_moment degree

/-- All radial polynomial moments are integrable, as their exact integrals
are nonzero. -/
theorem normSq_power_integrable (degree : ℕ) :
    Integrable (fun value : ℂ => Complex.normSq value ^ degree) circular := by
  by_contra hnot
  have hz := integral_undef hnot
  rw [normSq_moment] at hz
  exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero degree)) hz

set_option backward.isDefEq.respectTransparency false in
/-- Mixed circular monomials are integrable in every finite degree. -/
theorem mixed_monomial_integrable (firstDegree secondDegree : ℕ) :
    Integrable (fun value : ℂ => value ^ firstDegree * ((starRingEnd ℂ) value) ^ secondDegree)
      circular := by
  apply ((integrable_const (1 : ℝ)).add
    (normSq_power_integrable (firstDegree + secondDegree))).mono'
      (by fun_prop : AEStronglyMeasurable _ circular)
  apply Filter.Eventually.of_forall
  intro value
  simp only [norm_mul, norm_pow, RCLike.norm_conj, Pi.add_apply]
  rw [← pow_add, Complex.normSq_eq_norm_sq, ← pow_mul, Nat.mul_comm 2 (firstDegree + secondDegree),
    pow_mul]
  nlinarith [sq_nonneg (‖value‖ ^ (firstDegree + secondDegree) - 1)]

variable {Coordinate : Type*} [Fintype Coordinate]

noncomputable def field : Measure (Coordinate → ℂ) := Measure.pi (fun _ : Coordinate => circular)

instance field_probability : IsProbabilityMeasure (field (Coordinate := Coordinate)) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Coordinate => circular)))

/-- Actual monomial in finitely many complex coordinates. -/
def monomial (degree : Coordinate → ℕ) (value : Coordinate → ℂ) : ℂ :=
  ∏ coordinate, value coordinate ^ degree coordinate

/-- The monomial's exact Fock weight, a product of coordinate factorials. -/
def monomialWeight (degree : Coordinate → ℕ) : ℕ :=
  ∏ coordinate, (degree coordinate).factorial

set_option backward.isDefEq.respectTransparency false in
/-- Full multivariate mixed-monomial orthogonality, for the actual Gaussian
product measure in every finite coordinate dimension. -/
theorem monomial_orthogonality (firstDegree secondDegree : Coordinate → ℕ) :
    (∫ value, monomial firstDegree value * (starRingEnd ℂ) (monomial secondDegree value)
      ∂(field (Coordinate := Coordinate))) =
      if firstDegree = secondDegree then (monomialWeight firstDegree : ℂ) else 0 := by
  classical
  simp only [monomial, map_prod, map_pow, ← Finset.prod_mul_distrib, field]
  rw [integral_fintype_prod_eq_prod
    (fun coordinate value => value ^ firstDegree coordinate *
      ((starRingEnd ℂ) value) ^ secondDegree coordinate)]
  simp_rw [mixed_moment]
  by_cases heq : firstDegree = secondDegree
  · subst secondDegree
    simp [monomialWeight]
  · simp only [heq, ↓reduceIte]
    obtain ⟨coordinate, hcoordinate⟩ := Function.ne_iff.mp heq
    apply Finset.prod_eq_zero (Finset.mem_univ coordinate)
    simp [hcoordinate]

set_option backward.isDefEq.respectTransparency false in
/-- Integrability needed to expand finite polynomial square norms. -/
theorem monomial_pair_integrable (firstDegree secondDegree : Coordinate → ℕ) :
    Integrable (fun value => monomial firstDegree value * (starRingEnd ℂ) (monomial secondDegree value))
      (field (Coordinate := Coordinate)) := by
  simp only [monomial, map_prod, map_pow, ← Finset.prod_mul_distrib, field]
  exact Integrable.fintype_prod (fun coordinate =>
    mixed_monomial_integrable (firstDegree coordinate) (secondDegree coordinate))

/-- Evaluation of an actual finite multivariate polynomial. Every selected
multi-index is retained, including the highest present degree. -/
noncomputable def polynomialEvaluation (terms : Finset (Coordinate → ℕ))
    (coefficient : (Coordinate → ℕ) → ℂ) (value : Coordinate → ℂ) : ℂ :=
  ∑ degree ∈ terms, coefficient degree * monomial degree value

set_option backward.isDefEq.respectTransparency false in
/-- Exact finite polynomial Parseval identity in complex form. -/
theorem polynomial_square_integral (terms : Finset (Coordinate → ℕ))
    (coefficient : (Coordinate → ℕ) → ℂ) :
    (∫ value, polynomialEvaluation terms coefficient value *
        (starRingEnd ℂ) (polynomialEvaluation terms coefficient value)
      ∂(field (Coordinate := Coordinate))) =
      ∑ degree ∈ terms, coefficient degree * (starRingEnd ℂ) (coefficient degree) *
        (monomialWeight degree : ℂ) := by
  classical
  have hterm (firstDegree secondDegree : Coordinate → ℕ) :
      Integrable (fun value => (coefficient firstDegree * (starRingEnd ℂ) (coefficient secondDegree)) *
        (monomial firstDegree value * (starRingEnd ℂ) (monomial secondDegree value))) field :=
    (monomial_pair_integrable firstDegree secondDegree).const_mul _
  have hexpand (value : Coordinate → ℂ) :
      polynomialEvaluation terms coefficient value *
          (starRingEnd ℂ) (polynomialEvaluation terms coefficient value) =
        ∑ firstDegree ∈ terms, ∑ secondDegree ∈ terms,
          (coefficient firstDegree * (starRingEnd ℂ) (coefficient secondDegree)) *
            (monomial firstDegree value * (starRingEnd ℂ) (monomial secondDegree value)) := by
    simp only [polynomialEvaluation, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro firstDegree _
    apply Finset.sum_congr rfl
    intro secondDegree _
    ring
  simp_rw [hexpand]
  rw [integral_finset_sum _ (fun firstDegree _ =>
    integrable_finset_sum _ (fun secondDegree _ => hterm firstDegree secondDegree))]
  apply Finset.sum_congr rfl
  intro firstDegree hfirst
  rw [integral_finset_sum _ (fun secondDegree _ => hterm firstDegree secondDegree)]
  simp_rw [integral_const_mul, monomial_orthogonality]
  simp [hfirst]

set_option backward.isDefEq.respectTransparency false in
/-- The exact Fock/Gaussian isometry for arbitrary actual finite polynomials,
with coordinate-factorial weights and no limit or truncated error term. -/
theorem polynomial_fock_isometry (terms : Finset (Coordinate → ℕ))
    (coefficient : (Coordinate → ℕ) → ℂ) :
    (∫ value, Complex.normSq (polynomialEvaluation terms coefficient value)
      ∂(field (Coordinate := Coordinate))) =
      ∑ degree ∈ terms, Complex.normSq (coefficient degree) * (monomialWeight degree : ℝ) := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [← Complex.mul_conj]
  rw [polynomial_square_integral]
  push_cast
  apply Finset.sum_congr rfl
  intro degree _
  rw [Complex.mul_conj]

/-- Coordinatewise complexification of two independent real Gaussian fields. -/
noncomputable def complexify (point : (Coordinate → ℝ) × (Coordinate → ℝ)) : Coordinate → ℂ :=
  fun index => (point.1 index : ℂ) + (point.2 index : ℂ) * Complex.I

set_option backward.isDefEq.respectTransparency false in
/-- The circular product measure is exactly the pushforward of the two real
Gaussian fields used in the concrete block estimate. -/
theorem complexify_map :
    ((BlockFock.realGaussianField (Index := Coordinate)).prod BlockFock.realGaussianField).map
      complexify = field := by
  have hpres := measurePreserving_arrowProdEquivProdArrow ℝ ℝ Coordinate
    (fun _ => component) (fun _ => component)
  change ((Measure.pi (fun _ : Coordinate => component)).prod
    (Measure.pi (fun _ : Coordinate => component))).map complexify = field
  rw [← hpres.map_eq, Measure.map_map (by unfold complexify; fun_prop) hpres.measurable]
  change (Measure.pi (fun _ : Coordinate => plane)).map
    (fun point index => (point index).1 + ((point index).2 : ℂ) * Complex.I) = field
  exact Measure.pi_map_pi (μ := fun _ : Coordinate => plane)
    (f := fun _ (point : ℝ × ℝ) => (point.1 : ℂ) + (point.2 : ℂ) * Complex.I)
    (fun _ => (by fun_prop))

set_option backward.isDefEq.respectTransparency false in
/-- The actual finite linear-block estimate in the same circular field as the
exact polynomial Fock isometry. -/
theorem normalized_linear_product_bound {State : Type*} [Fintype State]
    (law : FiniteDist State) (direction : State → Coordinate → ℝ)
    (hunit : ∀ state, ∑ index, direction state index ^ 2 = 1)
    (energy : ℝ) (henergy0 : 0 ≤ energy) (henergy : energy ≤ 1 / 4) :
    (∫ point, ∏ state, Complex.normSq (1 + ∑ index,
        ((Real.sqrt (energy * law.weight state) * direction state index : ℝ) : ℂ) * point index)
      ∂(field (Coordinate := Coordinate))) ≤
        4 * Real.exp (2 * ∑ index, BlockFock.normalizedLinearMean law direction energy index ^ 2) := by
  rw [← complexify_map, integral_map (by unfold complexify; fun_prop)
    (by apply Continuous.aestronglyMeasurable; fun_prop)]
  have hvalue (state : State) (point : (Coordinate → ℝ) × (Coordinate → ℝ)) :
      (∑ index, ((Real.sqrt (energy * law.weight state) * direction state index : ℝ) : ℂ) *
        complexify point index) = BlockFock.normalizedLinearValue law direction energy state point := by
    simp only [complexify, BlockFock.normalizedLinearValue, Complex.ofReal_mul,
      Complex.ofReal_sum, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_mul, mul_add]
    simp only [mul_assoc]
  simp_rw [hvalue]
  exact BlockFock.normalized_linear_product_gaussian_bound law direction hunit energy henergy0 henergy

set_option backward.isDefEq.respectTransparency false in
/-- Every finite family of real vectors with positive total energy admits the
unit-direction probability representation used in the Gaussian bound. -/
theorem linear_normalization {State : Type*} [Fintype State] [Nonempty Coordinate]
    (coefficient : State → Coordinate → ℝ)
    (henergy : 0 < ∑ state, ∑ index, coefficient state index ^ 2) :
    ∃ (law : FiniteDist State) (direction : State → Coordinate → ℝ),
      (∀ state, ∑ index, direction state index ^ 2 = 1) ∧
      ∀ state index,
        Real.sqrt ((∑ state, ∑ index, coefficient state index ^ 2) * law.weight state) *
          direction state index = coefficient state index := by
  classical
  let rowEnergy (state : State) := ∑ index, coefficient state index ^ 2
  let energy := ∑ state, rowEnergy state
  have hrow (state : State) : 0 ≤ rowEnergy state := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have henergy' : 0 < energy := henergy
  let law : FiniteDist State :=
    { weight := fun state => rowEnergy state / energy
      nonneg := fun state => div_nonneg (hrow state) henergy'.le
      sum_one := by rw [← Finset.sum_div]; exact div_self henergy'.ne' }
  let origin : Coordinate := Classical.choice inferInstance
  let direction (state : State) (index : Coordinate) :=
    if rowEnergy state = 0 then (if index = origin then (1 : ℝ) else 0)
    else coefficient state index / Real.sqrt (rowEnergy state)
  refine ⟨law, direction, ?_, ?_⟩
  · intro state
    by_cases hzero : rowEnergy state = 0
    · simp [direction, hzero]
    · have hsqrt := Real.sq_sqrt (hrow state)
      simp only [direction, if_neg hzero, div_pow, ← Finset.sum_div, hsqrt]
      exact div_self hzero
  · intro state index
    have hweight : energy * law.weight state = rowEnergy state := by
      dsimp [law]
      exact mul_div_cancel₀ _ henergy'.ne'
    change Real.sqrt (energy * law.weight state) * direction state index = _
    rw [hweight]
    by_cases hzero : rowEnergy state = 0
    · have hentry : coefficient state index ^ 2 = 0 := by
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun index _ => sq_nonneg (coefficient state index))).mp hzero
          index (Finset.mem_univ _)
      have hentry' : coefficient state index = 0 := by nlinarith [sq_nonneg (coefficient state index)]
      simp [direction, hzero, hentry']
    · simp only [direction, if_neg hzero]
      exact mul_div_cancel₀ _ (Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne (hrow state) (Ne.symm hzero)))

set_option backward.isDefEq.respectTransparency false in
/-- Concrete linear-block estimate for arbitrary real coefficient vectors.
The only smallness premise is their actual total squared Euclidean energy. -/
theorem linear_product_bound {State : Type*} [Fintype State] [Nonempty Coordinate]
    (coefficient : State → Coordinate → ℝ)
    (henergy : (∑ state, ∑ index, coefficient state index ^ 2) ≤ 1 / 4) :
    (∫ point, ∏ state, Complex.normSq (1 + ∑ index, (coefficient state index : ℂ) * point index)
      ∂(field (Coordinate := Coordinate))) ≤
        4 * Real.exp (2 * ∑ index, (∑ state, coefficient state index) ^ 2) := by
  have hnonneg : 0 ≤ ∑ state, ∑ index, coefficient state index ^ 2 := by positivity
  rcases eq_or_lt_of_le hnonneg with hzero | hpositive
  · have hentries : ∀ state index, coefficient state index = 0 := by
      intro state index
      have hrows := (Finset.sum_eq_zero_iff_of_nonneg (fun state _ =>
        Finset.sum_nonneg (fun index _ => sq_nonneg (coefficient state index)))).mp hzero.symm
      have hentry := (Finset.sum_eq_zero_iff_of_nonneg (fun index _ =>
        sq_nonneg (coefficient state index))).mp (hrows state (Finset.mem_univ _)) index (Finset.mem_univ _)
      nlinarith [sq_nonneg (coefficient state index)]
    simp only [hentries, Complex.ofReal_zero, zero_mul, Finset.sum_const_zero, add_zero,
      Complex.normSq_one, Finset.prod_const_one, zero_pow (by omega : 2 ≠ 0)]
    haveI : IsProbabilityMeasure (field (Coordinate := Coordinate)) := inferInstanceAs
      (IsProbabilityMeasure (Measure.pi (fun _ : Coordinate => circular)))
    norm_num
  · obtain ⟨law, direction, hunit, hcoeff⟩ := linear_normalization coefficient hpositive
    have h := normalized_linear_product_bound law direction hunit _ hpositive.le henergy
    simp only [BlockFock.normalizedLinearMean, hcoeff] at h
    exact h

end FockGaussian
end AFT
