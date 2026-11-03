import AFT.TensorFock

/-! # Concrete polynomial representation for nonlinear block estimates -/

namespace AFT
namespace NonlinearFock

open MeasureTheory TensorFock
open scoped BigOperators Classical

variable {Slot OtherSlot Coordinate Term : Type*}
variable [Fintype Slot] [Fintype OtherSlot] [Fintype Coordinate]

/-- A change of slot names does not change a tensor polynomial. -/
theorem tensorEvaluation_reindex (equiv : Slot ≃ OtherSlot)
    (tensor : BlockFock.Tensor Slot Coordinate) (value : Coordinate → ℂ) :
    tensorEvaluation (fun word : OtherSlot → Coordinate => tensor (word ∘ equiv)) value =
      tensorEvaluation tensor value := by
  let e : (OtherSlot → Coordinate) ≃ (Slot → Coordinate) :=
    { toFun := fun word => word ∘ equiv
      invFun := fun word => word ∘ equiv.symm
      left_inv := by intro word; ext index; simp
      right_inv := by intro word; ext index; simp }
  have hmonomial (word : OtherSlot → Coordinate) :
      wordMonomial (word ∘ equiv) value = wordMonomial word value :=
    equiv.prod_comp (fun index => value (word index))
  have h := e.sum_comp (fun word => (tensor word : ℂ) * wordMonomial word value)
  change (∑ word : OtherSlot → Coordinate, (tensor (word ∘ equiv) : ℂ) *
    wordMonomial (word ∘ equiv) value) = _ at h
  simpa only [hmonomial, tensorEvaluation] using h

/-- Tensor evaluation is linear in a finite sum of actual arrays. -/
theorem tensorEvaluation_sum (terms : Finset Term) (tensor : Term → BlockFock.Tensor Slot Coordinate)
    (value : Coordinate → ℂ) :
    tensorEvaluation (fun word => ∑ term ∈ terms, tensor term word) value =
      ∑ term ∈ terms, tensorEvaluation (tensor term) value := by
  simp only [tensorEvaluation, Complex.ofReal_sum, Finset.sum_mul]
  exact Finset.sum_comm

/-- Tensor evaluation is linear under real scalar multiplication. -/
theorem tensorEvaluation_smul (scalar : ℝ) (tensor : BlockFock.Tensor Slot Coordinate)
    (value : Coordinate → ℂ) :
    tensorEvaluation (fun word => scalar * tensor word) value = (scalar : ℂ) * tensorEvaluation tensor value := by
  simp only [tensorEvaluation, Complex.ofReal_mul, Finset.mul_sum, mul_assoc]

omit [Fintype Coordinate] in
/-- The permutation average really is a symmetric tensor. -/
theorem symmetrize_symmetric (tensor : BlockFock.Tensor Slot Coordinate)
    (word : Slot → Coordinate) (permutation : Equiv.Perm Slot) :
    BlockFock.symmetrize tensor (word ∘ permutation) = BlockFock.symmetrize tensor word := by
  simp only [BlockFock.symmetrize, FiniteDist.uniform_weight, ← Finset.mul_sum]
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft permutation) (fun p : Equiv.Perm Slot => tensor (word ∘ p))

/-- Averaging over slot permutations leaves the actual polynomial unchanged. -/
theorem tensorEvaluation_symmetrize (tensor : BlockFock.Tensor Slot Coordinate) (value : Coordinate → ℂ) :
    tensorEvaluation (BlockFock.symmetrize tensor) value = tensorEvaluation tensor value := by
  unfold BlockFock.symmetrize
  rw [tensorEvaluation_sum]
  simp_rw [tensorEvaluation_smul, tensorEvaluation_reindex]
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, FiniteDist.sum_one]
  simp

/-- A finite tensor-polynomial certificate, with all its symmetric coefficients
and exact evaluation identity retained. -/
def IsTensorPolynomial (function : (Coordinate → ℂ) → ℂ) : Prop :=
  ∃ (degrees : Finset ℕ) (tensor : (degree : ℕ) → BlockFock.Tensor (Fin degree) Coordinate),
    (∀ degree ∈ degrees, ∀ word (permutation : Equiv.Perm (Fin degree)),
      tensor degree (word ∘ permutation) = tensor degree word) ∧
    ∀ value, function value = seriesEvaluation degrees tensor value

omit [Fintype Slot] [Fintype OtherSlot] in
set_option backward.isDefEq.respectTransparency false in
/-- Every actual finite sum of homogeneous tensors has an exact symmetric
coefficient representation. No analytic estimate is assumed in this conversion. -/
theorem finite_homogeneous_sum_polynomial [Fintype Term]
    (Slots : Term → Type*) [∀ term, Fintype (Slots term)]
    (tensor : (term : Term) → BlockFock.Tensor (Slots term) Coordinate) :
    IsTensorPolynomial (fun value => ∑ term, tensorEvaluation (tensor term) value) := by
  let bound := ∑ term, Fintype.card (Slots term)
  let piece (degree : ℕ) (term : Term) : BlockFock.Tensor (Fin degree) Coordinate :=
    if h : Fintype.card (Slots term) = degree then
      (fun word => tensor term (word ∘ Fintype.equivFinOfCardEq h)) else (fun _ => 0)
  let grouped (degree : ℕ) : BlockFock.Tensor (Fin degree) Coordinate :=
    fun word => ∑ term, piece degree term word
  refine ⟨Finset.range (bound + 1), fun degree => BlockFock.symmetrize (grouped degree), ?_, ?_⟩
  · intro degree _ word permutation
    exact symmetrize_symmetric _ _ _
  · intro value
    have hpiece (degree : ℕ) (term : Term) :
        tensorEvaluation (piece degree term) value =
          if Fintype.card (Slots term) = degree then tensorEvaluation (tensor term) value else 0 := by
      by_cases h : Fintype.card (Slots term) = degree
      · simp only [piece, dif_pos h, if_pos h]
        exact tensorEvaluation_reindex _ _ _
      · simp [piece, h, tensorEvaluation]
    simp only [seriesEvaluation, tensorEvaluation_symmetrize]
    simp only [grouped, tensorEvaluation_sum, hpiece]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro term _
    have hbound : Fintype.card (Slots term) ≤ bound := by
      dsimp [bound]
      exact Finset.single_le_sum (f := fun term => Fintype.card (Slots term))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ term)
    simp [Finset.mem_range, Nat.lt_succ_of_le hbound]

/-- The coordinate array for the actual product of finitely many homogeneous
polynomials, with one disjoint slot family per factor. -/
noncomputable def familyTensor [Fintype Term] (Slots : Term → Type*)
    (tensor : (term : Term) → BlockFock.Tensor (Slots term) Coordinate) :
    BlockFock.Tensor (Sigma Slots) Coordinate :=
  fun word => ∏ term, tensor term (fun slot => word ⟨term, slot⟩)

omit [Fintype Slot] [Fintype OtherSlot] in
set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Products of actual tensor polynomials have the expected disjoint-slot
coordinate array. -/
theorem family_tensor_evaluation [Fintype Term] (Slots : Term → Type*)
    [∀ term, Fintype (Slots term)] (tensor : (term : Term) → BlockFock.Tensor (Slots term) Coordinate)
    (value : Coordinate → ℂ) :
    tensorEvaluation (familyTensor Slots tensor) value = ∏ term, tensorEvaluation (tensor term) value := by
  letI : DecidableEq (Sigma Slots) := Classical.decEq _
  have h := (Equiv.piCurry (fun term (_ : Slots term) => Coordinate)).sum_comp
    (fun word => ∏ term, ((tensor term (word term) : ℂ) * wordMonomial (word term) value))
  unfold tensorEvaluation familyTensor wordMonomial
  simp only [Complex.ofReal_prod, Fintype.prod_sigma]
  calc
    _ = ∑ word : Sigma Slots → Coordinate,
        ∏ term, ((tensor term (fun slot => word ⟨term, slot⟩) : ℂ) *
          ∏ slot, value (word ⟨term, slot⟩)) := by simp only [Finset.prod_mul_distrib]
    _ = ∑ word : (term : Term) → Slots term → Coordinate,
        ∏ term, ((tensor term (word term) : ℂ) * ∏ slot, value (word term slot)) := h
    _ = _ := (Fintype.prod_sum (fun term (word : Slots term → Coordinate) =>
      (tensor term word : ℂ) * ∏ slot, value (word slot))).symm

omit [Fintype Slot] [Fintype OtherSlot] in
set_option backward.isDefEq.respectTransparency false in
/-- Actual tensor Hilbert energies multiply across disjoint slot families. -/
theorem family_tensor_energy [Fintype Term] (Slots : Term → Type*)
    [∀ term, Fintype (Slots term)] (tensor : (term : Term) → BlockFock.Tensor (Slots term) Coordinate) :
    BlockFock.tensorEnergy (familyTensor Slots tensor) = ∏ term, BlockFock.tensorEnergy (tensor term) := by
  letI : DecidableEq (Sigma Slots) := Classical.decEq _
  have h := (Equiv.piCurry (fun term (_ : Slots term) => Coordinate)).sum_comp
    (fun word => ∏ term, (tensor term (word term)) ^ 2)
  unfold BlockFock.tensorEnergy familyTensor
  simp_rw [← Finset.prod_pow]
  calc
    _ = ∑ word : (term : Term) → Slots term → Coordinate,
        ∏ term, tensor term (word term) ^ 2 := h
    _ = _ := (Fintype.prod_sum (fun term (word : Slots term → Coordinate) =>
      tensor term word ^ 2)).symm

omit [Fintype Slot] [Fintype OtherSlot] in
/-- A concrete finite product of finite homogeneous block polynomials has a
full symmetric tensor representation, obtained by expanding every choice. -/
theorem finite_block_product_polynomial [Fintype Term]
    (Choice : Term → Type*) [∀ term, Fintype (Choice term)]
    (Slots : (term : Term) → Choice term → Type*) [∀ term choice, Fintype (Slots term choice)]
    (tensor : (term : Term) → (choice : Choice term) → BlockFock.Tensor (Slots term choice) Coordinate) :
    IsTensorPolynomial (fun value => ∏ term, ∑ choice, tensorEvaluation (tensor term choice) value) := by
  have h := finite_homogeneous_sum_polynomial
    (fun choice : (term : Term) → Choice term => Sigma (fun term => Slots term (choice term)))
    (fun choice => familyTensor (fun term => Slots term (choice term)) (fun term => tensor term (choice term)))
  have hequal : (fun value => ∏ term, ∑ choice, tensorEvaluation (tensor term choice) value) =
      (fun value => ∑ choice : (term : Term) → Choice term,
        tensorEvaluation (familyTensor (fun term => Slots term (choice term))
          (fun term => tensor term (choice term))) value) := by
    funext value
    simp_rw [family_tensor_evaluation]
    exact Fintype.prod_sum _
  rw [hequal]
  exact h

/-- Dilation of the Gaussian argument is exactly degree-wise tensor scaling. -/
theorem tensorEvaluation_dilate (tensor : BlockFock.Tensor Slot Coordinate) (radius : ℝ)
    (value : Coordinate → ℂ) :
    tensorEvaluation tensor (fun coordinate => (radius : ℂ) * value coordinate) =
      tensorEvaluation (fun word => radius ^ Fintype.card Slot * tensor word) value := by
  simp only [tensorEvaluation, wordMonomial, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Complex.ofReal_mul, Complex.ofReal_pow]
  apply Finset.sum_congr rfl
  intro word _
  ring

/-- Every finite tensor polynomial belongs to Gaussian L2. -/
theorem tensor_memLp (tensor : BlockFock.Tensor Slot Coordinate) :
    MemLp (tensorEvaluation tensor) 2 FockGaussian.field := by
  apply (memLp_two_iff_integrable_sq_norm (by
    apply Continuous.aestronglyMeasurable
    unfold tensorEvaluation wordMonomial
    fun_prop)).mpr
  have h := (tensor_pair_integrable tensor tensor).re
  simpa only [Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm] using h

omit [Fintype Slot] [Fintype OtherSlot] in
/-- Every polynomial certificate supplies the integrability needed for finite
Gaussian norm inequalities. -/
theorem IsTensorPolynomial.memLp {function : (Coordinate → ℂ) → ℂ}
    (hfunction : IsTensorPolynomial function) : MemLp function 2 FockGaussian.field := by
  obtain ⟨degrees, tensor, _, heval⟩ := hfunction
  have h := memLp_finset_sum degrees (fun degree _ => tensor_memLp (tensor degree))
  have heq : function = seriesEvaluation degrees tensor := funext heval
  rw [heq]
  exact h

omit [Fintype Slot] [Fintype OtherSlot] in
/-- The genuine Gaussian L2 norm of an evaluated polynomial. -/
noncomputable def gaussianNorm (function : (Coordinate → ℂ) → ℂ) : ℝ :=
  lpNorm function 2 FockGaussian.field

omit [Fintype Slot] [Fintype OtherSlot] in
set_option backward.isDefEq.respectTransparency false in
/-- The Gaussian L2 norm agrees with the square root of the actual integral. -/
theorem gaussianNorm_eq_sqrt {function : (Coordinate → ℂ) → ℂ}
    (hfunction : AEStronglyMeasurable function FockGaussian.field) :
    gaussianNorm function = Real.sqrt (∫ value, Complex.normSq (function value) ∂FockGaussian.field) := by
  rw [gaussianNorm, lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hfunction]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two, ← Real.sqrt_eq_rpow, Complex.sq_norm]

set_option backward.isDefEq.respectTransparency false in
/-- The homogeneous multiplication estimate for any actual finite polynomial,
with its doubled-radius norm represented by a concrete Gaussian integral. -/
theorem homogeneous_times_polynomial_energy_le (tensor : BlockFock.Tensor Slot Coordinate)
    {function : (Coordinate → ℂ) → ℂ} (hfunction : IsTensorPolynomial function) :
    (∫ value, Complex.normSq (tensorEvaluation tensor value * function value) ∂FockGaussian.field) ≤
      ((Fintype.card Slot).factorial : ℝ) * 2 ^ Fintype.card Slot * BlockFock.tensorEnergy tensor *
        (∫ value, Complex.normSq (function (fun coordinate => (Real.sqrt 2 : ℂ) * value coordinate))
          ∂FockGaussian.field) := by
  obtain ⟨degrees, coefficient, hsymmetric, heval⟩ := hfunction
  have hscaled : (∫ value, Complex.normSq (function (fun coordinate => (Real.sqrt 2 : ℂ) * value coordinate))
      ∂FockGaussian.field) =
      ∑ degree ∈ degrees, (degree.factorial : ℝ) * 2 ^ degree * BlockFock.tensorEnergy (coefficient degree) := by
    simp_rw [heval, seriesEvaluation, tensorEvaluation_dilate, Fintype.card_fin]
    change (∫ value, Complex.normSq (seriesEvaluation degrees
      (fun degree word => Real.sqrt 2 ^ degree * coefficient degree word) value)
        ∂FockGaussian.field) = _
    rw [complete_tensor_fock_isometry _ _ (by
      intro degree hdegree word permutation
      rw [hsymmetric degree hdegree word permutation])]
    apply Finset.sum_congr rfl
    intro degree _
    rw [tensorEnergy_smul]
    have hp : (Real.sqrt 2 ^ degree) ^ 2 = (2 : ℝ) ^ degree := by
      rw [← pow_mul, Nat.mul_comm degree 2, pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rw [hp]
    ring
  rw [hscaled]
  simp_rw [heval]
  exact homogeneous_times_series_gaussian_le tensor degrees coefficient

omit [Fintype Slot] [Fintype OtherSlot] in
set_option backward.isDefEq.respectTransparency false in
/-- Linear factors are concrete finite tensor polynomials. -/
theorem linear_product_polynomial [Fintype Term] (coefficient : Term → Coordinate → ℝ) :
    IsTensorPolynomial (fun value => ∏ term, (1 + ∑ coordinate, (coefficient term coordinate : ℂ) * value coordinate)) := by
  letI : DecidableEq (Fin 1) := Classical.decEq _
  let Slots (_ : Term) : Bool → Type := fun choice => Fin (if choice then 1 else 0)
  letI : ∀ term choice, Fintype (Slots term choice) := fun _ _ => inferInstanceAs (Fintype (Fin _))
  let tensor (term : Term) : (choice : Bool) → BlockFock.Tensor (Slots term choice) Coordinate
    | false => fun _ => 1
    | true => fun word => coefficient term (word (0 : Fin 1))
  have h := finite_block_product_polynomial (fun _ : Term => Bool) Slots tensor
  have heval (term : Term) (value : Coordinate → ℂ) :
      (∑ choice : Bool, tensorEvaluation (tensor term choice) value) =
        1 + ∑ coordinate, (coefficient term coordinate : ℂ) * value coordinate := by
    rw [Fintype.sum_bool]
    change tensorEvaluation (fun word : Fin 1 → Coordinate => coefficient term (word 0)) value +
      tensorEvaluation (fun _ : Fin 0 → Coordinate => (1 : ℝ)) value = _
    simp only [tensorEvaluation, wordMonomial, Fin.prod_univ_one, Fin.prod_univ_zero,
      Complex.ofReal_one, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, pow_zero, Nat.cast_one, nsmul_eq_mul]
    have hsum := (Equiv.funUnique (Fin 1) Coordinate).sum_comp
      (fun coordinate => (coefficient term coordinate : ℂ) * value coordinate)
    change (∑ word : Fin 1 → Coordinate, (coefficient term (word 0) : ℂ) * value (word 0)) = _ at hsum
    rw [hsum, add_comm]
  simpa only [heval] using h

set_option backward.isDefEq.respectTransparency false in
/-- A selected homogeneous nonlinear tensor times every remaining linear
factor has a dimension-independent exact Gaussian bound. -/
theorem homogeneous_times_linear_product_energy_le [Fintype Term] [Nonempty Coordinate]
    (tensor : BlockFock.Tensor Slot Coordinate) (coefficient : Term → Coordinate → ℝ)
    (henergy : (∑ term, ∑ coordinate, coefficient term coordinate ^ 2) ≤ 1 / 8) :
    (∫ value, Complex.normSq (tensorEvaluation tensor value *
        ∏ term, (1 + ∑ coordinate, (coefficient term coordinate : ℂ) * value coordinate))
      ∂FockGaussian.field) ≤
      ((Fintype.card Slot).factorial : ℝ) * 2 ^ Fintype.card Slot * BlockFock.tensorEnergy tensor *
        (4 * Real.exp (4 * ∑ coordinate, (∑ term, coefficient term coordinate) ^ 2)) := by
  apply (homogeneous_times_polynomial_energy_le tensor (linear_product_polynomial coefficient)).trans
  apply mul_le_mul_of_nonneg_left _ (by
    exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  let scaled (term : Term) (coordinate : Coordinate) := Real.sqrt 2 * coefficient term coordinate
  have hscaled : (∑ term, ∑ coordinate, scaled term coordinate ^ 2) ≤ 1 / 4 := by
    simp only [scaled, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), ← Finset.mul_sum]
    linarith
  have h := FockGaussian.linear_product_bound scaled hscaled
  have hpoint (value : Coordinate → ℂ) :
      (∏ term, (1 + ∑ coordinate, (coefficient term coordinate : ℂ) *
        ((Real.sqrt 2 : ℂ) * value coordinate))) =
      ∏ term, (1 + ∑ coordinate, (scaled term coordinate : ℂ) * value coordinate) := by
    apply Finset.prod_congr rfl
    intro term _
    congr 1
    apply Finset.sum_congr rfl
    intro coordinate _
    simp only [scaled, Complex.ofReal_mul]
    ring
  simp_rw [hpoint, map_prod]
  have hmean : (∑ coordinate, (∑ term, scaled term coordinate) ^ 2) =
      2 * ∑ coordinate, (∑ term, coefficient term coordinate) ^ 2 := by
    simp only [scaled, ← Finset.mul_sum, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hmean] at h
  convert h using 1
  congr 2
  ring

set_option backward.isDefEq.respectTransparency false in
/-- Homogeneous multiplication preserves concrete polynomial certificates. -/
theorem homogeneous_times_polynomial (tensor : BlockFock.Tensor Slot Coordinate)
    {function : (Coordinate → ℂ) → ℂ} (hfunction : IsTensorPolynomial function) :
    IsTensorPolynomial (fun value => tensorEvaluation tensor value * function value) := by
  obtain ⟨degrees, coefficient, _, heval⟩ := hfunction
  have h := finite_homogeneous_sum_polynomial (fun degree : degrees => Slot ⊕ Fin degree.val)
    (fun degree => BlockFock.tensorProduct tensor (coefficient degree.val))
  have hequal : (fun value => tensorEvaluation tensor value * function value) =
      (fun value => ∑ degree : degrees,
        tensorEvaluation (BlockFock.tensorProduct tensor (coefficient degree.val)) value) := by
    funext value
    simp only [tensor_product_evaluation, heval, seriesEvaluation, Finset.mul_sum]
    exact (Finset.sum_coe_sort degrees (fun degree =>
      tensorEvaluation tensor value * tensorEvaluation (coefficient degree) value)).symm
  rw [hequal]
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Square-root form of the actual homogeneous-times-linear estimate. -/
theorem homogeneous_times_linear_product_norm_le [Fintype Term] [Nonempty Coordinate]
    (tensor : BlockFock.Tensor Slot Coordinate) (coefficient : Term → Coordinate → ℝ)
    (henergy : (∑ term, ∑ coordinate, coefficient term coordinate ^ 2) ≤ 1 / 8) :
    gaussianNorm (fun value => tensorEvaluation tensor value *
        ∏ term, (1 + ∑ coordinate, (coefficient term coordinate : ℂ) * value coordinate)) ≤
      Real.sqrt (((Fintype.card Slot).factorial : ℝ) * 2 ^ Fintype.card Slot * BlockFock.tensorEnergy tensor) *
        (2 * Real.exp (2 * ∑ coordinate, (∑ term, coefficient term coordinate) ^ 2)) := by
  rw [gaussianNorm_eq_sqrt
    (homogeneous_times_polynomial tensor (linear_product_polynomial coefficient)).memLp.aestronglyMeasurable]
  apply (Real.sqrt_le_sqrt (homogeneous_times_linear_product_energy_le tensor coefficient henergy)).trans_eq
  rw [Real.sqrt_mul (by
    exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))]
  congr 1
  have heq (mean : ℝ) : 4 * Real.exp (4 * mean) = (2 * Real.exp (2 * mean)) ^ 2 := by
    have hexp : Real.exp (4 * mean) = Real.exp (2 * mean) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num
      ring
    rw [hexp]
    ring
  rw [heq, Real.sqrt_sq (by positivity)]

/-- A nonlinear choice leaves the linear factor in place, or selects its
quadratic or cubic tensor. -/
abbrev BlockChoice := Option Bool

def selectedSlots : BlockChoice → Type
  | none => Fin 0
  | some false => Fin 2
  | some true => Fin 3

instance selectedSlots_fintype (choice : BlockChoice) : Fintype (selectedSlots choice) := by
  cases choice with
  | none => exact inferInstanceAs (Fintype (Fin 0))
  | some choice =>
    cases choice
    · exact inferInstanceAs (Fintype (Fin 2))
    · exact inferInstanceAs (Fintype (Fin 3))

/-- The actual homogeneous tensor selected from one block. -/
noncomputable def selectedTensor (quadratic : BlockFock.Tensor (Fin 2) Coordinate)
    (cubic : BlockFock.Tensor (Fin 3) Coordinate) :
    (choice : BlockChoice) → BlockFock.Tensor (selectedSlots choice) Coordinate
  | none => fun _ => 1
  | some false => quadratic
  | some true => cubic

/-- Linear coefficients remaining after one nonlinear selection pattern. -/
noncomputable def remainingLinear (coefficient : Term → Coordinate → ℝ)
    (choice : Term → BlockChoice) (term : Term) (coordinate : Coordinate) : ℝ :=
  if choice term = none then coefficient term coordinate else 0

/-- The actual normalized block product whose complete Fock energy is bounded. -/
noncomputable def cubicBlockProduct [Fintype Term] (coefficient : Term → Coordinate → ℝ)
    (quadratic : Term → BlockFock.Tensor (Fin 2) Coordinate)
    (cubic : Term → BlockFock.Tensor (Fin 3) Coordinate) (value : Coordinate → ℂ) : ℂ :=
  ∏ term, ((1 + ∑ coordinate, (coefficient term coordinate : ℂ) * value coordinate) +
    tensorEvaluation (quadratic term) value + tensorEvaluation (cubic term) value)

/-- The coordinate tensor of all homogeneous nonlinear factors selected in a
pattern, on their actual disjoint slot families. -/
noncomputable def selectionTensor [Fintype Term]
    (quadratic : Term → BlockFock.Tensor (Fin 2) Coordinate)
    (cubic : Term → BlockFock.Tensor (Fin 3) Coordinate) (choice : Term → BlockChoice) :
    BlockFock.Tensor (Sigma (fun term => selectedSlots (choice term))) Coordinate :=
  familyTensor (fun term => selectedSlots (choice term))
    (fun term => selectedTensor (quadratic term) (cubic term) (choice term))

omit [Fintype Slot] [Fintype OtherSlot] in
set_option backward.isDefEq.respectTransparency false in
/-- Exact expansion of the whole block product over all nonlinear selections. -/
theorem cubic_product_expansion [Fintype Term] (coefficient : Term → Coordinate → ℝ)
    (quadratic : Term → BlockFock.Tensor (Fin 2) Coordinate)
    (cubic : Term → BlockFock.Tensor (Fin 3) Coordinate) (value : Coordinate → ℂ) :
    cubicBlockProduct coefficient quadratic cubic value =
      ∑ choice : Term → BlockChoice,
        tensorEvaluation (selectionTensor quadratic cubic choice) value *
          ∏ term, (1 + ∑ coordinate, (remainingLinear coefficient choice term coordinate : ℂ) * value coordinate) := by
  let factor (term : Term) (choice : BlockChoice) : ℂ := match choice with
    | none => 1 + ∑ coordinate, (coefficient term coordinate : ℂ) * value coordinate
    | some false => tensorEvaluation (quadratic term) value
    | some true => tensorEvaluation (cubic term) value
  have hsum (term : Term) : (∑ choice : BlockChoice, factor term choice) =
      (1 + ∑ coordinate, (coefficient term coordinate : ℂ) * value coordinate) +
        tensorEvaluation (quadratic term) value + tensorEvaluation (cubic term) value := by
    simp only [Fintype.sum_option, Fintype.sum_bool, factor]
    ring
  have hexpand := Fintype.prod_sum factor
  simp only [hsum] at hexpand
  change cubicBlockProduct coefficient quadratic cubic value = _ at hexpand
  rw [hexpand]
  apply Finset.sum_congr rfl
  intro choice _
  rw [selectionTensor, family_tensor_evaluation, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro term _
  cases hchoice : choice term with
  | none => simp [factor, selectedTensor, selectedSlots, remainingLinear, hchoice, tensorEvaluation, wordMonomial]
  | some active => cases active <;> simp [factor, selectedTensor, remainingLinear, hchoice]

omit [Fintype Slot] [Fintype OtherSlot] in
/-- Omitting linear factors can only decrease their total squared coefficient energy. -/
theorem remaining_linear_energy_le [Fintype Term] (coefficient : Term → Coordinate → ℝ)
    (choice : Term → BlockChoice) :
    (∑ term, ∑ coordinate, remainingLinear coefficient choice term coordinate ^ 2) ≤
      ∑ term, ∑ coordinate, coefficient term coordinate ^ 2 := by
  apply Finset.sum_le_sum
  intro term _
  apply Finset.sum_le_sum
  intro coordinate _
  by_cases hchoice : choice term = none
  · simp [remainingLinear, hchoice]
  · simp [remainingLinear, hchoice, sq_nonneg]

/-- An explicit finite selection majorant, obtained from genuine tensor and
Gaussian norms, for the complete degree-three block product. -/
noncomputable def cubicSelectionMajorant [Fintype Term] (coefficient : Term → Coordinate → ℝ)
    (quadratic : Term → BlockFock.Tensor (Fin 2) Coordinate)
    (cubic : Term → BlockFock.Tensor (Fin 3) Coordinate) : ℝ :=
  ∑ choice : Term → BlockChoice,
    Real.sqrt (((Fintype.card (Sigma (fun term => selectedSlots (choice term)))).factorial : ℝ) *
      2 ^ Fintype.card (Sigma (fun term => selectedSlots (choice term))) *
        BlockFock.tensorEnergy (selectionTensor quadratic cubic choice)) *
      (2 * Real.exp (2 * ∑ coordinate, (∑ term, remainingLinear coefficient choice term coordinate) ^ 2))

omit [Fintype Slot] [Fintype OtherSlot] in
set_option backward.isDefEq.respectTransparency false in
/-- A complete bound for the actual product of arbitrary linear, quadratic,
and cubic blocks, before simplifying its finite selection sum to geometric
activities. This theorem assumes no Fock estimate. -/
theorem cubic_block_norm_le [Fintype Term] [Nonempty Coordinate]
    (coefficient : Term → Coordinate → ℝ)
    (quadratic : Term → BlockFock.Tensor (Fin 2) Coordinate)
    (cubic : Term → BlockFock.Tensor (Fin 3) Coordinate)
    (henergy : (∑ term, ∑ coordinate, coefficient term coordinate ^ 2) ≤ 1 / 8) :
    gaussianNorm (cubicBlockProduct coefficient quadratic cubic) ≤
      cubicSelectionMajorant coefficient quadratic cubic := by
  have hterm (choice : Term → BlockChoice) :=
    homogeneous_times_polynomial (selectionTensor quadratic cubic choice)
      (linear_product_polynomial (remainingLinear coefficient choice))
  have htriangle := lpNorm_sum_le (s := Finset.univ)
    (fun choice _ => (hterm choice).memLp) (show (1 : ENNReal) ≤ 2 by norm_num)
  have hfunction : cubicBlockProduct coefficient quadratic cubic =
      (∑ choice : Term → BlockChoice, fun value =>
        tensorEvaluation (selectionTensor quadratic cubic choice) value *
          ∏ term, (1 + ∑ coordinate, (remainingLinear coefficient choice term coordinate : ℂ) * value coordinate)) := by
    funext value
    simp only [Finset.sum_apply]
    exact cubic_product_expansion coefficient quadratic cubic value
  rw [gaussianNorm, hfunction]
  apply htriangle.trans
  apply Finset.sum_le_sum
  intro choice _
  exact homogeneous_times_linear_product_norm_le (selectionTensor quadratic cubic choice)
    (remainingLinear coefficient choice) ((remaining_linear_energy_le coefficient choice).trans henergy)

omit [Fintype Slot] [Fintype OtherSlot] in
/-- Integrability of the actual full cubic block product. -/
theorem cubic_product_memLp [Fintype Term] (coefficient : Term → Coordinate → ℝ)
    (quadratic : Term → BlockFock.Tensor (Fin 2) Coordinate)
    (cubic : Term → BlockFock.Tensor (Fin 3) Coordinate) :
    MemLp (cubicBlockProduct coefficient quadratic cubic) 2 FockGaussian.field := by
  have h := memLp_finset_sum Finset.univ (fun choice _ =>
    (homogeneous_times_polynomial (selectionTensor quadratic cubic choice)
      (linear_product_polynomial (remainingLinear coefficient choice))).memLp)
  have heq : cubicBlockProduct coefficient quadratic cubic =
      (fun value => ∑ choice : Term → BlockChoice,
        tensorEvaluation (selectionTensor quadratic cubic choice) value *
          ∏ term, (1 + ∑ coordinate, (remainingLinear coefficient choice term coordinate : ℂ) * value coordinate)) :=
    funext (cubic_product_expansion coefficient quadratic cubic)
  rw [heq]
  exact h

omit [Fintype Slot] [Fintype OtherSlot] in
/-- The explicit complete nonlinear majorant is nonnegative. -/
theorem cubic_selection_majorant_nonneg [Fintype Term] (coefficient : Term → Coordinate → ℝ)
    (quadratic : Term → BlockFock.Tensor (Fin 2) Coordinate)
    (cubic : Term → BlockFock.Tensor (Fin 3) Coordinate) :
    0 ≤ cubicSelectionMajorant coefficient quadratic cubic := by
  unfold cubicSelectionMajorant
  positivity

omit [Fintype Slot] [Fintype OtherSlot] in
set_option backward.isDefEq.respectTransparency false in
/-- Complete nonlinear Gaussian energy bound, with every selection and degree
included and no norm bound hidden in the premises. -/
theorem cubic_block_energy_le [Fintype Term] [Nonempty Coordinate]
    (coefficient : Term → Coordinate → ℝ)
    (quadratic : Term → BlockFock.Tensor (Fin 2) Coordinate)
    (cubic : Term → BlockFock.Tensor (Fin 3) Coordinate)
    (henergy : (∑ term, ∑ coordinate, coefficient term coordinate ^ 2) ≤ 1 / 8) :
    (∫ value, Complex.normSq (cubicBlockProduct coefficient quadratic cubic value) ∂FockGaussian.field) ≤
      cubicSelectionMajorant coefficient quadratic cubic ^ 2 := by
  have h := cubic_block_norm_le coefficient quadratic cubic henergy
  rw [gaussianNorm_eq_sqrt (cubic_product_memLp coefficient quadratic cubic).aestronglyMeasurable] at h
  have hi : 0 ≤ ∫ value, Complex.normSq (cubicBlockProduct coefficient quadratic cubic value) ∂FockGaussian.field :=
    integral_nonneg (fun _ => Complex.normSq_nonneg _)
  have hsq := Real.sq_sqrt hi
  have hm := cubic_selection_majorant_nonneg coefficient quadratic cubic
  nlinarith [Real.sqrt_nonneg (∫ value, Complex.normSq (cubicBlockProduct coefficient quadratic cubic value) ∂FockGaussian.field)]

omit [Fintype Slot] [Fintype OtherSlot] in
set_option backward.isDefEq.respectTransparency false in
/-- Full finite histogram tail for a genuine degree-at-most-three block
product. The explicit finite selection majorant is proved above from the
actual local tensors, and the falling-factorial denominator is retained
through the highest degree. -/
theorem complete_cubic_histogram_tail [Fintype Term] [Nonempty Coordinate]
    (population cutoff : ℕ) (radius : ℝ)
    (tensor : (degree : ℕ) → BlockFock.Tensor (Fin degree) Coordinate)
    (coefficient : Term → Coordinate → ℝ)
    (quadratic : Term → BlockFock.Tensor (Fin 2) Coordinate)
    (cubic : Term → BlockFock.Tensor (Fin 3) Coordinate)
    (hpopulation : 0 < population) (hradius : Real.exp 1 ≤ radius ^ 2)
    (hsymmetric : ∀ degree ≤ population, ∀ word (permutation : Equiv.Perm (Fin degree)),
      tensor degree (word ∘ permutation) = tensor degree word)
    (hcoefficients : ∀ value,
      seriesEvaluation (Finset.range (population + 1)) (normalizedTensor population radius tensor) value =
        cubicBlockProduct coefficient quadratic cubic value)
    (henergy : (∑ term, ∑ coordinate, coefficient term coordinate ^ 2) ≤ 1 / 8) :
    HistogramTail.likelihoodTailEnergy population cutoff (fun degree => BlockFock.tensorEnergy (tensor degree)) ≤
      (Real.exp 1 / radius ^ 2) ^ (cutoff + 1) * cubicSelectionMajorant coefficient quadratic cubic ^ 2 := by
  apply (HistogramTail.complete_tail_energy_le population cutoff radius _ hpopulation
    (fun degree => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hradius).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  change HistogramTail.fockEnergy population radius (fun degree => BlockFock.tensorEnergy (tensor degree)) ≤ _
  rw [← normalized_fock_isometry population radius tensor hsymmetric]
  simp_rw [hcoefficients]
  exact cubic_block_energy_le coefficient quadratic cubic henergy

end NonlinearFock
end AFT
