import AFT.BlockDensity

/-! # Actual local density coefficients as finite Gaussian tensors -/

namespace AFT
namespace LocalTensors

open scoped BigOperators Classical

variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]

/-- Whiten a genuine weighted density kernel into Euclidean tensor coordinates.
The ambient palette coordinates may be redundant; no basis choice is required. -/
noncomputable def whitenedTensor (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) : BlockFock.Tensor Slot Color :=
  fun word => (∏ slot, Real.sqrt ((reference slot).weight (word slot))) * kernel word

/-- Whitening is an exact isometry for the actual product reference law. -/
theorem whitenedTensor_energy (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) :
    BlockFock.tensorEnergy (whitenedTensor reference kernel) =
      (FiniteDist.independent reference).l2Sq kernel := by
  unfold BlockFock.tensorEnergy whitenedTensor FiniteDist.l2Sq FiniteDist.expectation FiniteDist.independent
  apply Finset.sum_congr rfl
  intro word _
  simp only [mul_pow, ← Finset.prod_pow, Real.sq_sqrt (FiniteDist.nonneg _ _)]

set_option backward.isDefEq.respectTransparency false in
/-- Restricting independent inputs to any specified set of slots preserves
the exact product law on those slots. -/
theorem independent_restriction_expectation (reference : Slot → FiniteDist Color)
    (selected : Finset Slot) (function : (selected → Color) → ℝ) :
    (FiniteDist.independent reference).expectation (fun word => function (fun slot => word slot)) =
      (FiniteDist.independent (fun slot : selected => reference slot)).expectation function := by
  let split := Equiv.piEquivPiSubtypeProd (fun slot => slot ∈ selected) (fun _ : Slot => Color)
  unfold FiniteDist.expectation FiniteDist.independent
  rw [← split.symm.sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro chosen _
  have hweight (rest : {slot : Slot // slot ∉ selected} → Color) :
      (∏ slot, (reference slot).weight (split.symm (chosen, rest) slot)) =
        (∏ slot : selected, (reference slot).weight (chosen slot)) *
          ∏ slot : {slot : Slot // slot ∉ selected}, (reference slot).weight (rest slot) := by
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun slot => slot ∈ selected)]
    apply congrArg₂ (· * ·)
    · apply Finset.prod_congr (by ext; simp)
      intro slot _
      change (reference slot).weight (if h : (slot : Slot) ∈ selected then chosen ⟨slot, h⟩ else rest ⟨slot, h⟩) = _
      simp only [dif_pos (show (slot : Slot) ∈ selected from slot.property)]
    · apply Finset.prod_congr (by ext; simp)
      intro slot _
      change (reference slot).weight (if h : (slot : Slot) ∈ selected then chosen ⟨slot, h⟩ else rest ⟨slot, h⟩) = _
      simp only [dif_neg (show (slot : Slot) ∉ selected from slot.property)]
  have hrestriction (rest : {slot : Slot // slot ∉ selected} → Color) :
      (fun slot : selected => split.symm (chosen, rest) slot) = chosen := by
    funext slot
    change (if h : (slot : Slot) ∈ selected then chosen ⟨slot, h⟩ else rest ⟨slot, h⟩) = _
    simp only [dif_pos (show (slot : Slot) ∈ selected from slot.property)]
  simp_rw [hweight, hrestriction]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hmass := (FiniteDist.independent
    (fun slot : {slot : Slot // slot ∉ selected} => reference slot)).sum_one
  change (∑ rest : {slot : Slot // slot ∉ selected} → Color,
    ∏ slot : {slot : Slot // slot ∉ selected}, (reference slot).weight (rest slot)) = 1 at hmass
  rw [hmass, mul_one]

/-- The genuine canonical component, with precisely its selected arguments. -/
noncomputable def restrictedComponent (reference : Slot → FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (selected : Finset Slot) (word : selected → Color) : ℝ :=
  ∑ input, mass input * ∏ slot : selected,
    Hoeffding.centeredAtom (reference slot) (input slot) (word slot)

/-- The restricted coefficient evaluates to the full Hoeffding coefficient
when the omitted coordinates are restored. -/
theorem restrictedComponent_eq (reference : Slot → FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (selected : Finset Slot) (word : Slot → Color) :
    restrictedComponent reference mass selected (fun slot => word slot) =
      Hoeffding.densityComponent reference mass selected word := by
  unfold restrictedComponent Hoeffding.densityComponent
  apply Finset.sum_congr rfl
  intro input _
  congr 1
  exact Finset.prod_coe_sort selected (fun slot =>
    Hoeffding.centeredAtom (reference slot) (input slot) (word slot))

/-- A local coefficient's actual Gaussian tensor, before symmetrization. -/
noncomputable def localTensor (reference : Slot → FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (selected : Finset Slot) : BlockFock.Tensor selected Color :=
  whitenedTensor (fun slot : selected => reference slot) (restrictedComponent reference mass selected)

set_option backward.isDefEq.respectTransparency false in
/-- The local tensor norm is the actual projected density norm, exactly. -/
theorem localTensor_energy_eq (reference : Slot → FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (selected : Finset Slot) :
    BlockFock.tensorEnergy (localTensor reference mass selected) =
      (FiniteDist.independent reference).l2Sq (Hoeffding.densityComponent reference mass selected) := by
  rw [localTensor, whitenedTensor_energy]
  unfold FiniteDist.l2Sq
  have h := independent_restriction_expectation reference selected
    (fun word => restrictedComponent reference mass selected word ^ 2)
  simp only [restrictedComponent_eq] at h
  unfold FiniteDist.expectation FiniteDist.independent at h ⊢
  apply Eq.trans ?_ h.symm
  apply Finset.sum_congr (by ext; simp)
  intro word _
  rfl

/-- Every concrete selected tensor is controlled by the full signed local
law, with no palette-dependent constant. -/
theorem localTensor_energy_le (reference : Slot → FiniteDist Color)
    (hreference : ∀ slot color, 0 < (reference slot).weight color)
    (mass : (Slot → Color) → ℝ) (selected : Finset Slot) :
    BlockFock.tensorEnergy (localTensor reference mass selected) ≤
      (FiniteDist.independent reference).l2Sq
        (fun value => mass value / (FiniteDist.independent reference).weight value) := by
  convert (localTensor_energy_eq reference mass selected).le.trans
    (BlockDensity.canonical_component_energy_le reference hreference mass selected) using 1

/-- Actual centered one-color coefficient in the Gaussian coordinate space. -/
noncomputable def atomCoefficient (reference : FiniteDist Color) (input output : Color) : ℝ :=
  Real.sqrt (reference.weight output) * Hoeffding.centeredAtom reference input output

/-- The linear polynomial of one centered color outcome. -/
noncomputable def atomLinear (reference : FiniteDist Color) (input : Color)
    (value : Color → ℂ) : ℂ :=
  ∑ output, (atomCoefficient reference input output : ℂ) * value output

/-- The coefficient tensor is computed directly from the actual signed mass
and the actual one-color centered vectors. -/
theorem localTensor_formula (reference : Slot → FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (selected : Finset Slot) (word : selected → Color) :
    localTensor reference mass selected word =
      ∑ input, mass input * ∏ slot : selected,
        atomCoefficient (reference slot) (input slot) (word slot) := by
  unfold localTensor whitenedTensor restrictedComponent atomCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro input _
  rw [Finset.prod_mul_distrib]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of a selected coefficient exactly equals the corresponding
product of centered color polynomials averaged over the original joint law. -/
theorem localTensor_evaluation (reference : Slot → FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (selected : Finset Slot) (value : Color → ℂ) :
    TensorFock.tensorEvaluation (localTensor reference mass selected) value =
      ∑ input, (mass input : ℂ) * ∏ slot : selected,
        atomLinear (reference slot) (input slot) value := by
  unfold TensorFock.tensorEvaluation TensorFock.wordMonomial
  simp only [localTensor_formula, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_prod, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro input _
  have h := Fintype.prod_sum (fun slot : selected => fun color : Color =>
    (atomCoefficient (reference slot) (input slot) color : ℂ) * value color)
  unfold atomLinear
  rw [h]
  rw [Finset.mul_sum]
  apply Finset.sum_congr (by ext; simp)
  intro word _
  rw [Finset.prod_mul_distrib]
  ring

/-- The actual generating polynomial of a finite signed output law. -/
noncomputable def localGenerating (reference : Slot → FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (value : Color → ℂ) : ℂ :=
  ∑ input, (mass input : ℂ) * ∏ slot, (1 + atomLinear (reference slot) (input slot) value)

set_option backward.isDefEq.respectTransparency false in
/-- Exact all-subset expansion of the physical output polynomial. -/
theorem localGenerating_expansion (reference : Slot → FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (value : Color → ℂ) :
    localGenerating reference mass value =
      ∑ selected : Finset Slot, TensorFock.tensorEvaluation (localTensor reference mass selected) value := by
  simp only [localTensor_evaluation]
  rw [Finset.sum_comm]
  unfold localGenerating
  apply Finset.sum_congr rfl
  intro input _
  rw [← Finset.mul_sum]
  congr 1
  have h := Fintype.prod_add
    (fun slot => atomLinear (reference slot) (input slot) value) (fun _ : Slot => (1 : ℂ))
  simp only [Finset.prod_const_one, mul_one] at h
  calc
    _ = ∑ selected : Finset Slot, ∏ slot ∈ selected,
        atomLinear (reference slot) (input slot) value := by simpa only [add_comm] using h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro selected _
      exact (Finset.prod_coe_sort selected (fun slot => atomLinear (reference slot) (input slot) value)).symm

/-- Every physical finite signed local law has a concrete symmetric tensor
polynomial certificate, obtained from its actual Hoeffding coefficients. -/
theorem localGenerating_polynomial (reference : Slot → FiniteDist Color)
    (mass : (Slot → Color) → ℝ) :
    NonlinearFock.IsTensorPolynomial (localGenerating reference mass) := by
  have h := NonlinearFock.finite_homogeneous_sum_polynomial
    (fun selected : Finset Slot => selected) (localTensor reference mass)
  have heq : localGenerating reference mass =
      (fun value => ∑ selected : Finset Slot,
        TensorFock.tensorEvaluation (localTensor reference mass selected) value) :=
    funext (localGenerating_expansion reference mass)
  rw [heq]
  exact h

/-- The actual selected coefficient reindexed onto its homogeneous degree. -/
noncomputable def degreePiece (reference : Slot → FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (degree : ℕ) (selected : Finset Slot) :
    BlockFock.Tensor (Fin degree) Color :=
  if h : Fintype.card selected = degree then
    fun word => localTensor reference mass selected (word ∘ Fintype.equivFinOfCardEq h)
  else fun _ => 0

/-- The actual symmetric homogeneous tensor of a local signed law. -/
noncomputable def degreeTensor (reference : Slot → FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (degree : ℕ) : BlockFock.Tensor (Fin degree) Color :=
  BlockFock.symmetrize (fun word => ∑ selected : Finset Slot, degreePiece reference mass degree selected word)

/-- The constructed homogeneous coefficients are genuinely symmetric. -/
theorem degreeTensor_symmetric (reference : Slot → FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (degree : ℕ) (word : Fin degree → Color)
    (permutation : Equiv.Perm (Fin degree)) :
    degreeTensor reference mass degree (word ∘ permutation) = degreeTensor reference mass degree word :=
  NonlinearFock.symmetrize_symmetric _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- Reindexing a finite tensor preserves its complete squared Hilbert norm. -/
theorem tensorEnergy_reindex {OtherSlot : Type*} [Fintype OtherSlot]
    (equiv : Slot ≃ OtherSlot) (tensor : BlockFock.Tensor Slot Color) :
    BlockFock.tensorEnergy (fun word : OtherSlot → Color => tensor (word ∘ equiv)) =
      BlockFock.tensorEnergy tensor := by
  let e : (OtherSlot → Color) ≃ (Slot → Color) :=
    { toFun := fun word => word ∘ equiv
      invFun := fun word => word ∘ equiv.symm
      left_inv := by intro word; ext index; simp
      right_inv := by intro word; ext index; simp }
  exact e.sum_comp (fun word => tensor word ^ 2)

set_option backward.isDefEq.respectTransparency false in
/-- The complete actual local generating polynomial has no coefficients
above its number of output slots. -/
theorem localGenerating_series (reference : Slot → FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (value : Color → ℂ) :
    localGenerating reference mass value =
      TensorFock.seriesEvaluation (Finset.range (Fintype.card Slot + 1))
        (degreeTensor reference mass) value := by
  rw [localGenerating_expansion]
  have hpiece (degree : ℕ) (selected : Finset Slot) :
      TensorFock.tensorEvaluation (degreePiece reference mass degree selected) value =
        if Fintype.card selected = degree then
          TensorFock.tensorEvaluation (localTensor reference mass selected) value else 0 := by
    by_cases h : Fintype.card selected = degree
    · simp only [degreePiece, dif_pos h, if_pos h]
      exact NonlinearFock.tensorEvaluation_reindex _ _ _
    · simp only [degreePiece, dif_neg h, if_neg h, TensorFock.tensorEvaluation,
        Complex.ofReal_zero, zero_mul, Finset.sum_const_zero]
  simp only [TensorFock.seriesEvaluation, degreeTensor,
    NonlinearFock.tensorEvaluation_symmetrize, NonlinearFock.tensorEvaluation_sum, hpiece]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro selected _
  have hbound : selected.card < Fintype.card Slot + 1 :=
    Nat.lt_succ_of_le (Finset.card_le_univ _)
  simp [Fintype.card_coe, Finset.mem_range, hbound]

set_option backward.isDefEq.respectTransparency false in
/-- Exact evaluation of one grouped homogeneous degree. -/
theorem degreeTensor_evaluation (reference : Slot → FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (degree : ℕ) (value : Color → ℂ) :
    TensorFock.tensorEvaluation (degreeTensor reference mass degree) value =
      ∑ selected : Finset Slot, if Fintype.card selected = degree then
        TensorFock.tensorEvaluation (localTensor reference mass selected) value else 0 := by
  simp only [degreeTensor, NonlinearFock.tensorEvaluation_symmetrize,
    NonlinearFock.tensorEvaluation_sum]
  apply Finset.sum_congr rfl
  intro selected _
  by_cases h : Fintype.card selected = degree
  · simp only [degreePiece, dif_pos h, if_pos h]
    exact NonlinearFock.tensorEvaluation_reindex _ _ _
  · simp only [degreePiece, dif_neg h, if_neg h, TensorFock.tensorEvaluation,
      Complex.ofReal_zero, zero_mul, Finset.sum_const_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The actual constant coefficient is exactly the signed law's total mass. -/
theorem degree_zero_evaluation (reference : Slot → FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (value : Color → ℂ) :
    TensorFock.tensorEvaluation (degreeTensor reference mass 0) value = (∑ input, mass input : ℝ) := by
  rw [degreeTensor_evaluation]
  simp only [Fintype.card_coe, Finset.card_eq_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [localTensor_evaluation]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Padding the exact coefficient series by zero above the actual output
size introduces no hypothesis on its coefficients. -/
theorem localGenerating_series_of_bound (reference : Slot → FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (bound : ℕ) (hbound : Fintype.card Slot ≤ bound) (value : Color → ℂ) :
    localGenerating reference mass value =
      TensorFock.seriesEvaluation (Finset.range (bound + 1)) (degreeTensor reference mass) value := by
  rw [localGenerating_expansion]
  simp only [TensorFock.seriesEvaluation, degreeTensor_evaluation]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro selected _
  have hselected : selected.card < bound + 1 :=
    Nat.lt_succ_of_le ((Finset.card_le_univ selected).trans hbound)
  simp [Fintype.card_coe, Finset.mem_range, hselected]

omit [Fintype Slot] in
set_option backward.isDefEq.respectTransparency false in
/-- A degree-one tensor is its actual one-color coefficient vector. -/
theorem linear_tensor_evaluation (tensor : BlockFock.Tensor (Fin 1) Color) (value : Color → ℂ) :
    TensorFock.tensorEvaluation tensor value =
      ∑ color, (tensor (fun _ => color) : ℂ) * value color := by
  letI : DecidableEq (Fin 1) := Classical.decEq _
  unfold TensorFock.tensorEvaluation TensorFock.wordMonomial
  rw [← (Equiv.funUnique (Fin 1) Color).symm.sum_comp]
  simp only [Equiv.funUnique_symm_apply, Fin.prod_univ_one]
  apply Finset.sum_congr rfl
  intro color _
  congr 2

set_option backward.isDefEq.respectTransparency false in
/-- The complete polynomial of an actual at-most-three-output probability
law has the precise constant/linear/quadratic/cubic form required by Fock. -/
theorem localGenerating_cubic (reference : Slot → FiniteDist Color)
    (law : FiniteDist (Slot → Color)) (hslots : Fintype.card Slot ≤ 3) (value : Color → ℂ) :
    localGenerating reference law.weight value =
      ((1 + ∑ color, (degreeTensor reference law.weight 1 (fun _ => color) : ℂ) * value color) +
        TensorFock.tensorEvaluation (degreeTensor reference law.weight 2) value +
        TensorFock.tensorEvaluation (degreeTensor reference law.weight 3) value) := by
  rw [localGenerating_series_of_bound reference law.weight 3 hslots]
  simp only [TensorFock.seriesEvaluation, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, degree_zero_evaluation, law.sum_one, Complex.ofReal_one, linear_tensor_evaluation]

/-- The genuine tensor energy of a finite sum obeys the finite Hilbert
Cauchy--Schwarz bound. -/
theorem tensorEnergy_sum_le {Index : Type*} [Fintype Index]
    (tensor : Index → BlockFock.Tensor Slot Color) :
    BlockFock.tensorEnergy (fun word => ∑ index, tensor index word) ≤
      (Fintype.card Index : ℝ) * ∑ index, BlockFock.tensorEnergy (tensor index) := by
  have hpoint (word : Slot → Color) : (∑ index, tensor index word) ^ 2 ≤
      (Fintype.card Index : ℝ) * ∑ index, tensor index word ^ 2 := by
    have h := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul (R := ℝ) Finset.univ
      (f := fun _ : Index => 1) (g := fun index => tensor index word ^ 2)
      (fun _ _ => by norm_num) (fun _ _ => sq_nonneg _) (by intro index _; ring)
    simpa using h
  unfold BlockFock.tensorEnergy
  calc
    _ ≤ ∑ word, (Fintype.card Index : ℝ) * ∑ index, tensor index word ^ 2 :=
      Finset.sum_le_sum fun word _ => hpoint word
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]

set_option backward.isDefEq.respectTransparency false in
/-- A degree piece is either the exact selected tensor or zero. -/
theorem degreePiece_energy_le (reference : Slot → FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (degree : ℕ) (selected : Finset Slot) :
    BlockFock.tensorEnergy (degreePiece reference mass degree selected) ≤
      BlockFock.tensorEnergy (localTensor reference mass selected) := by
  by_cases h : Fintype.card selected = degree
  · simp only [degreePiece, dif_pos h]
    exact (tensorEnergy_reindex _ _).le
  · simp only [degreePiece, dif_neg h, BlockFock.tensorEnergy, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, Finset.sum_const_zero]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _

set_option backward.isDefEq.respectTransparency false in
/-- Summing the actual selected tensor energies gives the full signed-law
energy, by the exact finite Hoeffding Parseval identity. -/
theorem localTensor_energy_sum (reference : Slot → FiniteDist Color)
    (hreference : ∀ slot color, 0 < (reference slot).weight color)
    (mass : (Slot → Color) → ℝ) :
    (∑ selected : Finset Slot, BlockFock.tensorEnergy (localTensor reference mass selected)) =
      (FiniteDist.independent reference).l2Sq
        (fun value => mass value / (FiniteDist.independent reference).weight value) := by
  simp_rw [localTensor_energy_eq]
  exact (Hoeffding.densityComponent_parseval reference hreference mass).symm

set_option backward.isDefEq.respectTransparency false in
/-- Every actual homogeneous response, including degrees two through four,
has energy at most a fixed slot-count factor times its full signed local law.
There is no palette-dependent factor. -/
theorem degreeTensor_energy_le (reference : Slot → FiniteDist Color)
    (hreference : ∀ slot color, 0 < (reference slot).weight color)
    (mass : (Slot → Color) → ℝ) (degree : ℕ) :
    BlockFock.tensorEnergy (degreeTensor reference mass degree) ≤
      (2 : ℝ) ^ Fintype.card Slot * (FiniteDist.independent reference).l2Sq
        (fun value => mass value / (FiniteDist.independent reference).weight value) := by
  apply (BlockFock.symmetrize_energy_le _).trans
  apply (tensorEnergy_sum_le (degreePiece reference mass degree)).trans
  have h := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun selected (_ : selected ∈ (Finset.univ : Finset (Finset Slot))) =>
      degreePiece_energy_le reference mass degree selected))
    (show (0 : ℝ) ≤ Fintype.card (Finset Slot) by positivity)
  rw [localTensor_energy_sum reference hreference mass] at h
  simpa only [Fintype.card_finset, Nat.cast_pow, Nat.cast_ofNat] using h

end LocalTensors
end AFT
