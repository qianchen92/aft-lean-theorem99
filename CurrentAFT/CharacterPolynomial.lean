import CurrentAFT.FourierSupportIsometry

/-!
# The actual character polynomial and its ordered coefficient tensors

The complex frequency argument are substituted into the real centered
color-frame polynomial using the normalized character matrix. The finite
all-degree expansion below constructs the literal ordered complex
coefficient arrays, with repeated frequency entries counted by the same
ordered-tuple convention.
-/

namespace CurrentAFT.CharacterPolynomial

open AFT FourierCoordinates FrequencySupport FourierSupportIsometry
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable {Color Index : Type*} [Fintype Color] [Nonempty Color] [Fintype Index]
  {modulus : ℕ} [NeZero modulus]

/-- The normalized nonconstant character matrix in the genuine color frame. -/
def characterCoordinates (palette : Color ≃ ZMod modulus)
    (argument : NonzeroFrequency modulus → ℂ) (color : Color) : ℂ :=
  ∑ frequency, (Real.sqrt ((uniformReference (Color := Color)).weight color) : ℂ) *
    scalarCharacter palette frequency.val color * argument frequency

theorem atomLinear_characterCoordinates (palette : Color ≃ ZMod modulus)
    (argument : NonzeroFrequency modulus → ℂ) (input : Color) :
    LocalTensors.atomLinear (uniformReference (Color := Color)) input
      (characterCoordinates palette argument) =
        ∑ frequency, argument frequency * scalarCharacter palette frequency.val input := by
  unfold LocalTensors.atomLinear characterCoordinates
  simp only [LocalTensors.atomCoefficient, Complex.ofReal_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro frequency _
  have hinner := centeredAtom_fourier palette input frequency.val
  rw [if_neg frequency.property] at hinner
  apply Eq.trans _ (congrArg (argument frequency * ·) hinner)
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro output _
  have hsquare : (Real.sqrt ((uniformReference (Color := Color)).weight output) : ℂ) ^ 2 =
      ((uniformReference (Color := Color)).weight output : ℂ) := by
    exact_mod_cast Real.sq_sqrt ((uniformReference (Color := Color)).nonneg output)
  calc
    _ = (Real.sqrt ((uniformReference (Color := Color)).weight output) : ℂ) ^ 2 *
        (Hoeffding.centeredAtom (uniformReference (Color := Color)) input output : ℂ) *
          scalarCharacter palette frequency.val output * argument frequency := by ring
    _ = _ := by rw [hsquare]; ring

/-- The manuscript's actual positive-sign character polynomial. -/
def polynomial (palette : Color ≃ ZMod modulus) (mass : (Index → Color) → ℝ)
    (argument : NonzeroFrequency modulus → ℂ) : ℂ :=
  ∑ input, (mass input : ℂ) * ∏ index,
    (1 + ∑ frequency, argument frequency * scalarCharacter palette frequency.val (input index))

/-- The physical polynomial is exactly the established real color-frame
generating polynomial under its normalized character substitution. -/
theorem polynomial_eq_generating (palette : Color ≃ ZMod modulus)
    (mass : (Index → Color) → ℝ) (argument : NonzeroFrequency modulus → ℂ) :
    polynomial palette mass argument =
      LocalTensors.localGenerating (fun _ : Index => uniformReference (Color := Color)) mass
        (characterCoordinates palette argument) := by
  unfold polynomial LocalTensors.localGenerating
  simp_rw [atomLinear_characterCoordinates]

/-- A concrete complex ordered coefficient tensor, obtained by applying
the normalized character matrix in every real tensor slot. -/
def tensorTransform {Slot : Type*} [Fintype Slot] (palette : Color ≃ ZMod modulus)
    (tensor : BlockFock.Tensor Slot Color) (frequency : Slot → NonzeroFrequency modulus) : ℂ :=
  ∑ colors : Slot → Color, (tensor colors : ℂ) * ∏ slot,
    ((Real.sqrt ((uniformReference (Color := Color)).weight (colors slot)) : ℂ) *
      scalarCharacter palette (frequency slot).val (colors slot))

/-- The literal ordered homogeneous coefficients of the character polynomial. -/
def orderedTensor (palette : Color ≃ ZMod modulus) (mass : (Index → Color) → ℝ) (degree : ℕ) :
    (Fin degree → NonzeroFrequency modulus) → ℂ :=
  tensorTransform palette
    (LocalTensors.degreeTensor (fun _ : Index => uniformReference (Color := Color)) mass degree)

/-- Expanding the coordinate substitution retains all ordered frequency
words, including words with repeated entries. -/
theorem tensorTransform_evaluation {Slot : Type*} [Fintype Slot]
    (palette : Color ≃ ZMod modulus) (tensor : BlockFock.Tensor Slot Color)
    (argument : NonzeroFrequency modulus → ℂ) :
    TensorFock.tensorEvaluation tensor (characterCoordinates palette argument) =
      ∑ frequency : Slot → NonzeroFrequency modulus,
        tensorTransform palette tensor frequency * ∏ slot, argument (frequency slot) := by
  unfold TensorFock.tensorEvaluation TensorFock.wordMonomial characterCoordinates tensorTransform
  simp_rw [Fintype.prod_sum]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro frequency _
  apply Finset.sum_congr rfl
  intro colors _
  rw [Finset.prod_mul_distrib]
  ring

/-- Exact all-degree ordinary polynomial expansion with no additional
factorial in any ordered coefficient tensor. -/
theorem polynomial_ordered_expansion (palette : Color ≃ ZMod modulus)
    (mass : (Index → Color) → ℝ) (argument : NonzeroFrequency modulus → ℂ) :
    polynomial palette mass argument =
      ∑ degree ∈ Finset.range (Fintype.card Index + 1),
        ∑ frequency : Fin degree → NonzeroFrequency modulus,
          orderedTensor palette mass degree frequency * ∏ slot, argument (frequency slot) := by
  rw [polynomial_eq_generating, LocalTensors.localGenerating_series]
  unfold TensorFock.seriesEvaluation
  apply Finset.sum_congr rfl
  intro degree _
  apply (tensorTransform_evaluation (Slot := Fin degree) palette
    (LocalTensors.degreeTensor (fun _ : Index => uniformReference (Color := Color)) mass degree) argument).trans
  apply Finset.sum_congr (by ext; simp)
  intro frequency _
  rfl

theorem tensorTransform_reindex {Slot OtherSlot : Type*} [Fintype Slot] [Fintype OtherSlot]
    (palette : Color ≃ ZMod modulus) (names : Slot ≃ OtherSlot)
    (tensor : BlockFock.Tensor Slot Color) (frequency : OtherSlot → NonzeroFrequency modulus) :
    tensorTransform palette (fun colors : OtherSlot → Color => tensor (colors ∘ names)) frequency =
      tensorTransform palette tensor (frequency ∘ names) := by
  let words : (OtherSlot → Color) ≃ (Slot → Color) :=
    { toFun := fun word => word ∘ names
      invFun := fun word => word ∘ names.symm
      left_inv := by intro word; ext slot; simp
      right_inv := by intro word; ext slot; simp }
  have h := words.sum_comp (fun colors => (tensor colors : ℂ) * ∏ slot : Slot,
    ((Real.sqrt ((uniformReference (Color := Color)).weight (colors slot)) : ℂ) *
      scalarCharacter palette (frequency (names slot)).val (colors slot)))
  unfold tensorTransform
  apply Eq.trans _ h
  apply Finset.sum_congr rfl
  intro colors _
  congr 1
  exact (names.prod_comp (fun slot =>
    (Real.sqrt ((uniformReference (Color := Color)).weight (colors slot)) : ℂ) *
      scalarCharacter palette (frequency slot).val (colors slot))).symm

/-- The normalized frequency transform of a genuine local whitened tensor
is exactly the selected canonical density's actual Fourier transform. -/
theorem tensorTransform_localTensor (palette : Color ≃ ZMod modulus)
    (mass : (Index → Color) → ℝ) (selected : Finset Index)
    (frequency : selected → NonzeroFrequency modulus) :
    tensorTransform palette (LocalTensors.localTensor
      (fun _ : Index => uniformReference (Color := Color)) mass selected) frequency =
      componentFourier palette mass selected (fun slot => (frequency slot).val) := by
  unfold tensorTransform LocalTensors.localTensor LocalTensors.whitenedTensor componentFourier FourierCoordinates.fourier
  apply Finset.sum_congr (by ext; simp)
  intro colors _
  simp only [Complex.ofReal_mul, Complex.ofReal_prod, Finset.prod_mul_distrib, FiniteDist.independent]
  have hsquare : (∏ slot : selected,
      (Real.sqrt ((uniformReference (Color := Color)).weight (colors slot)) : ℂ)) ^ 2 =
        ∏ slot : selected, ((uniformReference (Color := Color)).weight (colors slot) : ℂ) := by
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro slot _
    exact_mod_cast Real.sq_sqrt ((uniformReference (Color := Color)).nonneg _)
  calc
    _ = (∏ slot : selected, (Real.sqrt ((uniformReference (Color := Color)).weight (colors slot)) : ℂ)) ^ 2 *
        (LocalTensors.restrictedComponent (fun _ : Index => uniformReference (Color := Color)) mass selected colors : ℂ) *
          ∏ slot : selected, scalarCharacter palette (frequency slot).val (colors slot) := by ring
    _ = _ := by rw [hsquare]

/-- Every local selected frequency coordinate has its true physical
marginal coefficient, before any exchangeability normalization. -/
theorem tensorTransform_localTensor_formula (palette : Color ≃ ZMod modulus)
    (mass : (Index → Color) → ℝ) (selected : Finset Index)
    (frequency : selected → NonzeroFrequency modulus) :
    tensorTransform palette (LocalTensors.localTensor
      (fun _ : Index => uniformReference (Color := Color)) mass selected) frequency =
      FourierCoordinates.fourier palette (fun input => (mass input : ℂ)) (packed selected frequency) := by
  rw [tensorTransform_localTensor, componentFourier_formula, if_pos (fun slot => (frequency slot).property)]
  rfl

theorem tensorTransform_localTensor_energy (palette : Color ≃ ZMod modulus)
    (mass : (Index → Color) → ℝ) (selected : Finset Index) :
    (∑ frequency : selected → NonzeroFrequency modulus,
      ‖tensorTransform palette (LocalTensors.localTensor
        (fun _ : Index => uniformReference (Color := Color)) mass selected) frequency‖ ^ 2) =
      BlockFock.tensorEnergy (LocalTensors.localTensor
        (fun _ : Index => uniformReference (Color := Color)) mass selected) := by
  simp_rw [tensorTransform_localTensor_formula]
  rw [selected_support_energy, LocalTensors.localTensor_energy_eq]

theorem tensorTransform_reindex_energy {Slot OtherSlot : Type*} [Fintype Slot] [Fintype OtherSlot]
    [DecidableEq Slot] [DecidableEq OtherSlot]
    (palette : Color ≃ ZMod modulus) (names : Slot ≃ OtherSlot) (tensor : BlockFock.Tensor Slot Color) :
    (∑ frequency : OtherSlot → NonzeroFrequency modulus,
      ‖tensorTransform palette (fun colors : OtherSlot → Color => tensor (colors ∘ names)) frequency‖ ^ 2) =
      ∑ frequency : Slot → NonzeroFrequency modulus, ‖tensorTransform palette tensor frequency‖ ^ 2 := by
  let words : (OtherSlot → NonzeroFrequency modulus) ≃ (Slot → NonzeroFrequency modulus) :=
    { toFun := fun word => word ∘ names
      invFun := fun word => word ∘ names.symm
      left_inv := by intro word; ext slot; simp
      right_inv := by intro word; ext slot; simp }
  simp_rw [tensorTransform_reindex]
  exact words.sum_comp (fun frequency => ‖tensorTransform palette tensor frequency‖ ^ 2)

/-- Exact energy preservation of the literal ordered nonzero-character
tensor of an exchangeable physical signed law. -/
theorem orderedTensor_energy (palette : Color ≃ ZMod modulus)
    (mass : (Index → Color) → ℝ) (hexchangeable : HistogramNormalization.ExchangeableMass mass)
    (degree : ℕ) (hdegree : degree ≤ Fintype.card Index) :
    (∑ frequency : Fin degree → NonzeroFrequency modulus, ‖orderedTensor palette mass degree frequency‖ ^ 2) =
      BlockFock.tensorEnergy
        (LocalTensors.degreeTensor (fun _ : Index => uniformReference (Color := Color)) mass degree) := by
  obtain ⟨selected, hselectedMem⟩ := Finset.powersetCard_nonempty.mpr
    (show degree ≤ (Finset.univ : Finset Index).card by simpa using hdegree)
  have hselected : Fintype.card selected = degree := by
    simpa only [Fintype.card_coe] using (Finset.mem_powersetCard_univ.mp hselectedMem)
  have hcoeff : LocalTensors.degreeTensor (fun _ : Index => uniformReference (Color := Color)) mass degree =
      fun colors => ((Fintype.card Index).choose degree : ℝ) *
        LocalTensors.degreePiece (fun _ : Index => uniformReference (Color := Color)) mass degree selected colors :=
    funext (HistogramNormalization.degreeTensor_eq_choose (uniformReference (Color := Color)) mass
      hexchangeable degree selected hselected)
  have hpiece : (∑ frequency : Fin degree → NonzeroFrequency modulus,
      ‖tensorTransform palette (LocalTensors.degreePiece
        (fun _ : Index => uniformReference (Color := Color)) mass degree selected) frequency‖ ^ 2) =
      BlockFock.tensorEnergy (LocalTensors.degreePiece
        (fun _ : Index => uniformReference (Color := Color)) mass degree selected) := by
    simp only [LocalTensors.degreePiece, dif_pos hselected]
    rw [tensorTransform_reindex_energy, LocalTensors.tensorEnergy_reindex]
    exact tensorTransform_localTensor_energy palette mass selected
  have htransform (frequency : Fin degree → NonzeroFrequency modulus) :
      orderedTensor palette mass degree frequency =
        ((Fintype.card Index).choose degree : ℂ) * tensorTransform palette
          (LocalTensors.degreePiece (fun _ : Index => uniformReference (Color := Color)) mass degree selected) frequency := by
    unfold orderedTensor
    rw [hcoeff]
    unfold tensorTransform
    simp only [Complex.ofReal_mul, Complex.ofReal_natCast, Finset.mul_sum, mul_assoc]
  simp_rw [htransform, norm_mul, Complex.norm_natCast, mul_pow]
  rw [← Finset.mul_sum, hpiece, hcoeff, TensorFock.tensorEnergy_smul]

/-- The exact support-energy identity in the literal complex ordered
coefficient convention of the character polynomial. -/
theorem exact_support_isometry (palette : Color ≃ ZMod modulus)
    (mass : (Index → Color) → ℝ) (hexchangeable : HistogramNormalization.ExchangeableMass mass)
    (degree : ℕ) (hdegree : degree ≤ Fintype.card Index) :
    (∑ frequency : Index → ZMod modulus,
      if (support frequency).card = degree then
        ‖FourierCoordinates.fourier palette (fun input => (mass input : ℂ)) frequency‖ ^ 2 else 0) =
      (degree.factorial : ℝ) *
        (∑ frequency : Fin degree → NonzeroFrequency modulus, ‖orderedTensor palette mass degree frequency‖ ^ 2) /
          ((Fintype.card Index).descFactorial degree : ℝ) := by
  rw [orderedTensor_energy palette mass hexchangeable degree hdegree]
  exact degree_support_energy palette mass hexchangeable degree hdegree

end

end CurrentAFT.CharacterPolynomial
