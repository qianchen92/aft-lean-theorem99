import CurrentAFT.TruncatedOutput
import AFT.CenteredGaussianEvaluation

/-! # Actual homogeneous output coefficients of a truncated centered PGF -/
namespace CurrentAFT.CenteredPolynomialDegree
open AFT RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]

def selectedPolynomial (reference : FiniteDist Color) (mass : (Slot → Color) → ℝ)
    (selected : Finset Slot) : MvPolynomial Color ℝ :=
  ∑ word, mass word • ∏ slot ∈ selected, (centeredFactor reference.weight (word slot) - 1)

theorem factor_homogeneous (reference : FiniteDist Color) (color : Color) :
    (centeredFactor reference.weight color - 1).IsHomogeneous 1 := by
  have hequal : centeredFactor reference.weight color - 1 =
      MvPolynomial.X color - profileForm reference.weight := by unfold centeredFactor; ring
  rw [hequal]
  apply (MvPolynomial.isHomogeneous_X ℝ color).sub
  exact MvPolynomial.IsHomogeneous.sum _ _ _ (fun output _ =>
    MvPolynomial.isHomogeneous_C_mul_X _ _)

theorem selected_homogeneous (reference : FiniteDist Color) (mass : (Slot → Color) → ℝ)
    (selected : Finset Slot) : (selectedPolynomial reference mass selected).IsHomogeneous selected.card := by
  apply MvPolynomial.IsHomogeneous.sum
  intro word _
  rw [Algebra.smul_def]
  apply MvPolynomial.IsHomogeneous.C_mul
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
    MvPolynomial.IsHomogeneous.prod selected
      (fun slot => centeredFactor reference.weight (word slot) - 1) (fun _ => 1)
      (fun slot _ => factor_homogeneous reference (word slot))

theorem generating_expansion (reference : FiniteDist Color) (mass : (Slot → Color) → ℝ) :
    centeredGeneratingLinear reference.weight mass = ∑ selected : Finset Slot, selectedPolynomial reference mass selected := by
  unfold selectedPolynomial
  rw [Finset.sum_comm]
  change (∑ word, mass word • ∏ slot, centeredFactor reference.weight (word slot)) = _
  apply Finset.sum_congr rfl
  intro word _
  rw [← Finset.smul_sum]
  congr 1
  have h := Fintype.prod_add (fun slot => centeredFactor reference.weight (word slot) - 1)
    (fun _ : Slot => (1 : MvPolynomial Color ℝ))
  simpa only [sub_add_cancel, Finset.prod_const_one, mul_one] using h

theorem homogeneous_expansion (reference : FiniteDist Color) (mass : (Slot → Color) → ℝ) (degree : ℕ) :
    MvPolynomial.homogeneousComponent degree (centeredGeneratingLinear reference.weight mass) =
      ∑ selected : Finset Slot, if selected.card = degree then selectedPolynomial reference mass selected else 0 := by
  rw [generating_expansion, map_sum]
  apply Finset.sum_congr rfl
  intro selected _
  rw [MvPolynomial.homogeneousComponent_of_mem (selected_homogeneous reference mass selected)]
  simp only [eq_comm]

theorem selected_gaussian (reference : FiniteDist Color) (href : ∀ color, 0 < reference.weight color)
    (mass : (Slot → Color) → ℝ) (selected : Finset Slot) (value : Color → ℂ) :
    MvPolynomial.eval₂ Complex.ofRealHom (fun color => value color / (Real.sqrt (reference.weight color) : ℂ))
      (selectedPolynomial reference mass selected) =
      TensorFock.tensorEvaluation (LocalTensors.localTensor (fun _ : Slot => reference) mass selected) value := by
  rw [LocalTensors.localTensor_evaluation]
  simp only [selectedPolynomial, Algebra.smul_def, MvPolynomial.algebraMap_eq,
    MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_prod,
    MvPolynomial.eval₂_sub, MvPolynomial.eval₂_one, centeredFactor_gaussian reference href, add_sub_cancel_left]
  apply Finset.sum_congr rfl
  intro word _
  congr 1
  exact (Finset.prod_coe_sort selected (fun slot => LocalTensors.atomLinear reference (word slot) value)).symm

theorem homogeneous_gaussian (reference : FiniteDist Color) (href : ∀ color, 0 < reference.weight color)
    (mass : (Slot → Color) → ℝ) (degree : ℕ) (value : Color → ℂ) :
    MvPolynomial.eval₂ Complex.ofRealHom (fun color => value color / (Real.sqrt (reference.weight color) : ℂ))
      (MvPolynomial.homogeneousComponent degree (centeredGeneratingLinear reference.weight mass)) =
      TensorFock.tensorEvaluation (LocalTensors.degreeTensor (fun _ : Slot => reference) mass degree) value := by
  rw [homogeneous_expansion, MvPolynomial.eval₂_sum, LocalTensors.degreeTensor_evaluation]
  apply Finset.sum_congr rfl
  intro selected _
  simp only [Fintype.card_coe]
  split_ifs
  · exact selected_gaussian reference href mass selected value
  · exact MvPolynomial.eval₂_zero _ _

omit [Fintype Color] in
theorem homogeneous_cut (order degree : ℕ) (hdegree : degree ≤ order) (polynomial : MvPolynomial Color ℝ) :
    MvPolynomial.homogeneousComponent degree (TruncatedOutput.cut order polynomial) =
      MvPolynomial.homogeneousComponent degree polynomial := by
  ext powers
  simp only [MvPolynomial.coeff_homogeneousComponent, TruncatedOutput.cut, coeff_truncate]
  by_cases hequal : powers.degree = degree
  · have hweight : weightedOrder (fun _ : Color => 1) powers = powers.degree := by
      simp only [weightedOrder, Finsupp.degree, Finsupp.sum, AddMonoidHom.coe_mk, ZeroHom.coe_mk, mul_one]
    simp only [hweight, hequal, if_pos hdegree, ite_true]
  · simp only [if_neg hequal]

theorem degree_evaluation_zero_of_calibrated (reference : FiniteDist Color)
    (href : ∀ color, 0 < reference.weight color) (mass : (Slot → Color) → ℝ)
    (order degree : ℕ) (hpositive : 0 < degree) (hdegree : degree ≤ order)
    (hcalibrated : TruncatedOutput.quotientMap order (centeredGeneratingLinear reference.weight mass) = 1)
    (value : Color → ℂ) :
    TensorFock.tensorEvaluation (LocalTensors.degreeTensor (fun _ : Slot => reference) mass degree) value = 0 := by
  have hcut := congrArg Subtype.val hcalibrated
  change TruncatedOutput.cut order (centeredGeneratingLinear reference.weight mass) = 1 at hcut
  have hcomponent := congrArg (MvPolynomial.homogeneousComponent degree) hcut
  rw [homogeneous_cut order degree hdegree] at hcomponent
  have hone : MvPolynomial.homogeneousComponent degree (1 : MvPolynomial Color ℝ) = 0 :=
    MvPolynomial.homogeneousComponent_eq_zero degree 1 (by simpa only [MvPolynomial.totalDegree_one] using hpositive)
  rw [hone] at hcomponent
  rw [← homogeneous_gaussian reference href, hcomponent, MvPolynomial.eval₂_zero]

end
end CurrentAFT.CenteredPolynomialDegree
