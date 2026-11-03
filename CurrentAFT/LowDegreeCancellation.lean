import CurrentAFT.CenteredPolynomialDegree
import CurrentAFT.FourierSupportIsometry

/-! # Exact low-support Fourier cancellation from the actual centered PGF -/
namespace CurrentAFT.LowDegreeCancellation
open AFT RepresentedPolynomial FourierCoordinates FrequencySupport
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]

theorem degree_energy_zero (reference : FiniteDist Color)
    (href : ∀ color, 0 < reference.weight color) (mass : (Slot → Color) → ℝ)
    (order degree : ℕ) (hpositive : 0 < degree) (hdegree : degree ≤ order)
    (hcalibrated : TruncatedOutput.quotientMap order (centeredGeneratingLinear reference.weight mass) = 1) :
    BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Slot => reference) mass degree) = 0 := by
  have hisometry := TensorFock.symmetric_tensor_isometry
    (LocalTensors.degreeTensor (fun _ : Slot => reference) mass degree)
    (LocalTensors.degreeTensor_symmetric (fun _ : Slot => reference) mass degree)
  have heval := CenteredPolynomialDegree.degree_evaluation_zero_of_calibrated
    reference href mass order degree hpositive hdegree hcalibrated
  simp_rw [heval] at hisometry
  have hproduct : (degree.factorial : ℝ) *
      BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Slot => reference) mass degree) = 0 := by
    simpa only [Fintype.card_fin, Complex.normSq_zero, MeasureTheory.integral_zero] using hisometry.symm
  exact (mul_eq_zero.mp hproduct).resolve_left (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero degree))

/-- Exchangeability is used only in converting the genuine polynomial
degree to the complete Fourier support layer. -/
theorem fourier_zero_of_calibrated [Nonempty Color] {modulus : ℕ} [NeZero modulus]
    (palette : Color ≃ ZMod modulus) (mass : (Slot → Color) → ℝ)
    (hexchangeable : HistogramNormalization.ExchangeableMass mass) (order : ℕ)
    (hcalibrated : TruncatedOutput.quotientMap order
      (centeredGeneratingLinear (uniformReference (Color := Color)).weight mass) = 1)
    (frequency : Slot → ZMod modulus) (hpositive : 0 < (support frequency).card)
    (hdegree : (support frequency).card ≤ order) :
    fourier palette (fun word => (mass word : ℂ)) frequency = 0 := by
  have href (color : Color) : 0 < (uniformReference (Color := Color)).weight color := by
    change 0 < (Fintype.card Color : ℝ)⁻¹
    positivity
  have henergy := degree_energy_zero (uniformReference (Color := Color)) href mass order
    (support frequency).card hpositive hdegree hcalibrated
  have hsum := FourierSupportIsometry.degree_support_energy palette mass hexchangeable
    (support frequency).card (Finset.card_le_univ _)
  rw [henergy, mul_zero, zero_div] at hsum
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun other (_ : other ∈ (Finset.univ : Finset (Slot → ZMod modulus))) =>
    show 0 ≤ (if (support other).card = (support frequency).card then
      ‖fourier palette (fun word => (mass word : ℂ)) other‖ ^ 2 else 0) from by split_ifs <;> positivity)).mp hsum
  have hzero := hterm frequency (Finset.mem_univ _)
  simp only [ite_true] at hzero
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hzero)

end
end CurrentAFT.LowDegreeCancellation
