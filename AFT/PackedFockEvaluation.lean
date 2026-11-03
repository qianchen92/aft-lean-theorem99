import AFT.PackedFock

/-! # Decoding the finite coefficient channel gives the actual polynomial -/
namespace AFT.LocalTensors
open MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]
local instance packedFockEvaluationFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

/-- A factorial decoder of norm at most one. It converts the coefficient
Hilbert channel into its actual polynomial at the common Gaussian vector. -/
def fockDecoder (maximum : ℕ) (coordinate : PackedCoordinate maximum Color) : ℝ :=
  1 / Real.sqrt (coordinate.1.val.factorial : ℝ)

omit [Fintype Color] in
theorem fockDecoder_nonneg (maximum : ℕ) (coordinate : PackedCoordinate maximum Color) :
    0 ≤ fockDecoder maximum coordinate := by unfold fockDecoder; positivity

omit [Fintype Color] in
theorem fockDecoder_le_one (maximum : ℕ) (coordinate : PackedCoordinate maximum Color) :
    fockDecoder maximum coordinate ≤ 1 := by
  apply (div_le_one (Real.sqrt_pos.2 (by exact_mod_cast Nat.factorial_pos coordinate.1.val))).2
  exact Real.one_le_sqrt.2 (by exact_mod_cast Nat.factorial_pos coordinate.1.val)

/-- Decoding the actual local coefficient channel recovers all terms of the
literal signed generating polynomial exactly. -/
theorem packedFockChannel_evaluation (reference : FiniteDist Color) (maximum population : ℕ) (radius : ℝ)
    (hmaximum : Fintype.card Slot ≤ maximum) (mass : (Slot → Color) → ℝ) (value : Color → ℂ) :
    (∑ coordinate : PackedCoordinate maximum Color,
      ((fockDecoder maximum coordinate * packedFockChannel reference maximum population radius mass coordinate : ℝ) : ℂ) *
        TensorFock.wordMonomial coordinate.2 value) =
      localGenerating (fun _ : Slot => reference) mass
        (fun color => ((Real.sqrt 2 * (radius / Real.sqrt population) : ℝ) : ℂ) * value color) := by
  rw [localGenerating_series_of_bound _ _ maximum hmaximum]
  simp only [TensorFock.seriesEvaluation, NonlinearFock.tensorEvaluation_dilate, Fintype.card_fin]
  rw [Fintype.sum_sigma, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro degree _
  unfold TensorFock.tensorEvaluation
  apply Finset.sum_congr rfl
  intro word _
  have hs : Real.sqrt (degree.val.factorial : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast Nat.factorial_pos degree.val))
  simp only [fockDecoder, packedFockChannel, LinearMap.coe_mk, AddHom.coe_mk]
  have hsc : ((Real.sqrt (degree.val.factorial : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  push_cast
  field_simp [hsc]

/-- The marked coefficient budget is the exact Gaussian norm of the actual
polynomial, with its finite number-of-degrees prefactor. -/
theorem taggedCoefficientEnergy_gaussian (reference : FiniteDist Color) (population : ℕ) (radius : ℝ)
    (mass : (Slot → Color) → ℝ) :
    BlockProducts.taggedCoefficientEnergy reference mass population radius =
      (Fintype.card Slot + 1 : ℕ) *
        ∫ value, Complex.normSq (localGenerating (fun _ : Slot => reference) mass
          (fun color => ((Real.sqrt 2 * (radius / Real.sqrt population) : ℝ) : ℂ) * value color))
            ∂(FockGaussian.field (Coordinate := Color)) := by
  let coefficient := fun degree : ℕ => fun word : Fin degree → Color =>
    (Real.sqrt 2 * (radius / Real.sqrt population)) ^ degree *
      degreeTensor (fun _ : Slot => reference) mass degree word
  have heval (value : Color → ℂ) :
      localGenerating (fun _ : Slot => reference) mass
        (fun color => ((Real.sqrt 2 * (radius / Real.sqrt population) : ℝ) : ℂ) * value color) =
      TensorFock.seriesEvaluation (Finset.range (Fintype.card Slot + 1)) coefficient value := by
    rw [localGenerating_series]
    simp only [TensorFock.seriesEvaluation, NonlinearFock.tensorEvaluation_dilate, Fintype.card_fin]
    rfl
  simp_rw [heval]
  rw [TensorFock.complete_tensor_fock_isometry _ _ (by
    intro degree _ word permutation
    simp only [coefficient, degreeTensor_symmetric])]
  unfold BlockProducts.taggedCoefficientEnergy TensorFock.normalizedTensor BlockFock.tensorEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro degree _
  have hpow : (Real.sqrt 2 ^ degree) ^ 2 = (2 : ℝ) ^ degree := by
    rw [← pow_mul, Nat.mul_comm degree 2, pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [coefficient, mul_pow, hpow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro word _
  ring

end
end AFT.LocalTensors
