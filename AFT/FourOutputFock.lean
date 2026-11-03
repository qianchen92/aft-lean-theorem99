import AFT.SingletonFock

/-! # The complete four-output Fock scale from the sharp first response -/
namespace AFT.LocalTensors
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Color : Type*} [Fintype Color]
local instance fourOutputFockFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

/-- The first coefficient uses its calibrated estimate, while every higher
coefficient uses the complete four-output density bound. This retains the
primary `lambda^-15` norm scale across the full finite polynomial. -/
theorem four_output_fock_energy_le (reference : FiniteDist Color) (population : ℕ) (radius parameter : ℝ)
    (mass : (Fin 4 → Color) → ℝ) (hmass : ∑ word, mass word = 0)
    (firstConstant higherConstant inputEnergy : ℝ)
    (_hfirstConstant : 0 ≤ firstConstant) (hhigherConstant : 0 ≤ higherConstant) (hinput : 0 ≤ inputEnergy)
    (hparameter : 1 ≤ parameter)
    (hscale0 : 0 ≤ radius / Real.sqrt population) (hscale1 : radius / Real.sqrt population ≤ 1)
    (hscale : radius / Real.sqrt population ≤ 2 / parameter ^ 28)
    (hfirst : BlockFock.tensorEnergy (degreeTensor (fun _ : Fin 4 => reference) mass 1) ≤
      firstConstant * parameter ^ 26 * inputEnergy)
    (hhigher : ∀ degree, 2 ≤ degree → degree ≤ 4 →
      BlockFock.tensorEnergy (degreeTensor (fun _ : Fin 4 => reference) mass degree) ≤
        higherConstant * parameter ^ 46 * inputEnergy) :
    BlockProducts.taggedCoefficientEnergy reference mass population radius ≤
      ((40 * firstConstant + 35200 * higherConstant) / parameter ^ 30) * inputEnergy := by
  let scale := radius / Real.sqrt population
  let energy := fun degree => BlockFock.tensorEnergy (degreeTensor (fun _ : Fin 4 => reference) mass degree)
  have hx : 0 < parameter := lt_of_lt_of_le (by norm_num) hparameter
  have hz : energy 0 = 0 := by
    unfold energy BlockFock.tensorEnergy
    simp only [degreeTensor_zero_formula, hmass, zero_pow (by omega : 2 ≠ 0), Finset.sum_const_zero]
  have hidentity : BlockProducts.taggedCoefficientEnergy reference mass population radius =
      10 * scale ^ 2 * energy 1 + 40 * scale ^ 4 * energy 2 +
        240 * scale ^ 6 * energy 3 + 1920 * scale ^ 8 * energy 4 := by
    unfold BlockProducts.taggedCoefficientEnergy TensorFock.normalizedTensor
    simp only [TensorFock.tensorEnergy_smul, Fintype.card_fin, Finset.sum_range_succ,
      Finset.sum_range_zero, pow_zero, zero_add]
    norm_num only [Nat.factorial, Nat.reduceAdd, Nat.reduceMul, Nat.cast_ofNat,
      Nat.cast_one, Nat.cast_zero, one_mul, pow_one, Nat.reducePow]
    change 5 * (energy 0 + 2 * (scale ^ 2 * energy 1) +
      8 * ((scale ^ 2) ^ 2 * energy 2) + 48 * ((scale ^ 3) ^ 2 * energy 3) +
      384 * ((scale ^ 4) ^ 2 * energy 4)) = _
    rw [hz]
    dsimp only [scale]
    ring
  have hs2 : scale ^ 2 ≤ 4 / parameter ^ 56 := by
    calc
      _ ≤ (2 / parameter ^ 28) ^ 2 := pow_le_pow_left₀ hscale0 hscale 2
      _ = _ := by field_simp; ring
  have hs4 : scale ^ 4 ≤ 16 / parameter ^ 112 := by
    calc
      _ ≤ (2 / parameter ^ 28) ^ 4 := pow_le_pow_left₀ hscale0 hscale 4
      _ = _ := by field_simp; ring
  have hs6 : scale ^ 6 ≤ scale ^ 4 := pow_le_pow_of_le_one hscale0 hscale1 (by omega : 4 ≤ 6)
  have hs8 : scale ^ 8 ≤ scale ^ 4 := pow_le_pow_of_le_one hscale0 hscale1 (by omega : 4 ≤ 8)
  have hepos (degree : ℕ) : 0 ≤ energy degree := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have he2 := hhigher 2 (by omega) (by omega)
  have he3 := hhigher 3 (by omega) (by omega)
  have he4 := hhigher 4 (by omega) (by omega)
  have hraw : BlockProducts.taggedCoefficientEnergy reference mass population radius ≤
      10 * (4 / parameter ^ 56) * (firstConstant * parameter ^ 26 * inputEnergy) +
        2200 * (16 / parameter ^ 112) * (higherConstant * parameter ^ 46 * inputEnergy) := by
    rw [hidentity]
    calc
      _ ≤ 10 * (4 / parameter ^ 56) * (firstConstant * parameter ^ 26 * inputEnergy) +
          40 * (16 / parameter ^ 112) * (higherConstant * parameter ^ 46 * inputEnergy) +
          240 * (16 / parameter ^ 112) * (higherConstant * parameter ^ 46 * inputEnergy) +
          1920 * (16 / parameter ^ 112) * (higherConstant * parameter ^ 46 * inputEnergy) := by
        gcongr <;> first | exact hepos _ | exact hfirst | exact he2 | exact he3 | exact he4 |
          exact hs6.trans hs4 | exact hs8.trans hs4
      _ = _ := by ring
  have hxpower : parameter ^ 30 ≤ parameter ^ 66 := pow_le_pow_right₀ hparameter (by omega)
  have hratio : 1 / parameter ^ 66 ≤ 1 / parameter ^ 30 := one_div_le_one_div_of_le (by positivity) hxpower
  apply hraw.trans
  calc
    _ = (40 * firstConstant / parameter ^ 30 + 35200 * higherConstant / parameter ^ 66) * inputEnergy := by
      field_simp
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hinput
      have hh := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 35200 * higherConstant by positivity)
      calc
        _ ≤ 40 * firstConstant / parameter ^ 30 + 35200 * higherConstant / parameter ^ 30 := by
          exact add_le_add le_rfl (by simpa only [mul_one_div] using hh)
        _ = _ := by ring

end
end AFT.LocalTensors
