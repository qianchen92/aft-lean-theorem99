import AFT.BinaryUniformDraw
import AFT.RationalPaletteSampler

/-! Exact target law and ticket error for the executed interval-index sampler. -/
namespace CurrentAFT.CurrentUniformDraw
open AFT AFT.BinaryArithmetic
open scoped BigOperators Classical
noncomputable section

def law (count : ℕ) (hpositive : 0 < count) (bits : ℕ) : FiniteDist (Fin count) :=
  (FiniteDist.uniform (Fin (bits + count + 1) → Fin 2)).map
    (fun word => (binaryUniformDraw count hpositive bits word).value)

theorem law_l1 (count : ℕ) (hpositive : 0 < count) (bits : ℕ) :
    (∑ index, |(law count hpositive bits).weight index -
      (letI : Nonempty (Fin count) := ⟨⟨0, hpositive⟩⟩; FiniteDist.uniform (Fin count)).weight index|) ≤ 1 / (2 : ℝ)^bits := by
  letI : Nonempty (Fin count) := ⟨⟨0, hpositive⟩⟩
  have he : (∑ color : Fin count, |(((count : ℚ)⁻¹ : ℚ) : ℝ) -
      (FiniteDist.uniform (Fin count)).weight color|) ≤ (0 : ℝ) := by
    simp only [Rat.cast_inv, Rat.cast_natCast, FiniteDist.uniform_weight, Fintype.card_fin,
      sub_self, abs_zero, Finset.sum_const_zero, le_refl]
  have h := RationalPaletteSampler.draw_l1 count hpositive (fun _ => (count : ℚ)⁻¹) bits
    (FiniteDist.uniform (Fin count)) 0 he (by norm_num)
  simpa only [law, binaryUniformDraw_value, mul_zero, add_zero] using h

end
end CurrentAFT.CurrentUniformDraw
