import CurrentAFT.AffineFlagLaw
import CurrentAFT.Parameters
import AFT.BoundaryChartParameters

/-!
# Feasibility at the current polynomial parameters

Only the generic finite palette-count lemmas are reused from the old library.
All sizes and all numerical estimates in this file use `CurrentAFT.Parameters`.
-/

namespace CurrentAFT.AffineFlagCalibration

open AFT AFT.BoundaryCalibration
open scoped BigOperators Classical

noncomputable section

private theorem small_budget (x S : ℝ) (hx : 1 ≤ x) (hS0 : 0 ≤ S) (hS : S ≤ 4 * x ^ 4) :
    let δ := 1 / (1024 * x ^ 12)
    δ < 1 ∧ (2 * S + 1) * δ ≤ 1 / 4 ∧
      S / (1 - δ) * (δ + ((2 * S + 1) * δ) / (1 - (2 * S + 1) * δ)) ≤ 1 / 3 := by
  dsimp only
  let δ := 1 / (1024 * x ^ 12)
  let b := (2 * S + 1) * δ
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hx4 : 1 ≤ x ^ 4 := one_le_pow₀ hx
  have hx12 : 1 ≤ x ^ 12 := one_le_pow₀ hx
  have h412 : x ^ 4 ≤ x ^ 12 := pow_le_pow_right₀ hx (by omega)
  have h812 : x ^ 8 ≤ x ^ 12 := pow_le_pow_right₀ hx (by omega)
  have hδ0 : 0 ≤ δ := by dsimp [δ]; positivity
  have hδ : δ ≤ 1 / 1024 := by
    dsimp [δ]
    apply (div_le_iff₀ (by positivity : 0 < 1024 * x ^ 12)).mpr
    nlinarith
  have htwo : 2 * S + 1 ≤ 9 * x ^ 4 := by linarith
  have hb0 : 0 ≤ b := mul_nonneg (by linarith) hδ0
  have hb : b ≤ 9 / 1024 := by
    dsimp [b, δ]
    rw [mul_one_div, div_le_iff₀ (by positivity : 0 < 1024 * x ^ 12)]
    nlinarith
  have hSδ : S * δ ≤ 1 / 256 := by
    dsimp [δ]
    rw [mul_one_div, div_le_iff₀ (by positivity : 0 < 1024 * x ^ 12)]
    nlinarith
  have hSb : S * b ≤ 9 / 256 := by
    have hm := mul_le_mul hS htwo (by linarith : 0 ≤ 2 * S + 1) (by positivity : 0 ≤ 4 * x ^ 4)
    have hpow : (4 * x ^ 4) * (9 * x ^ 4) = 36 * x ^ 8 := by ring
    rw [hpow] at hm
    dsimp [b, δ]
    rw [← mul_assoc, mul_one_div, div_le_iff₀ (by positivity : 0 < 1024 * x ^ 12)]
    nlinarith
  have hd1 : 0 < 1 - δ := by linarith
  have hb1 : 0 < 1 - b := by linarith
  have hden : (1 : ℝ) / 4 ≤ (1 - δ) * (1 - b) := by
    have hm := mul_le_mul (by linarith : (1 : ℝ) / 2 ≤ 1 - δ)
      (by linarith : (1 : ℝ) / 2 ≤ 1 - b) (by norm_num : (0 : ℝ) ≤ 1 / 2) hd1.le
    norm_num at hm
    exact hm
  refine ⟨by linarith, by change b ≤ _; linarith, ?_⟩
  change S / (1 - δ) * (δ + b / (1 - b)) ≤ _
  rw [show S / (1 - δ) * (δ + b / (1 - b)) =
      (S * δ * (1 - b) + S * b) / ((1 - δ) * (1 - b)) by
        field_simp]
  rw [div_le_iff₀ (mul_pos hd1 hb1)]
  have hm : S * δ * (1 - b) ≤ S * δ := by nlinarith [mul_nonneg (mul_nonneg hS0 hδ0) hb0]
  nlinarith

def legDeletionUpper (security : ℕ) : ℝ :=
  1 / (1024 * (Parameters.base security : ℝ) ^ 12)

abbrev ProtectedInput (security : ℕ) :=
  GaussianSource.Window (Parameters.sourceCutoff security - 1) ×
    GaussianSource.Window (Parameters.sourceCutoff security - 1)

def legOffsetBound (security : ℕ) : ℤ :=
  2 * (Parameters.anchorWidth security : ℤ) + Parameters.sourceCutoff security - 1

theorem leg_trimmed_room (security : ℕ) :
    2 + legOffsetBound security + (Parameters.sourceCutoff security - 1 : ℕ) <
      (Parameters.modulus security : ℤ) := by
  have hb : 1 ≤ Parameters.base security := (Parameters.base_ge_two security).trans' (by omega)
  have hp : 0 < Parameters.base security ^ 64 := pow_pos (Parameters.base_pos security) _
  have hA : Parameters.anchorWidth security ≤ Parameters.base security ^ 64 := by
    simpa only [Parameters.anchorWidth, Parameters.scale, ← pow_mul] using
      Nat.pow_le_pow_right hb (show 48 ≤ 64 by omega)
  have hB : Parameters.sourceCutoff security ≤ Parameters.base security ^ 64 :=
    Nat.pow_le_pow_right hb (show 2 ≤ 64 by omega)
  have hBpos : 0 < Parameters.sourceCutoff security := pow_pos (Parameters.base_pos security) _
  have hq := (Parameters.modulus_bounds security).1
  have hclear : 2 * Parameters.anchorWidth security + 2 * Parameters.sourceCutoff security <
      Parameters.modulus security := by omega
  dsimp only [legOffsetBound]
  omega

theorem leg_input_separation (security : ℕ) :
    2 * (Parameters.sourceCutoff security - 1) < Parameters.modulus security := by
  have h := leg_trimmed_room security
  have hA : (0 : ℤ) ≤ Parameters.anchorWidth security := Int.natCast_nonneg _
  dsimp only [legOffsetBound] at h
  omega

theorem protectedInput_count_le (security : ℕ) :
    (Fintype.card (ProtectedInput security) : ℝ) ≤ 4 * (Parameters.base security : ℝ) ^ 4 := by
  rw [protectedInputs_card]
  have hB : 0 < Parameters.sourceCutoff security := pow_pos (Parameters.base_pos security) _
  have hcount : 2 * (Parameters.sourceCutoff security - 1) + 1 ≤ 2 * Parameters.sourceCutoff security := by omega
  have hsquare := Nat.pow_le_pow_left hcount 2
  have hh : ((2 * Parameters.sourceCutoff security) ^ 2 : ℕ) = 4 * Parameters.base security ^ 4 := by
    simp only [Parameters.sourceCutoff]
    ring
  rw [hh] at hsquare
  exact_mod_cast hsquare

theorem leg_budget_conditions (security : ℕ) :
    0 ≤ legDeletionUpper security ∧ legDeletionUpper security < 1 ∧
      (2 * Fintype.card (ProtectedInput security) + 1) * legDeletionUpper security ≤ 1 / 4 ∧
      (Fintype.card (ProtectedInput security) : ℝ) / (1 - legDeletionUpper security) *
        (legDeletionUpper security +
          ((2 * Fintype.card (ProtectedInput security) + 1) * legDeletionUpper security) /
            (1 - (2 * Fintype.card (ProtectedInput security) + 1) * legDeletionUpper security)) ≤ 1 / 3 := by
  have h := small_budget (Parameters.base security : ℝ) (Fintype.card (ProtectedInput security))
    (by exact_mod_cast (show 1 ≤ Parameters.base security from by have := Parameters.base_ge_two security; omega))
    (Nat.cast_nonneg _) (protectedInput_count_le security)
  exact ⟨by unfold legDeletionUpper; positivity, h⟩

local instance currentModulusNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩

theorem protectedPalette_current_budget (security : ℕ) (baseline : ℤ)
    (hbaseline : |baseline| ≤ legOffsetBound security) :
    affineDeletionBudget (protectedPalettes (Parameters.sourceCutoff security - 1)
      (Parameters.modulus security) 1 baseline) ≤ legDeletionUpper security := by
  have hbudget := protectedPalette_budget (Parameters.sourceCutoff security - 1)
    (Parameters.modulus security) 1 baseline (legOffsetBound security) (by norm_num)
    hbaseline (by simpa using leg_trimmed_room security)
  apply hbudget.trans
  let x : ℝ := Parameters.base security
  let S : ℝ := ((2 * (Parameters.sourceCutoff security - 1) + 1 : ℕ) : ℝ) ^ 2
  let d : ℝ := 2 + (legOffsetBound security : ℝ) + (Parameters.sourceCutoff security - 1 : ℕ)
  have hx : 1 ≤ x := by
    dsimp [x]
    exact_mod_cast (show 1 ≤ Parameters.base security from by have := Parameters.base_ge_two security; omega)
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hBpos : 0 < Parameters.sourceCutoff security := pow_pos (Parameters.base_pos security) _
  have hS : S ≤ 4 * x ^ 4 := by
    simpa only [S, x, protectedInputs_card, Nat.cast_pow] using protectedInput_count_le security
  have hB : (Parameters.sourceCutoff security : ℝ) ≤ x ^ 48 := by
    simpa only [Parameters.sourceCutoff, Nat.cast_pow, x] using
      pow_le_pow_right₀ hx (show 2 ≤ 48 by omega)
  have hd : d ≤ 4 * x ^ 48 := by
    have heq : d = 2 * x ^ 48 + 2 * (Parameters.sourceCutoff security : ℝ) := by
      dsimp only [d, legOffsetBound, x]
      push_cast
      rw [Nat.cast_sub (by omega : 1 ≤ Parameters.sourceCutoff security)]
      simp only [Parameters.anchorWidth, Parameters.scale, Nat.cast_pow, ← pow_mul]
      ring
    rw [heq]
    linarith
  have hd0 : 0 ≤ d := by
    have hT : 0 ≤ legOffsetBound security := by
      dsimp only [legOffsetBound]
      omega
    dsimp only [d]
    have hTR : (0 : ℝ) ≤ (legOffsetBound security : ℝ) := by exact_mod_cast hT
    exact add_nonneg (add_nonneg (by norm_num) hTR) (Nat.cast_nonneg _)
  have hq : (65536 : ℝ) * x ^ 64 ≤ Parameters.modulus security := by
    dsimp [x]
    exact_mod_cast (Parameters.modulus_bounds security).1
  have hq0 : (0 : ℝ) < Parameters.modulus security :=
    lt_of_lt_of_le (by positivity) hq
  have hnum : 1 + S * d ≤ 17 * x ^ 52 := by
    have hm := mul_le_mul hS hd hd0 (by positivity : 0 ≤ 4 * x ^ 4)
    have heq : (4 * x ^ 4) * (4 * x ^ 48) = 16 * x ^ 52 := by ring
    rw [heq] at hm
    nlinarith [one_le_pow₀ hx (n := 52)]
  simp only [Int.cast_one, mul_one]
  change (1 + S * d) / Parameters.modulus security ≤ 1 / (1024 * x ^ 12)
  apply (div_le_iff₀ hq0).mpr
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : 0 < 1024 * x ^ 12)]
  have hm := mul_le_mul_of_nonneg_right hnum (by positivity : 0 ≤ 1024 * x ^ 12)
  have heq : (17 * x ^ 52) * (1024 * x ^ 12) = 17408 * x ^ 64 := by ring
  rw [heq] at hm
  nlinarith [pow_nonneg hx0.le 64]

end
end CurrentAFT.AffineFlagCalibration
