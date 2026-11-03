import CurrentAFT.OptionRejection
import AFT.BinaryRejectionLoop

/-! # The finite binary coin approximates the actual clipped public weight -/
namespace CurrentAFT.ClippedRejectionCoin
open AFT
set_option maxHeartbeats 400000

def raw (accepted : Bool) (score : ℚ) : ℚ := if accepted then score else 0

noncomputable section
open scoped Classical

def probability (bits : ℕ) (accepted : Bool) (score : ℚ) : ℝ :=
  RationalAcceptanceCoin.probability bits (max (raw accepted score) 0 / 2)

theorem bounds (bits : ℕ) (accepted : Bool) (score : ℚ) :
    0 ≤ probability bits accepted score ∧ probability bits accepted score ≤ 1 :=
  RationalAcceptanceCoin.probability_bounds _ _

theorem clipped_ratio (score : ℚ) :
    (RationalAcceptanceCoin.clipped (max score 0 / 2) : ℝ) = clip (score : ℝ)/2 := by
  have hn : (0 : ℝ) ≤ max (score : ℝ) 0 / 2 := by positivity
  simp only [RationalAcceptanceCoin.clipped, Rat.cast_min, Rat.cast_max, Rat.cast_div,
    Rat.cast_ofNat, Rat.cast_zero, Rat.cast_one]
  rw [max_eq_left hn]
  rw [show (1 : ℝ) = 2/2 by norm_num]
  rw [min_div_div_right (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [clip, max_comm]

theorem probability_error (bits : ℕ) (accepted : Bool) (score : ℚ) (target error : ℝ)
    (he : 0 ≤ error) (herror : |(score : ℝ)-target| ≤ error) :
    |probability bits accepted score - (if accepted then clip target/2 else 0)| ≤
      1/(2 : ℝ)^bits+error/2 := by
  cases accepted with
  | false =>
    norm_num [probability, raw, RationalAcceptanceCoin.probability, RationalAcceptanceCoin.count,
      RationalAcceptanceCoin.clipped]
    positivity
  | true =>
    simp only [probability, raw, if_true]
    have hf := RationalAcceptanceCoin.probability_floor_error bits (max score 0/2)
    rw [clipped_ratio] at hf
    have hc : |clip (score : ℝ)/2-clip target/2| ≤ error/2 := by
      rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact div_le_div_of_nonneg_right ((clip_abs_sub_le _ _).trans herror) (by norm_num)
    exact (abs_sub_le _ _ _).trans (add_le_add hf hc)

theorem false_probability (bits : ℕ) (score : ℚ) : probability bits false score = 0 := by
  norm_num [probability, raw, RationalAcceptanceCoin.probability, RationalAcceptanceCoin.count,
    RationalAcceptanceCoin.clipped]

def optionCoin {Core : Type*} (bits : ℕ) (accepted : Core → Bool) (score : Core → ℚ) : Option Core → ℝ
  | none => 0
  | some core => probability bits (accepted core) (score core)

theorem option_bounds {Core : Type*} (bits : ℕ) (accepted : Core → Bool) (score : Core → ℚ) :
    ∀ core, 0 ≤ optionCoin bits accepted score core ∧ optionCoin bits accepted score core ≤ 1 := by
  intro core
  cases core with
  | none => exact ⟨le_rfl, by norm_num [optionCoin]⟩
  | some core => exact bounds bits (accepted core) (score core)

theorem option_error {Core : Type*} (bits : ℕ) (accepted : Core → Bool) (score : Core → ℚ)
    (target : Core → ℝ) (predicate : Core → Prop) (error : ℝ) (he : 0 ≤ error)
    (haccepted : ∀ core, accepted core = true ↔ predicate core)
    (herror : ∀ core, |(score core : ℝ)-target core| ≤ error) (core : Option Core) :
    |optionCoin bits accepted score core -
      clippedChargeCoin (OptionRejection.weight target) (OptionRejection.charge predicate) core| ≤
      1/(2 : ℝ)^bits+error/2 := by
  cases core with
  | none => simp only [optionCoin, clippedChargeCoin, OptionRejection.charge, if_false, sub_self, abs_zero]; positivity
  | some core =>
    have h := probability_error bits (accepted core) (score core) (target core) error he (herror core)
    simpa only [optionCoin, clippedChargeCoin, OptionRejection.charge, OptionRejection.weight, haccepted] using h

end
end CurrentAFT.ClippedRejectionCoin
