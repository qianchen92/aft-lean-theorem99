import AFT.FairBitSampling
import AFT.RejectionCoin

/-! # Executable acceptance coins from rational score approximations

All executable definitions use rational or integer arithmetic. Approximating
the actual real score is a separate obligation, not a real-floor oracle.
-/
namespace AFT.RationalAcceptanceCoin
open scoped BigOperators

/-- Clipping a rational approximation ensures a legal acceptance coin. -/
def clipped (value : ℚ) : ℚ := min 1 (max value 0)

theorem clipped_bounds (value : ℚ) : 0 ≤ clipped value ∧ clipped value ≤ 1 :=
  ⟨le_min (by norm_num) (le_max_right _ _),min_le_left _ _⟩

def count (bits : ℕ) (value : ℚ) : ℕ := ⌊(2^bits : ℚ)*clipped value⌋₊

theorem count_le (bits : ℕ) (value : ℚ) : count bits value ≤ 2^bits := by
  have hh := Nat.floor_le (mul_nonneg (by positivity : (0 : ℚ) ≤ 2^bits) (clipped_bounds value).1)
  have hmul := mul_le_mul_of_nonneg_left (clipped_bounds value).2 (by positivity : (0 : ℚ) ≤ 2^bits)
  have hc : (count bits value : ℚ) ≤ (2^bits : ℕ) := by
    simpa only [count,mul_one,Nat.cast_pow,Nat.cast_ofNat] using hh.trans hmul
  exact_mod_cast hc

def counts (bits : ℕ) (value : ℚ) : Fin 2 → ℕ := ![count bits value,2^bits-count bits value]

theorem counts_total (bits : ℕ) (value : ℚ) : ∑ i,counts bits value i=2^bits := by
  have hc := count_le bits value
  simp only [counts,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  omega

/-- Output zero means acceptance. The procedure consumes exactly `bits`
fair bits and performs rational rounding followed by integer table selection. -/
def draw (bits : ℕ) (value : ℚ) (word : Fin bits → Fin 2) : Fin 2 :=
  FiniteTicketSampler.drawBitTable bits (counts bits value) (counts_total bits value) word

noncomputable section

def probability (bits : ℕ) (value : ℚ) : ℝ := (count bits value : ℝ)/(2 : ℝ)^bits

theorem draw_acceptance (bits : ℕ) (value : ℚ) :
    ((FiniteDist.independent (fun _ : Fin bits => FiniteDist.uniform (Fin 2))).map
      (draw bits value)).weight 0=probability bits value := by
  exact FiniteTicketSampler.drawBitTable_law bits (counts bits value) (counts_total bits value) 0

theorem probability_bounds (bits : ℕ) (value : ℚ) :
    0 ≤ probability bits value ∧ probability bits value ≤ 1 := by
  refine ⟨by unfold probability; positivity,?_⟩
  apply (div_le_one (by positivity : (0 : ℝ) < 2^bits)).mpr
  exact_mod_cast count_le bits value

theorem probability_floor_error (bits : ℕ) (value : ℚ) :
    |probability bits value-(clipped value : ℝ)| ≤ 1/(2 : ℝ)^bits := by
  have hlo := Nat.floor_le (mul_nonneg (by positivity : (0 : ℚ) ≤ 2^bits) (clipped_bounds value).1)
  have hhi := Nat.lt_floor_add_one ((2^bits : ℚ)*clipped value)
  have hlod : (count bits value : ℚ) ≤ (2 : ℚ)^bits*clipped value := by simpa only [count] using hlo
  have hlo' : (count bits value : ℝ) ≤ (2 : ℝ)^bits*(clipped value : ℝ) := by exact_mod_cast hlod
  have hhid : (2 : ℚ)^bits*clipped value ≤ (count bits value : ℚ)+1 := by simpa only [count] using hhi.le
  have hhi' : (2 : ℝ)^bits*(clipped value : ℝ) ≤ (count bits value : ℝ)+1 := by exact_mod_cast hhid
  have hp : (0 : ℝ) < 2^bits := by positivity
  have he : probability bits value-(clipped value : ℝ)=
      ((count bits value : ℝ)-(2 : ℝ)^bits*(clipped value : ℝ))/(2 : ℝ)^bits := by
    unfold probability
    field_simp
  rw [he,abs_div,abs_of_pos hp]
  apply div_le_div_of_nonneg_right _ hp.le
  rw [abs_le]
  constructor <;> linarith

/-- Clipping does not amplify error against any legal target probability. -/
theorem clipped_error (value : ℚ) (target : ℝ) (ht : 0 ≤ target ∧ target ≤ 1) :
    |(clipped value : ℝ)-target| ≤ |(value : ℝ)-target| := by
  have he : (clipped value : ℝ)=min 1 (max (value : ℝ) 0) := by
    simp [clipped]
  rw [he]
  by_cases hv : (value : ℝ) ≤ 0
  · rw [max_eq_right hv,min_eq_right (by norm_num : (0 : ℝ) ≤ 1),zero_sub,abs_neg,
      abs_of_nonneg ht.1,abs_of_nonpos (by linarith : (value : ℝ)-target ≤ 0)]
    linarith
  · rw [max_eq_left (by linarith : (0 : ℝ) ≤ value)]
    by_cases hv1 : (value : ℝ) ≤ 1
    · rw [min_eq_right hv1]
    · rw [min_eq_left (by linarith : (1 : ℝ) ≤ value),
        abs_of_nonneg (by linarith : 0 ≤ (1 : ℝ)-target),
        abs_of_nonneg (by linarith : 0 ≤ (value : ℝ)-target)]
      linarith

theorem probability_error (bits : ℕ) (value : ℚ) (target : ℝ)
    (ht : 0 ≤ target ∧ target ≤ 1) :
    |probability bits value-target| ≤ 1/(2 : ℝ)^bits+|(value : ℝ)-target| := by
  calc
    _ ≤ |probability bits value-(clipped value : ℝ)|+|(clipped value : ℝ)-target| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add (probability_floor_error bits value) (clipped_error value target ht)

/-- A genuinely executable rational coin replaces any ideal real coin in
a capped loop. Only its numerical approximation error remains as a premise. -/
theorem cappedRejection_error {State : Type*} [Fintype State]
    (proposal fallback : FiniteDist State) (target : State → ℝ)
    (ht : ∀ point,0 ≤ target point ∧ target point ≤ 1)
    (approximation : State → ℚ) (bits attempts : ℕ) (error : ℝ)
    (herror : ∀ point,|(approximation point : ℝ)-target point| ≤ error) :
    FiniteDist.TVBound
      (proposal.cappedRejection (fun point => probability bits (approximation point))
        (fun point => probability_bounds bits (approximation point)) fallback attempts)
      (proposal.cappedRejection target ht fallback attempts)
      ((attempts : ℝ)*(1/(2 : ℝ)^bits+error)) :=
  FiniteDist.cappedRejection_coin_tv proposal _ target _ ht fallback _
    (fun point => (probability_error bits (approximation point) (target point) (ht point)).trans
      (add_le_add (le_refl _) (herror point))) attempts

end
end AFT.RationalAcceptanceCoin
