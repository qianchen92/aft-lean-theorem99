import CurrentAFT.NumericalWeightRates

/-! Polynomial envelopes in the current security base. These are analytic
bounds on explicitly defined errors, not parameters of an executable program. -/
namespace CurrentAFT
open AFT
noncomputable section

def PolynomialErrorEnvelope (value : ℕ → ℝ) : Prop :=
  ∃ constant : ℝ, ∃ degree : ℕ, 0 ≤ constant ∧
    ∀ security, |value security| ≤ constant*(Parameters.base security : ℝ)^degree

namespace PolynomialErrorEnvelope
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.dimension Parameters.bodySize

theorem constant (value : ℝ) : PolynomialErrorEnvelope (fun _ => value) :=
  ⟨|value|, 0, abs_nonneg _, fun _ => by simp⟩

theorem mono {value bound : ℕ → ℝ} (h : PolynomialErrorEnvelope bound)
    (hle : ∀ security, |value security| ≤ |bound security|) : PolynomialErrorEnvelope value := by
  obtain ⟨C, d, hC, hh⟩ := h
  exact ⟨C, d, hC, fun n => (hle n).trans (hh n)⟩

theorem add {first second : ℕ → ℝ} (h : PolynomialErrorEnvelope first) (g : PolynomialErrorEnvelope second) :
    PolynomialErrorEnvelope (fun n => first n+second n) := by
  obtain ⟨C, c, hC, hc⟩ := h
  obtain ⟨D, d, hD, hd⟩ := g
  refine ⟨C+D, c+d, add_nonneg hC hD, fun n => ?_⟩
  have hb : (1 : ℝ) ≤ Parameters.base n := by exact_mod_cast (Parameters.base_ge_two n).trans' (by norm_num)
  have hfirst := pow_le_pow_right₀ hb (Nat.le_add_right c d)
  have hsecond := pow_le_pow_right₀ hb (Nat.le_add_left d c)
  exact (abs_add_le _ _).trans (((add_le_add (hc n) (hd n)).trans
    (add_le_add (mul_le_mul_of_nonneg_left hfirst hC) (mul_le_mul_of_nonneg_left hsecond hD))).trans_eq (by ring))

theorem mul {first second : ℕ → ℝ} (h : PolynomialErrorEnvelope first) (g : PolynomialErrorEnvelope second) :
    PolynomialErrorEnvelope (fun n => first n*second n) := by
  obtain ⟨C, c, hC, hc⟩ := h
  obtain ⟨D, d, hD, hd⟩ := g
  refine ⟨C*D, c+d, mul_nonneg hC hD, fun n => ?_⟩
  rw [abs_mul]
  apply (mul_le_mul (hc n) (hd n) (abs_nonneg _) (by positivity)).trans_eq
  rw [pow_add]
  ring

theorem pow {value : ℕ → ℝ} (h : PolynomialErrorEnvelope value) (power : ℕ) :
    PolynomialErrorEnvelope (fun n => value n^power) := by
  obtain ⟨C, d, hC, hh⟩ := h
  refine ⟨C^power, d*power, pow_nonneg hC _, fun n => ?_⟩
  rw [abs_pow]
  apply (pow_le_pow_left₀ (abs_nonneg _) (hh n) power).trans_eq
  rw [mul_pow, ← pow_mul]

theorem neg {value : ℕ → ℝ} (h : PolynomialErrorEnvelope value) : PolynomialErrorEnvelope (fun n => -value n) :=
  h.mono (fun _ => by rw [abs_neg])

theorem absolute {value : ℕ → ℝ} (h : PolynomialErrorEnvelope value) : PolynomialErrorEnvelope (fun n => |value n|) :=
  h.mono (fun _ => by rw [abs_abs])

theorem sub {first second : ℕ → ℝ} (h : PolynomialErrorEnvelope first) (g : PolynomialErrorEnvelope second) :
    PolynomialErrorEnvelope (fun n => first n-second n) := by
  simpa only [sub_eq_add_neg] using h.add g.neg

theorem sum {Index : Type*} (indices : Finset Index) (value : Index → ℕ → ℝ)
    (h : ∀ index ∈ indices, PolynomialErrorEnvelope (value index)) :
    PolynomialErrorEnvelope (fun security => ∑ index ∈ indices, value index security) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using constant 0
  | @insert index indices hnot ih =>
    simp only [Finset.sum_insert hnot]
    exact (h index (Finset.mem_insert_self _ _)).add
      (ih (fun element hm => h element (Finset.mem_insert_of_mem hm)))

theorem div_ge_one {value denominator : ℕ → ℝ} (h : PolynomialErrorEnvelope value)
    (hd : ∀ n, 1 ≤ denominator n) : PolynomialErrorEnvelope (fun n => value n/denominator n) := by
  apply h.mono
  intro n
  rw [abs_div]
  exact div_le_self (abs_nonneg _) ((hd n).trans (le_abs_self _))

theorem base : PolynomialErrorEnvelope (fun n => (Parameters.base n : ℝ)) :=
  ⟨1, 1, by norm_num, fun _ => by rw [abs_of_nonneg (Nat.cast_nonneg _), pow_one, one_mul]⟩

theorem modulus : PolynomialErrorEnvelope (fun n => (Parameters.modulus n : ℝ)) := by
  refine ⟨131072, 64, by norm_num, fun n => ?_⟩
  dsimp only
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (Parameters.modulus_bounds n).2

theorem dimension : PolynomialErrorEnvelope (fun n => (Parameters.dimension n : ℝ)) := by
  refine ⟨131074, 160, by norm_num, fun n => ?_⟩
  dsimp only
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (Parameters.dimension_bounds n).2

theorem legs : PolynomialErrorEnvelope (fun n => (Parameters.legCount n : ℝ)) := by
  simpa only [Parameters.legCount_eq, Nat.cast_pow] using base.pow 128

theorem body : PolynomialErrorEnvelope (fun n => (Parameters.bodySize n : ℝ)) := by
  apply dimension.mono
  intro n
  rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (show Parameters.bodySize n ≤ Parameters.dimension n by rw [Parameters.dimension]; omega)

theorem dyadic {value : ℕ → ℝ} (h : PolynomialErrorEnvelope value) :
    Negligible (fun security => value security*(1/(2 : ℝ)^security)) := by
  obtain ⟨C, d, hC, hh⟩ := h
  have hdyadic : Negligible (fun security => 1/(2 : ℝ)^security) := by
    simpa only [pow_zero, mul_one, one_mul, div_pow, one_pow] using
      CalibrationPrecisionRates.polynomial_geometric_negligible 1 0 (1/2) (by norm_num) (by norm_num) (by norm_num)
  exact NumericalWeightRates.negligible_bounded_factor hdyadic C d hh

end PolynomialErrorEnvelope
end
end CurrentAFT
