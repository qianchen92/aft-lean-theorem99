import CurrentAFT.CurrentCoreProposalRates

/-! A fixed polynomial amount of table precision discharges the actual
primary-positivity budget for every security parameter. Requested ticket
precision remains dynamic. -/
namespace CurrentAFT.CurrentProposalPrecision
open AFT CurrentCoreProposalRates CurrentReferenceDraw
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
attribute [local irreducible] Parameters.base

abbrev padding (security : ℕ) : ℕ := 2^44 * (security + 2)^226
abbrev tableBits (security bits : ℕ) : ℕ := bits + padding security

theorem padding_primary_budget (security : ℕ) :
    256 * Parameters.base security * Parameters.dimension security * Parameters.modulus security ≤ padding security := by
  have hb : 1 ≤ Parameters.base security := (Parameters.base_ge_two security).trans' (by decide)
  calc
    _ ≤ 256 * Parameters.base security * (131074 * Parameters.base security^160) *
        (131072 * Parameters.base security^64) := by
      gcongr
      · exact (Parameters.dimension_bounds security).2
      · exact (Parameters.modulus_bounds security).2
    _ = (256 * 131074 * 131072) * Parameters.base security^225 := by
      rw [show (225 : ℕ) = 1 + 160 + 64 from rfl, pow_add, pow_add, pow_one]
      ac_rfl
    _ ≤ 2^44 * Parameters.base security^226 := Nat.mul_le_mul (by norm_num)
      (Nat.pow_le_pow_right hb (by decide))
    _ = padding security := by simp only [padding, Parameters.base]

theorem padding_base_budget (security : ℕ) : 4 * Parameters.base security ≤ padding security := by
  have hb : 1 ≤ Parameters.base security := (Parameters.base_ge_two security).trans' (by decide)
  have h := Nat.mul_le_mul (by norm_num : 4 ≤ 2^44)
    (Nat.pow_le_pow_right hb (by decide : 1 ≤ 226))
  simpa only [pow_one, Parameters.base] using h

private theorem padding_le_pow (security bits : ℕ) :
    (padding security : ℝ) ≤ (2 : ℝ)^tableBits security bits := by
  have h := (Nat.lt_two_pow_self (n := padding security)).le.trans
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by change padding security ≤ bits + padding security; omega : padding security ≤ tableBits security bits))
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using (Nat.cast_le (α := ℝ)).mpr h

theorem precision_conditions (security bits : ℕ) :
    ticketError (tableBits security bits) ≤ 1 / (4 * (Parameters.base security : ℝ)) ∧
    64 * (Parameters.base security : ℝ) * Parameters.dimension security * ticketError (tableBits security bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)) := by
  have hb : (0 : ℝ) < Parameters.base security := Nat.cast_pos.mpr (Parameters.base_pos security)
  have hq : (0 : ℝ) < Parameters.modulus security := Nat.cast_pos.mpr (Parameters.modulus_spec security).2.pos
  have hfour₀ : (4 : ℝ) * Parameters.base security ≤ (padding security : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using (Nat.cast_le (α := ℝ)).mpr (padding_base_budget security)
  have hfull₀ : (256 : ℝ) * Parameters.base security * Parameters.dimension security * Parameters.modulus security ≤
      (padding security : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using (Nat.cast_le (α := ℝ)).mpr (padding_primary_budget security)
  have hfour : (4 : ℝ) * Parameters.base security ≤ (2 : ℝ)^tableBits security bits :=
    hfour₀.trans (padding_le_pow security bits)
  have hfull : (256 : ℝ) * Parameters.base security * Parameters.dimension security * Parameters.modulus security ≤
      (2 : ℝ)^tableBits security bits := hfull₀.trans (padding_le_pow security bits)
  constructor
  · exact one_div_le_one_div_of_le (by positivity) hfour
  · apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * Parameters.modulus security)).mpr
    calc
      64 * (Parameters.base security : ℝ) * Parameters.dimension security * ticketError (tableBits security bits) *
          (4 * Parameters.modulus security) =
          (256 * (Parameters.base security : ℝ) * Parameters.dimension security * Parameters.modulus security) /
            (2 : ℝ)^tableBits security bits := by
              unfold ticketError
              rw [div_eq_mul_inv, div_eq_mul_inv, one_mul, show (256 : ℝ) = 64 * 4 by norm_num]
              ac_rfl
      _ ≤ 1 := (div_le_one₀ (by positivity)).mpr hfull

theorem proposal_l1 (security bits : ℕ) (cache : Cache security (tableBits security bits)) :
    (∑ core, |(CurrentCoreProposalLaw.law security (tableBits security bits) bits cache).weight core -
      (ActualPublicCharge.proposal security).weight core|) ≤ error security (tableBits security bits) bits :=
  CurrentCoreProposalRates.proposal_l1 security (tableBits security bits) bits cache
    (precision_conditions security bits).1 (precision_conditions security bits).2

noncomputable def paddingPolynomial : Polynomial ℕ := 2^44 * (Polynomial.X + 2)^226
@[simp] theorem paddingPolynomial_eval (security : ℕ) : paddingPolynomial.eval security = padding security := by
  simp only [paddingPolynomial, padding, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat]

end
end CurrentAFT.CurrentProposalPrecision
