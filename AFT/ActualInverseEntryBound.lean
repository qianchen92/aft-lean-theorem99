import AFT.ActualInverseEntryProgram

/-! # Polynomial magnitude bounds for the true primary inverse entries -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance inverseEntryBoundFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

theorem actual_inverse_entry_bound_eventually (constant : ℕ) (hc : 1 ≤ constant) :
    ∀ᶠ n : ℕ in atTop,
      ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap=actualResponse (constant : ℝ) n →
      ∀ input output,|operator.symm (Pi.single input 1) output| ≤ 32*(n : ℝ)^70 := by
  have hinverse := actual_response_inverse_eventually (κ := Unit) (constant : ℝ) (by exact_mod_cast hc)
    analysisBeta Parameters.legs (by filter_upwards [] with n; exact ⟨(analysisBeta_typical n).1,(analysisBeta_typical n).2,by omega⟩)
  filter_upwards [hinverse,analysisPrimary_estimates_eventually (constant : ℝ) (by exact_mod_cast hc),
    analysisRate_bounds_eventually,eventually_ge_atTop 2] with n hi hp hr hn operator hop input output
  obtain ⟨inverse,hinverse,hbound,_⟩ := hi
  have he : operator=inverse := by
    ext profile color
    change operator.toLinearMap profile color=inverse.toLinearMap profile color
    rw [hop,hinverse]
  subst operator
  have hq : 0 < (Parameters.modulus n : ℝ) := by exact_mod_cast (Parameters.modulus_prime n).pos
  have hq1 : (1 : ℝ) ≤ Parameters.modulus n := by exact_mod_cast (Parameters.modulus_prime n).one_lt.le
  have hp' : ∀ color,0 < analysisPrimary (constant : ℝ) n color := fun color => lt_of_lt_of_le (by positivity) (hp.1 color)
  have hpInv (color : Fin (Parameters.modulus n)) : 1/analysisPrimary (constant : ℝ) n color ≤ 4*(Parameters.modulus n : ℝ) := by
    have hh := one_div_le_one_div_of_le (by positivity : 0 < 1/(4*(Parameters.modulus n : ℝ))) (hp.1 color)
    simpa only [one_div,inv_inv] using hh
  have hb := primaryActivity_single_bound (analysisPrimary (constant : ℝ) n) (analysisRate n)
    (4*(Parameters.modulus n : ℝ)) hr.1.le (by linarith) hp' (by linarith) hpInv input
  have hqbound : (Parameters.modulus n : ℝ) ≤ 2*(n : ℝ)^40 := by
    have hh := (Parameters.modulus_bounds n).2
    rw [Parameters.security_eq n hn] at hh
    exact_mod_cast hh
  have hb' : primaryActivity (analysisRate n) (analysisPrimary (constant : ℝ) n) (Pi.single input 1) ≤ 16*(n : ℝ)^40 := by
    linarith
  have hinv : primaryActivity (analysisRate n) (analysisPrimary (constant : ℝ) n)
      (inverse.symm (Pi.single input 1)) ≤ 32*(n : ℝ)^40 := by
    have hh := hbound (Pi.single input 1)
    change primaryActivity (analysisRate n) (analysisPrimary (constant : ℝ) n)
      (inverse.symm (Pi.single input 1)) ≤ 2*primaryActivity (analysisRate n)
        (analysisPrimary (constant : ℝ) n) (Pi.single input 1) at hh
    linarith
  have hpoint := primaryActivity_controls_atom (analysisPrimary (constant : ℝ) n)
    (inverse.symm (Pi.single input 1)) (analysisRate n) hr.1 hp' hp.2.1 output
  have hrateSq : (analysisRate n)^2=1/(n : ℝ)^30 := by
    unfold analysisRate
    rw [div_pow,Real.sq_sqrt (by positivity)]
    simp only [one_pow,Parameters.legs,Parameters.security_eq n hn,Nat.cast_pow]
  rw [hrateSq] at hpoint
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hh := mul_le_mul_of_nonneg_left (hpoint.trans hinv) (by positivity : 0 ≤ (n : ℝ)^30)
  have hcancel : (n : ℝ)^30*(1/(n : ℝ)^30*|inverse.symm (Pi.single input 1) output|)=|inverse.symm (Pi.single input 1) output| := by field_simp
  rw [hcancel] at hh
  exact hh.trans_eq (by ring)

end
end AFT.V7Calibration
