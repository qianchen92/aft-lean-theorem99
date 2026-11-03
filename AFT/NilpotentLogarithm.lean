import AFT.FormalLogarithm

/-! # Finite logarithms in the actual nilpotent input quotient -/

namespace AFT.FormalLogarithm

open scoped BigOperators Classical PowerSeries

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {R : Type*} [CommRing R] [Algebra ℚ R]

theorem substitution_constant_finite (inner : PowerSeries R) (outer : PowerSeries ℚ)
    (count : ℕ) (hzero : PowerSeries.constantCoeff inner ^ count = 0) :
    PowerSeries.constantCoeff (outer.subst inner) =
      ∑ index ∈ Finset.range count,
        PowerSeries.coeff index outer • PowerSeries.constantCoeff inner ^ index := by
  have hsubst : PowerSeries.HasSubst inner := ⟨count, hzero⟩
  change MvPowerSeries.constantCoeff (outer.subst inner) = _
  rw [PowerSeries.constantCoeff_subst hsubst]
  simp only [map_pow]
  apply finsum_eq_sum_of_support_subset
  intro index hindex
  by_contra hlt
  have hge : count ≤ index := by simpa using hlt
  apply hindex
  change PowerSeries.coeff index outer • PowerSeries.constantCoeff inner ^ index = 0
  rw [pow_eq_zero_of_le hge hzero, smul_zero]

theorem substitution_exp_constant (inner : PowerSeries R) (hinner : PowerSeries.HasSubst inner) :
    PowerSeries.constantCoeff ((PowerSeries.exp ℚ).subst inner) =
      IsNilpotent.exp (PowerSeries.constantCoeff inner) := by
  change IsNilpotent (PowerSeries.constantCoeff inner) at hinner
  obtain ⟨count, hzero⟩ := hinner
  rw [substitution_constant_finite inner _ count hzero, IsNilpotent.exp_eq_sum hzero]
  apply Finset.sum_congr rfl
  intro index _
  simp [PowerSeries.coeff_exp]

def finiteLogarithm (value : R) (cutoff : ℕ) : R :=
  ∑ index ∈ Finset.range cutoff,
    ((-1 : ℚ) ^ index / (index + 1)) • value ^ (index + 1)

theorem substitution_logarithm_constant (value : R) (cutoff : ℕ)
    (hzero : value ^ (cutoff + 1) = 0) :
    PowerSeries.constantCoeff (logarithm.subst (PowerSeries.C value)) =
      finiteLogarithm value cutoff := by
  rw [substitution_constant_finite _ _ (cutoff + 1) (by simpa using hzero)]
  rw [Finset.sum_range_succ']
  simp only [PowerSeries.coeff_zero_eq_constantCoeff, logarithm_constant, zero_smul,
    add_zero, PowerSeries.constantCoeff_C, logarithm_coeff_succ]
  rfl

/-- The finite sum is a logarithm because the formal exp/log identity can be
substituted at a genuinely nilpotent element. -/
theorem exp_finiteLogarithm (value : R) (cutoff : ℕ)
    (hzero : value ^ (cutoff + 1) = 0) :
    IsNilpotent.exp (finiteLogarithm value cutoff) = 1 + value := by
  have hc : PowerSeries.HasSubst (PowerSeries.C value : PowerSeries R) := by
    change IsNilpotent (PowerSeries.constantCoeff (PowerSeries.C value))
    simpa using (show IsNilpotent value from ⟨cutoff + 1, hzero⟩)
  have hl := PowerSeries.HasSubst.of_constantCoeff_zero logarithm_constant
  have hh := congrArg PowerSeries.constantCoeff
    (PowerSeries.subst_comp_subst_apply hl hc (PowerSeries.exp ℚ))
  rw [exp_logarithm, PowerSeries.subst_add hc, PowerSeries.subst_X hc] at hh
  have hcomp : PowerSeries.HasSubst (logarithm.subst (PowerSeries.C value)) := by
    simpa only [PowerSeries.coe_substAlgHom] using hl.comp hc
  rw [substitution_exp_constant _ hcomp, substitution_logarithm_constant value cutoff hzero] at hh
  simpa only [← PowerSeries.coe_substAlgHom hc, map_one, map_add, PowerSeries.constantCoeff_C] using hh.symm

end

end AFT.FormalLogarithm
