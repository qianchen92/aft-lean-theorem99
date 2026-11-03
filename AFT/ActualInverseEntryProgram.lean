import AFT.ActualInverseIterationCorrect

/-! # Uniform negligible entry error for the executable response inverse -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance inverseEntryProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

theorem primaryActivity_single_bound {Color : Type*} [Fintype Color] [DecidableEq Color]
    (primary : Color → ℝ) (rate bound : ℝ) (hrate : 0≤rate) (hrate1 : rate≤1)
    (hp : ∀ color,0<primary color) (hb : 1≤bound)
    (hinverse : ∀ color,1/primary color≤bound) (input : Color) :
    primaryActivity rate primary (Pi.single input 1)≤2*bound := by
  have hs : profileSquareNorm primary (Pi.single input 1)=1/primary input := by
    simp [profileSquareNorm,Pi.single_apply,ite_div]
  have hroot : Real.sqrt (1/primary input)≤bound := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by linarith,?_⟩
    nlinarith [hinverse input]
  have hnorm : ‖fun color => (Pi.single input 1 : Color → ℝ) color/primary color‖≤bound := by
    apply (pi_norm_le_iff_of_nonneg (by linarith)).mpr
    intro color
    by_cases h : color=input
    · subst color
      simpa [abs_of_pos (hp input)] using hinverse input
    · simp [h]
      linarith
  unfold primaryActivity
  rw [hs]
  have h1 := mul_le_mul hrate1 hroot (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ)≤1)
  have hrsq : rate^2≤1 := by nlinarith
  have h2 := mul_le_mul hrsq hnorm (norm_nonneg _) (by norm_num : (0 : ℝ)≤1)
  linarith

theorem primaryActivity_controls_atom {Color : Type*} [Fintype Color]
    (primary profile : Color → ℝ) (rate : ℝ) (hrate : 0<rate)
    (hp : ∀ color,0<primary color) (hmass : ∑ color,primary color=1) (output : Color) :
    rate^2*|profile output|≤primaryActivity rate primary profile := by
  have hp1 : primary output≤1 := by
    rw [←hmass]
    exact Finset.single_le_sum (fun color _ => (hp color).le) (Finset.mem_univ output)
  have hnorm : |profile output/primary output|≤‖fun color => profile color/primary color‖ := by
    simpa only [Real.norm_eq_abs] using
      norm_le_pi_norm (fun color => profile color/primary color) output
  have hvalue : |profile output|≤‖fun color => profile color/primary color‖ := by
    rw [abs_div,abs_of_pos (hp output)] at hnorm
    have hh := (div_le_iff₀ (hp output)).mp hnorm
    exact hh.trans (mul_le_of_le_one_right (norm_nonneg _) hp1)
  have hh := mul_le_mul_of_nonneg_left hvalue (sq_nonneg rate)
  unfold primaryActivity
  nlinarith [mul_nonneg hrate.le (Real.sqrt_nonneg (profileSquareNorm primary profile))]

def actualInverseEntryError (n : ℕ) : ℝ := 16*(n : ℝ)^70*actualInverseIterationError n n

theorem actualInverseIterationError_negligible : Negligible (fun n => actualInverseIterationError n n) := by
  have hg : Negligible (fun n : ℕ => 2*(1/2 : ℝ)^n) := by
    apply BetaReference.negligible_geometric_population 2 (1/2) (by norm_num) (by norm_num) (by norm_num) id
    exact Filter.Eventually.of_forall (fun n => le_rfl)
  exact (hg.add (actualRankActivityError_negligible.const_mul 10)).add (actualAnchorActivityError_negligible.const_mul 16)

theorem actualInverseEntryError_negligible : Negligible actualInverseEntryError := by
  convert (actualInverseIterationError_negligible.mul_polynomial 70).const_mul 16 using 1
  funext n
  unfold actualInverseEntryError
  ring

theorem actual_inverse_entry_program_eventually (constant : ℕ) (hc : 1≤constant) :
    ∀ᶠ n : ℕ in atTop,
      ∃ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
        operator.toLinearMap=actualResponse (constant : ℝ) n ∧
        ∀ (input output : Fin (Parameters.modulus n)),
          |(actualInverseIterationProgram constant n input.val n output.val : ℝ)-operator.symm (Pi.single input 1) output|≤
            actualInverseEntryError n := by
  filter_upwards [actual_inverse_iteration_correct_eventually constant hc,
    analysisPrimary_estimates_eventually (constant : ℝ) (by exact_mod_cast hc),analysisRate_bounds_eventually,
    eventually_ge_atTop 2] with n hi hp hr hn
  obtain ⟨operator,hop,he⟩ := hi
  refine ⟨operator,hop,?_⟩
  intro input output
  have hq : 0<(Parameters.modulus n : ℝ) := by exact_mod_cast (Parameters.modulus_prime n).pos
  have hq1 : (1 : ℝ)≤Parameters.modulus n := by exact_mod_cast (Parameters.modulus_prime n).one_lt.le
  have hp' : ∀color,0<analysisPrimary (constant : ℝ) n color := fun color => lt_of_lt_of_le (by positivity) (hp.1 color)
  have hpInv (color : Fin (Parameters.modulus n)) : 1/analysisPrimary (constant : ℝ) n color≤4*(Parameters.modulus n : ℝ) := by
    have hh := one_div_le_one_div_of_le (by positivity : 0<1/(4*(Parameters.modulus n : ℝ))) (hp.1 color)
    simpa only [one_div,inv_inv] using hh
  have hb := primaryActivity_single_bound (analysisPrimary (constant : ℝ) n) (analysisRate n)
    (4*(Parameters.modulus n : ℝ)) hr.1.le (by linarith) hp' (by linarith) hpInv input
  have hqbound : (Parameters.modulus n : ℝ)≤2*(n : ℝ)^40 := by
    have hh := (Parameters.modulus_bounds n).2
    rw [Parameters.security_eq n hn] at hh
    exact_mod_cast hh
  have hb' : primaryActivity (analysisRate n) (analysisPrimary (constant : ℝ) n) (Pi.single input 1)≤16*(n : ℝ)^40 := by
    linarith
  have herr0 : 0≤actualInverseIterationError n n := by
    unfold actualInverseIterationError
    positivity [actualRankActivityError_nonneg n,actualAnchorActivityError_nonneg n]
  have hactivity := (he input n).trans (mul_le_mul_of_nonneg_left hb' herr0)
  let difference : Fin (Parameters.modulus n) → ℝ :=
    (fun output => (actualInverseIterationProgram constant n input.val n output.val : ℝ))-operator.symm (Pi.single input 1)
  have hpoint := primaryActivity_controls_atom (analysisPrimary (constant : ℝ) n) difference (analysisRate n) hr.1 hp' hp.2.1 output
  have hrateSq : (analysisRate n)^2=1/(n : ℝ)^30 := by
    unfold analysisRate
    rw [div_pow,Real.sq_sqrt (by positivity)]
    simp only [one_pow,Parameters.legs,Parameters.security_eq n hn,Nat.cast_pow]
  rw [hrateSq] at hpoint
  have hn0 : 0<(n : ℝ) := by exact_mod_cast (by omega : 0<n)
  have hcombined := hpoint.trans hactivity
  have hh := mul_le_mul_of_nonneg_left hcombined (by positivity : 0≤(n : ℝ)^30)
  have hcancel : (n : ℝ)^30*(1/(n : ℝ)^30*|difference output|)=|difference output| := by field_simp
  rw [hcancel] at hh
  apply hh.trans_eq
  unfold actualInverseEntryError
  ring

end
end AFT.V7Calibration
