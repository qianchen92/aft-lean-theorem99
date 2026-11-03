import AFT.ActualPrimaryReciprocalProgram
import AFT.ActualInverseEntryBound

/-! # Executable density-conjugated inverse entries for actual joint seeds -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators

def actualDensityInverseProgram (constant n : ℕ) (beta : ℚ) (input output : ℕ) : ℚ :=
  actualActivationInverseApprox constant n n * probabilityClamp (actualPrimaryProgram constant n beta input) *
    actualInverseIterationProgram constant n input n output * actualPrimaryReciprocalProgram constant n beta output

noncomputable section
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
local instance densityInverseProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def actualDensityInverseProgramError (n : ℕ) : ℝ :=
  (4*64^4 : ℝ)*(n : ℝ)^280*(actualActivationInverseError n+actualPrimaryProgramError n+
    actualInverseEntryError n+actualPrimaryReciprocalProgramError n)

theorem actualDensityInverseProgramError_negligible : Negligible actualDensityInverseProgramError := by
  convert ((((actualActivationInverseError_negligible.add actualPrimaryProgramError_negligible).add
    actualInverseEntryError_negligible).add actualPrimaryReciprocalProgramError_negligible).mul_polynomial 280).const_mul (4*64^4) using 1
  funext n
  unfold actualDensityInverseProgramError
  ring

/-- The computed entry includes the two primary reference weights and the
activation inverse, exactly as used when acting on a joint density kernel. -/
theorem actual_density_inverse_program_eventually (constant : ℕ) (hc : 1 ≤ constant) (beta : ℕ → ℚ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ (beta n : ℝ) ∧
      (beta n : ℝ) ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
      ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap=actualResponse (constant : ℝ) n →
      ∀ input output,
      |(actualDensityInverseProgram constant n (beta n) input.val output.val : ℝ)-
        (v7Activation constant n)⁻¹*(actualPrimaryLaw constant n (beta n)).weight input*
          operator.symm (Pi.single input 1) output/((actualPrimaryLaw constant n (beta n)).weight output)| ≤
        actualDensityInverseProgramError n := by
  filter_upwards [actual_activation_inverse_program_eventually constant hc,
    actual_primary_program_eventually constant hc,actual_inverse_entry_program_eventually constant hc,
    actual_primary_reciprocal_program_eventually constant hc beta hbeta,
    actual_inverse_entry_bound_eventually constant hc,
    actual_primary_law_quarter_lower_eventually (constant : ℝ) (by exact_mod_cast hc) (fun n => beta n) hbeta,
    actual_reference_laws_eventually (constant : ℝ) (by exact_mod_cast hc) (fun n => beta n) hbeta,
    v7Activation_lower_eventually (constant : ℝ) (by exact_mod_cast hc),
    actualActivationInverseError_negligible 0,actualInverseEntryError_negligible 0,
    hbeta,eventually_ge_atTop 2] with n ha hp hi hrec hbound hlower hl hrho haSmall hiSmall hb hn operator hop input output
  obtain ⟨inverse,hinverse,hie⟩ := hi
  have heq : operator=inverse := by
    ext profile color
    change operator.toLinearMap profile color=inverse.toLinearMap profile color
    rw [hop,hinverse]
  have hie' : |(actualInverseIterationProgram constant n input.val n output.val : ℝ)-operator.symm (Pi.single input 1) output| ≤ actualInverseEntryError n := by
    rw [heq]
    exact hie input output
  let a : ℝ := (v7Activation constant n)⁻¹
  let aa : ℝ := actualActivationInverseApprox constant n n
  let p : ℝ := (actualPrimaryLaw constant n (beta n)).weight input
  let pa : ℝ := probabilityClamp (actualPrimaryProgram constant n (beta n) input.val)
  let v : ℝ := operator.symm (Pi.single input 1) output
  let va : ℝ := actualInverseIterationProgram constant n input.val n output.val
  let r : ℝ := ((actualPrimaryLaw constant n (beta n)).weight output)⁻¹
  let ra : ℝ := actualPrimaryReciprocalProgram constant n (beta n) output.val
  let B : ℝ := 64*(n : ℝ)^70
  let error : ℝ := actualActivationInverseError n+actualPrimaryProgramError n+actualInverseEntryError n+actualPrimaryReciprocalProgramError n
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hqpos : (0 : ℝ) < Parameters.modulus n := by exact_mod_cast (Parameters.modulus_prime n).pos
  have hpow : 1 ≤ (n : ℝ)^70 := one_le_pow₀ hn1
  have hb0 : 1 ≤ B := by dsimp [B];linarith
  have hp0 : 0 ≤ p := (actualPrimaryLaw constant n (beta n)).nonneg input
  have hp1 : p ≤ 1 := by
    simpa only [(actualPrimaryLaw constant n (beta n)).sum_one] using Finset.single_le_sum
      (fun color (_ : color∈Finset.univ) => (actualPrimaryLaw constant n (beta n)).nonneg color) (Finset.mem_univ input)
  have hpa := probabilityClamp_bounds (actualPrimaryProgram constant n (beta n) input.val)
  have hpe : |pa-p| ≤ actualPrimaryProgramError n := by
    apply (probabilityClamp_error _ _ hp0 hp1).trans
    simpa only [p,hl.1] using hp (beta n) hb.1 input
  have hρ0 : 0 < v7Activation constant n := lt_of_lt_of_le (by positivity) hrho
  have ha0 : 0 ≤ a := (inv_pos.mpr hρ0).le
  have ha1 : a ≤ (n : ℝ)^5 := by
    have hh := one_div_le_one_div_of_le (by positivity : 0 < ((n : ℝ)^5)⁻¹) hrho
    simpa only [one_div,inv_inv] using hh
  have haB : |a| ≤ B := by
    rw [abs_of_nonneg ha0]
    exact ha1.trans ((pow_le_pow_right₀ hn1 (by decide : 5 ≤ 70)).trans (by dsimp [B];nlinarith))
  have haE0 : 0 ≤ actualActivationInverseError n := (abs_nonneg _).trans ha
  have hpE0 : 0 ≤ actualPrimaryProgramError n := (abs_nonneg _).trans hpe
  have hiE0 : 0 ≤ actualInverseEntryError n := (abs_nonneg _).trans hie'
  have hrE0 : 0 ≤ actualPrimaryReciprocalProgramError n := (abs_nonneg _).trans (hrec output).2.2
  have hsmallA : actualActivationInverseError n ≤ 1 := by simpa only [pow_zero,div_one] using (le_abs_self _).trans haSmall
  have hsmallI : actualInverseEntryError n ≤ 1 := by simpa only [pow_zero,div_one] using (le_abs_self _).trans hiSmall
  have haaB : |aa| ≤ B := by
    have hh := abs_add_le (aa-a) a
    rw [sub_add_cancel] at hh
    have h5 := pow_le_pow_right₀ hn1 (by decide : 5 ≤ 70)
    rw [abs_of_nonneg ha0] at hh
    dsimp only [aa,a] at hh
    dsimp only [B]
    nlinarith only [hh,ha,ha1,hsmallA,h5,hpow]
  have hvB : |v| ≤ B := (hbound operator hop input output).trans (by dsimp [B];nlinarith)
  have hvaB : |va| ≤ B := by
    have hh := abs_add_le (va-v) v
    rw [sub_add_cancel] at hh
    have hv := hbound operator hop input output
    dsimp only [va,v] at hh
    dsimp only [B]
    nlinarith only [hh,hv,hie',hsmallI,hpow]
  have hrpos : 0 < (actualPrimaryLaw constant n (beta n)).weight output :=
    lt_of_lt_of_le (by positivity) (hlower output)
  have hr1 : r ≤ 4*(Parameters.modulus n : ℝ) := by
    have hh := one_div_le_one_div_of_le (by positivity : 0 < 1/(4*(Parameters.modulus n : ℝ))) (hlower output)
    simpa only [one_div,inv_inv] using hh
  have hqbound : (Parameters.modulus n : ℝ) ≤ 2*(n : ℝ)^40 := by
    have hh := (Parameters.modulus_bounds n).2
    rw [Parameters.security_eq n hn] at hh
    exact_mod_cast hh
  have h40 := pow_le_pow_right₀ hn1 (by decide : 40 ≤ 70)
  have hrB : |r| ≤ B := by rw [abs_of_pos (inv_pos.mpr hrpos)];dsimp [B];nlinarith only [hr1,hqbound,h40,hpow]
  have hraB : |ra| ≤ B := by rw [abs_of_pos (hrec output).1];have hh := (hrec output).2.1;dsimp [B];nlinarith only [hh,h40,hpow]
  let first : Fin 4 → ℝ := ![aa,pa,va,ra]
  let second : Fin 4 → ℝ := ![a,p,v,r]
  have hf : ∀ i∈(Finset.univ : Finset (Fin 4)),|first i| ≤ B := by
    intro i _
    fin_cases i
    · exact haaB
    · change |pa| ≤ B
      rw [abs_of_nonneg hpa.1]
      exact hpa.2.trans hb0
    · exact hvaB
    · exact hraB
  have hg : ∀ i∈(Finset.univ : Finset (Fin 4)),|second i| ≤ B := by
    intro i _
    fin_cases i
    · exact haB
    · change |p| ≤ B
      rw [abs_of_nonneg hp0]
      exact hp1.trans hb0
    · exact hvB
    · exact hrB
  have hd : ∀ i∈(Finset.univ : Finset (Fin 4)),|first i-second i| ≤ error := by
    intro i _
    fin_cases i
    · exact ha.trans (by dsimp [error];linarith)
    · exact hpe.trans (by dsimp [error];linarith)
    · exact hie'.trans (by dsimp [error];linarith)
    · exact (hrec output).2.2.trans (by dsimp [error];linarith)
  have hh := abs_prod_sub_prod_le Finset.univ first second B error hb0 (by dsimp [error];positivity) hf hg hd
  simp only [Fin.prod_univ_four,first,second,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Finset.card_univ,Fintype.card_fin] at hh
  simp only [actualDensityInverseProgram,Rat.cast_mul,div_eq_mul_inv]
  change |aa*pa*va*ra-a*p*v*r| ≤ _
  apply hh.trans_eq
  unfold actualDensityInverseProgramError B error
  ring

end
end AFT.V7Calibration
