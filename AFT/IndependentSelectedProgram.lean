import AFT.IndependentPairedDensityProgram
import AFT.IndependentJointCanonical
import AFT.SelectedCoefficientBound

/-! # Actual selected independent-response columns without scalar oracles -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators

def independentSelectedProgram (constant n : ℕ) (beta : ℚ) {colors : ℕ} (point : ℕ)
    (selected : Finset (Fin 4)) (output : selected → Fin colors) : ℚ :=
  rationalSelectedCoefficient constant n beta
    (fun word : Fin 4 → Fin colors => independentPairedDensityProgram constant n beta point (fun slot => (word slot).val))
    selected output

noncomputable section
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
local instance independentSelectedProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance independentSelectedProgramSubtypeDecEq (selected : Finset (Fin 4)) : DecidableEq selected := Classical.decEq _

theorem independentPairedDensityColumn_bound_eventually (constant : ℕ) (hc : 1 ≤ constant) (beta : ℕ → ℚ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ (beta n : ℝ) ∧
      (beta n : ℝ) ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily constant n mark,
    (∀ mark attached first second,publicChartRaw constant n mark (charts mark) attached first second=
      conditionalJointOutput constant n mark attached first second) →
    ∀ (point : Fin (Parameters.modulus n)) (word : Fin 4 → Fin (Parameters.modulus n)),
      |independentPairedNumerator constant n (beta n) charts
        (fun color => (actualPrimaryLaw constant n (beta n)).weight color*
          (Pi.single point (1 : ℝ) : Fin (Parameters.modulus n) → ℝ) color) word| ≤ 773 := by
  filter_upwards [fixed_paired_density_program_bounds_eventually constant hc beta hbeta,
    actual_primary_law_quarter_lower_eventually (constant : ℝ) (by exact_mod_cast hc) (fun n => beta n) hbeta]
    with n hb hp
  intro charts hcharts point word
  have hp0 (color) : (actualPrimaryLaw constant n (beta n)).weight color ≠ 0 := by
    have hq : (0 : ℝ) < Parameters.modulus n := by exact_mod_cast (Parameters.modulus_prime n).pos
    exact (lt_of_lt_of_le (by positivity : (0 : ℝ) < 1/(4*Parameters.modulus n)) (hp color)).ne'
  have hb' (roots : Window (v7RootCutoff n) × Window (v7RootCutoff n)) :
      |fixedPairedChartRaw constant n (beta n) charts roots.1 roots.2 0
        (fun color => (actualPrimaryLaw constant n (beta n)).weight color*
          (Pi.single point (1 : ℝ) : Fin (Parameters.modulus n) → ℝ) color) word| ≤ 773 := by
    have hh := (hb charts hcharts roots.1 roots.2 0
      (abs_le.mpr (Finset.mem_Icc.mp roots.1.property)) (by simp) point word).1
    rw [fixedPairedDensityColumn_exact _ _ _ _ _ _ _ _ _ hp0] at hh
    exact hh
  exact FiniteDist.abs_average_le_bound (pairedRootReference n)
    (fun roots => fixedPairedChartRaw constant n (beta n) charts roots.1 roots.2 0
      (fun color => (actualPrimaryLaw constant n (beta n)).weight color*
        (Pi.single point (1 : ℝ) : Fin (Parameters.modulus n) → ℝ) color) word) 773 hb'

/-- The local coefficient array has a fixed polynomial magnitude even
before the new-coordinate inverse is applied. -/
theorem independentReferenceChannel_bound_eventually (constant : ℕ) (hc : 1 ≤ constant) (beta : ℕ → ℚ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ (beta n : ℝ) ∧
      (beta n : ℝ) ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily constant n mark,
    (∀ mark attached first second,publicChartRaw constant n mark (charts mark) attached first second=
      conditionalJointOutput constant n mark attached first second) →
    ∀ (point : Fin (Parameters.modulus n)) (selected : Finset (Fin 4)) (output : selected → Fin (Parameters.modulus n)),
      |independentReferenceChannel constant n (beta n) charts selected (Pi.single point 1) output| ≤
        (773*1048576 : ℝ)*(n : ℝ)^320 := by
  filter_upwards [independentPairedDensityColumn_bound_eventually constant hc beta hbeta,
    actual_reference_atom_program_eventually constant hc beta hbeta,eventually_ge_atTop 2]
    with n hm ha hn charts hcharts point selected output
  rw [independentReferenceChannel_apply]
  have hh := LocalTensors.referenceRestrictedComponent_abs_le
    (fun _ : Fin 4 => actualPrimaryLaw constant n (beta n))
    (fun _ : Fin 4 => actualReferenceLaw constant n (beta n))
    (independentPairedNumerator constant n (beta n) charts
      (fun color => (actualPrimaryLaw constant n (beta n)).weight color*
        (Pi.single point (1 : ℝ) : Fin (Parameters.modulus n) → ℝ) color)) selected output
    773 (16*(n : ℝ)^40) (by norm_num) (by positivity) (hm charts hcharts point)
    (fun slot input => (ha input (output slot)).1)
  apply hh.trans
  simp only [Fintype.card_fin]
  have hcard : selected.card ≤ 4 := (Finset.card_le_univ selected).trans_eq (Fintype.card_fin 4)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hbase : 1 ≤ 16*(n : ℝ)^40 := by have hp := one_le_pow₀ hn1 (n:=40);linarith
  have hq : (Parameters.modulus n : ℝ) ≤ 2*(n : ℝ)^40 := by
    have h := (Parameters.modulus_bounds n).2
    rw [Parameters.security_eq n hn] at h
    exact_mod_cast h
  calc
    _ ≤ (2*(n : ℝ)^40)^4*773*(16*(n : ℝ)^40)^4 := by
      gcongr
      exact hbase
    _ = _ := by ring

def independentSelectedProgramError (n : ℕ) : ℝ :=
  (1048576 : ℝ)*(n : ℝ)^320*
    (independentPairedDensityProgramError n+3092*actualPrimaryReciprocalProgramError n)

theorem independentSelectedProgramError_negligible : Negligible independentSelectedProgramError := by
  convert ((independentPairedDensityProgramError_negligible.add
    (actualPrimaryReciprocalProgramError_negligible.const_mul 3092)).mul_polynomial 320).const_mul 1048576 using 1
  funext n;unfold independentSelectedProgramError;ring

/-- All fifteen nonempty selected coefficients, and the empty coefficient,
use the actual centered reference and actual inverse-primary atom. -/
theorem independent_selected_program_eventually (constant : ℕ) (hc : 1 ≤ constant) (beta : ℕ → ℚ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ (beta n : ℝ) ∧
      (beta n : ℝ) ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily constant n mark,
    (∀ mark attached first second,publicChartRaw constant n mark (charts mark) attached first second=
      conditionalJointOutput constant n mark attached first second) →
    ∀ (point : Fin (Parameters.modulus n)) (selected : Finset (Fin 4)) (output : selected → Fin (Parameters.modulus n)),
      |(independentSelectedProgram constant n (beta n) point.val selected output : ℝ)-
        independentReferenceChannel constant n (beta n) charts selected (Pi.single point 1) output| ≤
          independentSelectedProgramError n := by
  filter_upwards [independent_paired_density_program_eventually constant hc beta hbeta,
    independentPairedDensityColumn_bound_eventually constant hc beta hbeta,
    actual_selected_coefficient_program_eventually constant hc beta hbeta,
    actual_primary_reciprocal_program_eventually constant hc beta hbeta,eventually_ge_atTop 2]
    with n hd hb hs hi hn
  intro charts hcharts point selected output
  have he0 : 0 ≤ independentPairedDensityProgramError n := (abs_nonneg _).trans
    (hd charts hcharts point (fun _ => point))
  have he1 : 0 ≤ actualPrimaryReciprocalProgramError n := (abs_nonneg _).trans (hi point).2.2
  have hh := hs 4
    (independentPairedNumerator constant n (beta n) charts
      (fun color => (actualPrimaryLaw constant n (beta n)).weight color*
        (Pi.single point (1 : ℝ) : Fin (Parameters.modulus n) → ℝ) color))
    (fun word => independentPairedDensityProgram constant n (beta n) point.val (fun slot => (word slot).val))
    773 (independentPairedDensityProgramError n) (by norm_num) he0
    (hb charts hcharts point) (hd charts hcharts point) selected output
  rw [show instDecidableEqFin 4=independentJointCanonicalFinDecEq 4 from Subsingleton.elim _ _] at hh
  rw [independentReferenceChannel_apply]
  apply hh.trans
  have hcard : selected.card ≤ 4 := (Finset.card_le_univ selected).trans_eq (Fintype.card_fin 4)
  have hcard' : (selected.card : ℝ) ≤ 4 := by exact_mod_cast hcard
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hbase : 1 ≤ 16*(n : ℝ)^40 := by have hp := one_le_pow₀ hn1 (n := 40);linarith
  have hq : (Parameters.modulus n : ℝ) ≤ 2*(n : ℝ)^40 := by
    have h := (Parameters.modulus_bounds n).2
    rw [Parameters.security_eq n hn] at h
    exact_mod_cast h
  have hpower := pow_le_pow_right₀ hbase hcard
  calc
    _ ≤ (2*(n : ℝ)^40)^4*(independentPairedDensityProgramError n+773*4*actualPrimaryReciprocalProgramError n)*
        (16*(n : ℝ)^40)^4 := by gcongr
    _ = independentSelectedProgramError n := by unfold independentSelectedProgramError;ring

end
end AFT.V7Calibration
