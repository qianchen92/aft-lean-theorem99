import AFT.IndependentSelectedProgram
import AFT.IndependentInverseColumns
import AFT.SelectedInverseProgram

/-! # The actual nonlinear independent-response inverse is numerically evaluable -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators

def independentInverseProgram (constant n : ℕ) (beta : ℚ) {colors : ℕ} (point : ℕ)
    (selected : Finset (Fin 4)) (output : selected → Fin colors) : ℚ :=
  selectedInverseProgram constant n beta selected
    (independentSelectedProgram constant n beta point selected) output

noncomputable section
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
local instance independentInverseProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance independentInverseProgramSubtypeDecEq (selected : Finset (Fin 4)) : DecidableEq selected := Classical.decEq _

def independentInverseProgramError (n : ℕ) : ℝ :=
  (16*257^4 : ℝ)*(n : ℝ)^640*
    (independentSelectedProgramError n+(4*773*1048576 : ℝ)*(n : ℝ)^320*actualDensityInverseProgramError n)

theorem independentInverseProgramError_negligible : Negligible independentInverseProgramError := by
  convert ((independentSelectedProgramError_negligible.add
    ((actualDensityInverseProgramError_negligible.mul_polynomial 320).const_mul (4*773*1048576))).mul_polynomial 640).const_mul
      (16*257^4) using 1
  funext n;unfold independentInverseProgramError;ring

/-- No magnitude, inverse, source-law or local-kernel approximation oracle
is an assumption of this actual-model column estimate. -/
theorem independent_inverse_program_eventually (constant : ℕ) (hc : 1 ≤ constant) (beta : ℕ → ℚ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ (beta n : ℝ) ∧
      (beta n : ℝ) ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse constant n →
    ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily constant n mark,
    (∀ mark attached first second,publicChartRaw constant n mark (charts mark) attached first second=
      conditionalJointOutput constant n mark attached first second) →
    ∀ (point : Fin (Parameters.modulus n)) (selected : Finset (Fin 4)) (output : selected → Fin (Parameters.modulus n)),
      |(independentInverseProgram constant n (beta n) point.val selected output : ℝ)-
        independentInverseColumn constant n (beta n) operator charts selected point output| ≤
          independentInverseProgramError n := by
  filter_upwards [independent_selected_program_eventually constant hc beta hbeta,
    independentReferenceChannel_bound_eventually constant hc beta hbeta,
    selected_inverse_program_eventually constant hc beta hbeta,
    actual_density_inverse_estimates_eventually constant hc beta hbeta,eventually_ge_atTop 2]
    with n hs hb hi hm hn operator hop charts hcharts point selected output
  have he0 : 0 ≤ independentSelectedProgramError n := (abs_nonneg _).trans
    (hs charts hcharts point selected output)
  have he1 : 0 ≤ actualDensityInverseProgramError n := (abs_nonneg _).trans (hm operator hop point point).2.2
  have hh := hi operator hop 4 selected
    (independentReferenceChannel constant n (beta n) charts selected (Pi.single point 1))
    (independentSelectedProgram constant n (beta n) point.val selected)
    ((773*1048576 : ℝ)*(n : ℝ)^320) (independentSelectedProgramError n)
    (by positivity) he0 (hb charts hcharts point selected) (hs charts hcharts point selected) output
  rw [show @Subtype.instDecidableEq (Fin 4) (fun slot => slot∈selected) (instDecidableEqFin 4)=
    independentInverseColumnsSubtypeDecEq selected from Subsingleton.elim _ _] at hh
  change |_ - independentInverseColumn constant n (beta n) operator charts selected point output| ≤ _ at hh
  apply hh.trans
  have hcard : selected.card ≤ 4 := (Finset.card_le_univ selected).trans_eq (Fintype.card_fin 4)
  have hcard' : (selected.card : ℝ) ≤ 4 := by exact_mod_cast hcard
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hbase : 1 ≤ 257*(n : ℝ)^120 := by have hp := one_le_pow₀ hn1 (n:=120);linarith
  have hq1 : (1 : ℝ) ≤ Parameters.modulus n := by exact_mod_cast (Parameters.modulus_prime n).one_lt.le
  have hq : (Parameters.modulus n : ℝ) ≤ 2*(n : ℝ)^40 := by
    have h := (Parameters.modulus_bounds n).2
    rw [Parameters.security_eq n hn] at h
    exact_mod_cast h
  calc
    _ ≤ (2*(n : ℝ)^40)^4*
        (independentSelectedProgramError n+((773*1048576 : ℝ)*(n : ℝ)^320)*4*actualDensityInverseProgramError n)*
        (257*(n : ℝ)^120)^4 := by
      gcongr
      · exact (pow_le_pow_right₀ hq1 hcard).trans (pow_le_pow_left₀ (by positivity) hq _)
      · exact hbase
    _ = independentInverseProgramError n := by unfold independentInverseProgramError;ring

end
end AFT.V7Calibration
