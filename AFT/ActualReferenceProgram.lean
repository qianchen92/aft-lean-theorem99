import AFT.ActualPrimaryProgram
import AFT.V7ReferenceLaws

/-! # Exact rational evaluation of the actual reference profile

The activation cancels in the calibrated reference.  This program therefore
uses rational beta and integer population parameters only.
-/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators

def actualReferenceProgram (constant n : ℕ) (beta : ℚ) (color : ℤ) : ℚ :=
  1/(ParameterProgram.modulus n).value+
    (actualLegPopulationProgram n : ℚ)/actualDimensionProgram n*
      actualBoundaryCoefficientProgram constant n beta color

noncomputable section
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
local instance referenceProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

theorem actualReferenceMean_rational_formula (constant : ℝ) (n : ℕ) (beta : ℝ)
    (hrho : v7Activation constant n≠0) (color : Fin (Parameters.modulus n)) :
    actualReferenceMean constant n beta color=1/(Parameters.modulus n : ℝ)+
      (Parameters.legs n : ℝ)/Parameters.dimension n*actualBoundaryCoefficient constant n beta color := by
  unfold actualReferenceMean referenceMean calibratedReferenceMean actualBoundaryCoefficient
    repairedBoundaryMass v7BaseBoundaryMass
  simp only [Pi.add_apply,Pi.smul_apply,Pi.sub_apply,smul_eq_mul]
  simp only [div_eq_mul_inv,mul_inv_rev]
  field_simp [hrho]

theorem actual_reference_mean_program_eventually (constant : ℕ) (hc : 1≤constant) :
    ∀ᶠ n : ℕ in atTop,∀ (beta : ℚ) (color : Fin (Parameters.modulus n)),
      (actualReferenceProgram constant n beta color.val : ℝ)=actualReferenceMean constant n beta color := by
  filter_upwards [actual_boundary_coefficient_program_eventually constant hc,
    v7Activation_lower_eventually (constant : ℝ) (by exact_mod_cast hc),eventually_ge_atTop 2]
    with n hcoeff hrho hn beta color
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have ha : v7Activation constant n≠0 := ne_of_gt (lt_of_lt_of_le (by positivity) hrho)
  rw [actualReferenceMean_rational_formula _ _ _ ha]
  simp only [actualReferenceProgram,Rat.cast_add,Rat.cast_div,Rat.cast_one,Rat.cast_natCast,
    Rat.cast_mul,ParameterProgram.modulus_value,actualLegPopulationProgram_eq,actualDimensionProgram_eq,hcoeff]

theorem actual_reference_program_eventually (constant : ℕ) (hc : 1≤constant) (beta : ℕ → ℚ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n)≤(beta n : ℝ) ∧
      (beta n : ℝ)≤2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ color : Fin (Parameters.modulus n),
      (actualReferenceProgram constant n (beta n) color.val : ℝ)=
        (actualReferenceLaw constant n (beta n)).weight color := by
  filter_upwards [actual_reference_mean_program_eventually constant hc,
    actual_reference_laws_eventually (constant : ℝ) (by exact_mod_cast hc) (fun n => beta n) hbeta]
    with n hprog hlaw color
  rw [hlaw.2.2]
  exact hprog _ _

end
end AFT.V7Calibration
