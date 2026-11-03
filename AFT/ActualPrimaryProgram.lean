import AFT.ActualBasePrimaryProgram
import AFT.ActualBetaStandaloneProgram

/-! # Executable beta repair of the actual primary probability profile -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators

def actualBoundaryCountProgram (constant n : ℕ) : ℕ :=
  2*(actualBoundaryHalfProgram constant n).toNat

def actualInteriorCountProgram (constant n : ℕ) : ℕ :=
  (ParameterProgram.modulus n).value-actualBoundaryCountProgram constant n

def actualBoundaryUniformProgram (constant n : ℕ) (color : ℤ) : ℚ :=
  if color<actualBoundaryHalfProgram constant n ∨
      ((ParameterProgram.modulus n).value : ℤ)-1-actualBoundaryHalfProgram constant n<color
  then (actualBoundaryCountProgram constant n : ℚ)⁻¹ else 0

def actualInteriorUniformProgram (constant n : ℕ) (color : ℤ) : ℚ :=
  if color<actualBoundaryHalfProgram constant n ∨
      ((ParameterProgram.modulus n).value : ℤ)-1-actualBoundaryHalfProgram constant n<color
  then 0 else (actualInteriorCountProgram constant n : ℚ)⁻¹

def actualBoundaryCoefficientProgram (constant n : ℕ) (beta : ℚ) (color : ℤ) : ℚ :=
  ((actualBoundaryCountProgram constant n : ℚ)/(ParameterProgram.modulus n).value)*
    (beta⁻¹-(actualDimensionProgram n : ℚ)/actualLegPopulationProgram n)*
    (actualBoundaryUniformProgram constant n color-actualInteriorUniformProgram constant n color)

def actualPrimaryProgram (constant n : ℕ) (beta : ℚ) (color : ℤ) : ℚ :=
  actualBasePrimaryProgram constant n color+
    actualActivationInverseApprox constant n n*actualBoundaryCoefficientProgram constant n beta color

def actualPrimaryFromBits (constant n : ℕ) (word : Fin (n+n) → Fin 2) (color : ℤ) : ℚ :=
  actualPrimaryProgram constant n (ParameterProgram.beta n word).value color

noncomputable section
open scoped Topology
set_option backward.isDefEq.respectTransparency false

theorem actual_boundary_counts_program_eventually (constant : ℕ) (hc : 1≤constant) :
    ∀ᶠ n : ℕ in atTop,
      actualBoundaryCountProgram constant n=
        (boundaryPalette (Parameters.modulus n) (boundaryHalf (constant : ℝ) n)).card ∧
      actualInteriorCountProgram constant n=
        (boundaryPalette (Parameters.modulus n) (boundaryHalf (constant : ℝ) n))ᶜ.card := by
  filter_upwards [body_support_scales_eventually (constant : ℝ) (by exact_mod_cast hc)] with n hh
  have hs := Parameters.safeSize_positive n
  unfold Parameters.safeSize at hs
  have hc' := boundaryPalette_card (Parameters.modulus n) (boundaryHalf (constant : ℝ) n)
    hh.2.2.1 (by have := hh.2.2.2;omega)
  have hb : actualBoundaryCountProgram constant n=
      (boundaryPalette (Parameters.modulus n) (boundaryHalf (constant : ℝ) n)).card := by
    unfold actualBoundaryCountProgram
    rw [actualBoundaryHalfProgram_eq]
    omega
  refine ⟨hb,?_⟩
  simp only [actualInteriorCountProgram,ParameterProgram.modulus_value,hb,Finset.card_compl,Fintype.card_fin]

theorem actual_boundary_uniform_program_eventually (constant : ℕ) (hc : 1≤constant) :
    ∀ᶠ n : ℕ in atTop,∀ color : Fin (Parameters.modulus n),
      (actualBoundaryUniformProgram constant n color.val : ℝ)=
        uniformFiniteProfile (boundaryPalette (Parameters.modulus n) (boundaryHalf (constant : ℝ) n)) color ∧
      (actualInteriorUniformProgram constant n color.val : ℝ)=
        uniformFiniteProfile (boundaryPalette (Parameters.modulus n) (boundaryHalf (constant : ℝ) n))ᶜ color := by
  filter_upwards [actual_boundary_counts_program_eventually constant hc] with n hh color
  have hm := mem_boundaryPalette (Parameters.modulus n) (boundaryHalf (constant : ℝ) n) color
  simp only [actualBoundaryUniformProgram,actualInteriorUniformProgram,actualBoundaryHalfProgram_eq,
    ParameterProgram.modulus_value,uniformFiniteProfile,Finset.mem_compl,hm,hh.1,hh.2]
  split_ifs <;> simp only [Rat.cast_inv,Rat.cast_natCast,Rat.cast_zero,and_self]

def actualBoundaryCoefficient (constant : ℝ) (n : ℕ) (beta : ℝ)
    (color : Fin (Parameters.modulus n)) : ℝ :=
  ((boundaryPalette (Parameters.modulus n) (boundaryHalf constant n)).card/(Parameters.modulus n : ℝ))*
    (beta⁻¹-(Parameters.dimension n : ℝ)/Parameters.legs n)*
    (uniformFiniteProfile (boundaryPalette (Parameters.modulus n) (boundaryHalf constant n)) color-
      uniformFiniteProfile (boundaryPalette (Parameters.modulus n) (boundaryHalf constant n))ᶜ color)

theorem actual_boundary_coefficient_program_eventually (constant : ℕ) (hc : 1≤constant) :
    ∀ᶠ n : ℕ in atTop,∀ (beta : ℚ) (color : Fin (Parameters.modulus n)),
      (actualBoundaryCoefficientProgram constant n beta color.val : ℝ)=
        actualBoundaryCoefficient (constant : ℝ) n beta color := by
  filter_upwards [actual_boundary_counts_program_eventually constant hc,
    actual_boundary_uniform_program_eventually constant hc] with n hh hu beta color
  simp only [actualBoundaryCoefficientProgram,Rat.cast_mul,Rat.cast_div,Rat.cast_sub,Rat.cast_inv,
    Rat.cast_natCast,actualBoundaryCoefficient,hh.1,ParameterProgram.modulus_value,actualDimensionProgram_eq,
    actualLegPopulationProgram_eq,(hu color).1,(hu color).2]

theorem actualPrimary_base_repair (constant : ℝ) (n : ℕ) (beta : ℝ)
    (color : Fin (Parameters.modulus n)) :
    actualPrimary constant n beta color=
      basePrimary n constant (boundaryHalf constant n) (bodyShift constant n) (bodyBlur constant n)
        (startsPlus constant n) (startsMinus constant n) (pairSourceShift constant n) (pairSourceLaw constant n) color+
      (v7Activation constant n)⁻¹*actualBoundaryCoefficient constant n beta color := by
  unfold actualPrimary primary calibratedPrimaryProfile actualBoundaryCoefficient repairedBoundaryMass v7BaseBoundaryMass
  simp only [Pi.add_apply,Pi.smul_apply,Pi.sub_apply,smul_eq_mul]
  ring

theorem uniformFiniteProfile_abs_le_one {Color : Type*} [Fintype Color] [DecidableEq Color]
    (support : Finset Color) (color : Color) : |uniformFiniteProfile support color|≤1 := by
  unfold uniformFiniteProfile
  split_ifs with hm
  · rw [abs_of_nonneg (by positivity)]
    apply inv_le_one_of_one_le₀
    exact_mod_cast (Finset.one_le_card.mpr ⟨color,hm⟩)
  · norm_num

theorem actualBoundaryCoefficient_bound (constant : ℝ) (n : ℕ) (beta : ℝ) (hn : 2≤n)
    (hb : (Parameters.legs n : ℝ)/(2*Parameters.dimension n)≤beta)
    (color : Fin (Parameters.modulus n)) :
    |actualBoundaryCoefficient constant n beta color|≤12*(n : ℝ)^60 := by
  have hm : (0 : ℝ)<Parameters.legs n := by unfold Parameters.legs; have := Parameters.security_ge_two n; positivity
  have hN : (0 : ℝ)<Parameters.dimension n := by
    unfold Parameters.dimension Parameters.meanDensity
    have := (Parameters.modulus_prime n).pos
    have := Parameters.security_ge_two n
    positivity
  have hq : (0 : ℝ)<Parameters.modulus n := by exact_mod_cast (Parameters.modulus_prime n).pos
  have hb0 : 0<beta := lt_of_lt_of_le (by positivity : (0 : ℝ)<Parameters.legs n/(2*Parameters.dimension n)) hb
  have hib : beta⁻¹≤2*(Parameters.dimension n : ℝ)/Parameters.legs n := by
    have hh := one_div_le_one_div_of_le (by positivity : (0 : ℝ)<Parameters.legs n/(2*Parameters.dimension n)) hb
    simpa only [one_div,inv_div] using hh
  have hm1 : (1 : ℝ)≤Parameters.legs n := by exact_mod_cast (show 1≤Parameters.legs n by exact_mod_cast hm)
  have hdim : (Parameters.dimension n : ℝ)/Parameters.legs n≤2*(n : ℝ)^60 := by
    have hh := (Parameters.dimension_bounds n).2
    rw [Parameters.security_eq n hn] at hh
    exact (div_le_self hN.le hm1).trans (by exact_mod_cast hh)
  let support := boundaryPalette (Parameters.modulus n) (boundaryHalf constant n)
  have hfrac : (support.card : ℝ)/Parameters.modulus n≤1 := by
    apply (div_le_one hq).mpr
    exact_mod_cast (show support.card≤Parameters.modulus n by
      simpa only [Fintype.card_fin] using Finset.card_le_univ support)
  have hfrac0 : 0≤(support.card : ℝ)/Parameters.modulus n := by positivity
  have hp := uniformFiniteProfile_abs_le_one support color
  have hi := uniformFiniteProfile_abs_le_one supportᶜ color
  have hdiff : |uniformFiniteProfile support color-uniformFiniteProfile supportᶜ color|≤2 :=
    (abs_sub _ _).trans (by linarith)
  have hbeta : |beta⁻¹-(Parameters.dimension n : ℝ)/Parameters.legs n|≤6*(n : ℝ)^60 := by
    apply (abs_sub _ _).trans
    rw [abs_of_pos (inv_pos.mpr hb0),abs_of_nonneg (by positivity)]
    have heq : 2*(Parameters.dimension n : ℝ)/Parameters.legs n=2*((Parameters.dimension n : ℝ)/Parameters.legs n) := by ring
    rw [heq] at hib
    linarith
  unfold actualBoundaryCoefficient
  change |((support.card : ℝ)/Parameters.modulus n)*(beta⁻¹-(Parameters.dimension n : ℝ)/Parameters.legs n)*
    (uniformFiniteProfile support color-uniformFiniteProfile supportᶜ color)|≤_
  rw [abs_mul,abs_mul,abs_of_nonneg hfrac0]
  calc
    _ ≤ 1*(6*(n : ℝ)^60)*2 := by gcongr
    _ = _ := by ring

def actualPrimaryProgramError (n : ℕ) : ℝ :=
  actualBasePrimaryProgramError n+12*(n : ℝ)^60*actualActivationInverseError n

theorem actualPrimaryProgramError_negligible : Negligible actualPrimaryProgramError := by
  convert actualBasePrimaryProgramError_negligible.add
    ((actualActivationInverseError_negligible.mul_polynomial 60).const_mul 12) using 1
  funext n
  unfold actualPrimaryProgramError
  ring

/-- The exact finite beta value remains rational. Uniformity over its full
legal interval avoids a hidden pointwise-in-beta threshold. -/
theorem actual_primary_program_eventually (constant : ℕ) (hc : 1≤constant) :
    ∀ᶠ n : ℕ in atTop,∀ (beta : ℚ),
      (Parameters.legs n : ℝ)/(2*Parameters.dimension n)≤(beta : ℝ) →
      ∀ color : Fin (Parameters.modulus n),
        |(actualPrimaryProgram constant n beta color.val : ℝ)-actualPrimary (constant : ℝ) n beta color|≤
          actualPrimaryProgramError n := by
  filter_upwards [actual_base_primary_program_eventually constant hc,
    actual_boundary_coefficient_program_eventually constant hc,
    actual_activation_inverse_program_eventually constant hc,eventually_ge_atTop 2]
    with n hbase hcoeff hinv hn beta hbeta color
  rw [actualPrimary_base_repair]
  simp only [actualPrimaryProgram,Rat.cast_add,Rat.cast_mul,hcoeff]
  rw [show ∀ a b c d e : ℝ,(a+b*c)-(d+e*c)=(a-d)+(b-e)*c by intros;ring]
  apply (abs_add_le _ _).trans
  rw [abs_mul]
  apply (add_le_add (hbase color) (mul_le_mul hinv
    (actualBoundaryCoefficient_bound (constant : ℝ) n beta hn hbeta color)
    (abs_nonneg _) (by unfold actualActivationInverseError;positivity))).trans_eq
  unfold actualPrimaryProgramError
  ring

theorem actual_beta_program_typical (n : ℕ) (word : Fin (n+n) → Fin 2) :
    (Parameters.legs n : ℝ)/(2*Parameters.dimension n)≤((ParameterProgram.beta n word).value : ℝ) ∧
      ((ParameterProgram.beta n word).value : ℝ)≤2*(Parameters.legs n : ℝ)/Parameters.dimension n := by
  have hN : 0<Parameters.dimension n := by
    have hp := Parameters.population_identity n
    have hb := Parameters.bodies_positive n
    omega
  rw [ParameterProgram.beta_value,BetaReference.CountedFraction.beta_value _ _ _ _ hN]
  exact BetaReference.safeGridValue_real_typical _ _ _ _

/-- From the security parameter, the integer constant and the actual beta
fair-bit tape, every primary atom has the proved negligible error. -/
theorem actual_primary_from_bits_eventually (constant : ℕ) (hc : 1≤constant) :
    ∀ᶠ n : ℕ in atTop,∀ (word : Fin (n+n) → Fin 2) (color : Fin (Parameters.modulus n)),
      |(actualPrimaryFromBits constant n word color.val : ℝ)-
        actualPrimary (constant : ℝ) n (ParameterProgram.beta n word).value color|≤
        actualPrimaryProgramError n := by
  filter_upwards [actual_primary_program_eventually constant hc] with n hh word color
  exact hh _ (actual_beta_program_typical n word).1 color

end
end AFT.V7Calibration
