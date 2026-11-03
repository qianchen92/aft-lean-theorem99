import AFT.ActualPrimaryReciprocalProgram
import AFT.ActualBoundaryNormalizer

/-! # Stable evaluation of the actual interior primary mass -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators

def actualInteriorTest (constant n : ℕ) (color : ℤ) : Bool :=
  decide (¬ (color<actualBoundaryHalfProgram constant n ∨
    ((ParameterProgram.modulus n).value : ℤ)-1-actualBoundaryHalfProgram constant n<color))

def actualInteriorMassProgram (constant n : ℕ) (beta : ℚ) : ℚ :=
  ∑ color∈Finset.range (ParameterProgram.modulus n).value,
    if actualInteriorTest constant n color then actualPrimaryProgram constant n beta color else 0

def actualInteriorReciprocalProgram (constant n : ℕ) (beta : ℚ) : ℚ :=
  (max (actualInteriorMassProgram constant n beta)
    (1/(8*(ParameterProgram.modulus n).value : ℚ)))⁻¹

noncomputable section
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 350000
local instance interiorMassFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

theorem actualInteriorTest_eq (constant n : ℕ) (color : Fin (Parameters.modulus n)) :
    actualInteriorTest constant n color.val=decide (color∈(boundaryPalette (Parameters.modulus n)
      (boundaryHalf (constant : ℝ) n))ᶜ) := by
  simp only [actualInteriorTest,actualBoundaryHalfProgram_eq,ParameterProgram.modulus_value,
    Finset.mem_compl,mem_boundaryPalette]

def actualInteriorMass (constant : ℝ) (n : ℕ) (beta : ℝ) : ℝ :=
  ∑ color∈(boundaryPalette (Parameters.modulus n) (boundaryHalf constant n))ᶜ,
    (actualPrimaryLaw constant n beta).weight color

def actualInteriorMassProgramError (n : ℕ) : ℝ := 2*(n : ℝ)^40*actualPrimaryProgramError n

def actualInteriorReciprocalProgramError (n : ℕ) : ℝ :=
  256*(n : ℝ)^80*actualInteriorMassProgramError n

theorem actualInteriorMassProgramError_negligible : Negligible actualInteriorMassProgramError := by
  convert (actualPrimaryProgramError_negligible.mul_polynomial 40).const_mul 2 using 1
  funext n;unfold actualInteriorMassProgramError;ring

theorem actualInteriorReciprocalProgramError_negligible : Negligible actualInteriorReciprocalProgramError := by
  convert (actualInteriorMassProgramError_negligible.mul_polynomial 80).const_mul 256 using 1
  funext n;unfold actualInteriorReciprocalProgramError;ring

theorem actual_interior_mass_program_eventually (constant : ℕ) (hc : 1 ≤ constant) (beta : ℕ → ℚ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ (beta n : ℝ) ∧
      (beta n : ℝ) ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
      1/(4*(Parameters.modulus n : ℝ)) ≤ actualInteriorMass constant n (beta n) ∧
      |(actualInteriorMassProgram constant n (beta n) : ℝ)-actualInteriorMass constant n (beta n)| ≤
        actualInteriorMassProgramError n := by
  filter_upwards [actual_primary_program_eventually constant hc,
    actual_reference_laws_eventually (constant : ℝ) (by exact_mod_cast hc) (fun n => beta n) hbeta,
    actual_primary_law_quarter_lower_eventually (constant : ℝ) (by exact_mod_cast hc) (fun n => beta n) hbeta,
    actual_boundary_profiles_eventually (constant : ℝ) (by exact_mod_cast hc),
    hbeta,eventually_ge_atTop 2] with n hp hl hlow hint hb hn
  have hq : (Parameters.modulus n : ℝ) ≤ 2*(n : ℝ)^40 := by
    have hh := (Parameters.modulus_bounds n).2
    rw [Parameters.security_eq n hn] at hh
    exact_mod_cast hh
  have he (color : Fin (Parameters.modulus n)) :
      |(actualPrimaryProgram constant n (beta n) color.val : ℝ)-
        (actualPrimaryLaw constant n (beta n)).weight color| ≤ actualPrimaryProgramError n := by
    rw [hl.1]
    exact hp (beta n) hb.1 color
  have he0 : 0 ≤ actualPrimaryProgramError n :=
    (abs_nonneg _).trans (he ⟨0,(Parameters.modulus_prime n).pos⟩)
  constructor
  · obtain ⟨color,hcolor⟩ := hint.2.1
    have hcolor' : color∈(boundaryPalette (Parameters.modulus n) (boundaryHalf (constant : ℝ) n))ᶜ := by
      simpa only [Finset.mem_compl] using hcolor
    exact (hlow color).trans (Finset.single_le_sum
      (fun c _ => (actualPrimaryLaw constant n (beta n)).nonneg c) hcolor')
  · have hprog : (actualInteriorMassProgram constant n (beta n) : ℝ)=
        ∑ color : Fin (Parameters.modulus n),if color∈(boundaryPalette (Parameters.modulus n)
          (boundaryHalf (constant : ℝ) n))ᶜ then (actualPrimaryProgram constant n (beta n) color.val : ℝ) else 0 := by
      simp only [actualInteriorMassProgram,ParameterProgram.modulus_value,Rat.cast_sum]
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro color _
      simp only [actualInteriorTest_eq,decide_eq_true_eq,apply_ite,Rat.cast_zero]
      split_ifs <;> rfl
    have hmass : actualInteriorMass constant n (beta n)=
        ∑ color : Fin (Parameters.modulus n),if color∈(boundaryPalette (Parameters.modulus n)
          (boundaryHalf (constant : ℝ) n))ᶜ then (actualPrimaryLaw constant n (beta n)).weight color else 0 := by
      unfold actualInteriorMass
      symm
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext color;simp
      · intro color _;rfl
    rw [hprog,hmass,← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _color : Fin (Parameters.modulus n),actualPrimaryProgramError n := by
        apply Finset.sum_le_sum
        intro color _
        split_ifs
        · exact he color
        · simpa only [sub_self,abs_zero] using he0
      _ ≤ actualInteriorMassProgramError n := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right hq he0

theorem actual_interior_reciprocal_program_eventually (constant : ℕ) (hc : 1 ≤ constant) (beta : ℕ → ℚ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ (beta n : ℝ) ∧
      (beta n : ℝ) ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
      0 < (actualInteriorReciprocalProgram constant n (beta n) : ℝ) ∧
      (actualInteriorReciprocalProgram constant n (beta n) : ℝ) ≤ 16*(n : ℝ)^40 ∧
      |(actualInteriorReciprocalProgram constant n (beta n) : ℝ)-
        (actualInteriorMass constant n (beta n))⁻¹| ≤ actualInteriorReciprocalProgramError n := by
  filter_upwards [actual_interior_mass_program_eventually constant hc beta hbeta,eventually_ge_atTop 2]
    with n hm hn
  have hq0 : (0 : ℝ) < Parameters.modulus n := by exact_mod_cast (Parameters.modulus_prime n).pos
  have hq : (Parameters.modulus n : ℝ) ≤ 2*(n : ℝ)^40 := by
    have hh := (Parameters.modulus_bounds n).2
    rw [Parameters.security_eq n hn] at hh
    exact_mod_cast hh
  have hlo : 0 < 1/(8*(Parameters.modulus n : ℝ)) := by positivity
  have hl : 1/(8*(Parameters.modulus n : ℝ)) ≤ actualInteriorMass constant n (beta n) :=
    (one_div_le_one_div_of_le (by positivity) (by nlinarith)).trans hm.1
  have he0 : 0 ≤ actualInteriorMassProgramError n := (abs_nonneg _).trans hm.2
  simp only [actualInteriorReciprocalProgram,Rat.cast_inv,Rat.cast_max,Rat.cast_div,Rat.cast_one,
    Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast,ParameterProgram.modulus_value]
  refine ⟨inv_pos.mpr (hlo.trans_le (le_max_right _ _)),?_,?_⟩
  · have hh := one_div_le_one_div_of_le hlo (le_max_right (actualInteriorMassProgram constant n (beta n) : ℝ) _)
    simp only [one_div,inv_inv] at hh
    simpa only [one_div] using hh.trans (show 8*(Parameters.modulus n : ℝ) ≤ 16*(n : ℝ)^40 by nlinarith)
  · apply (clippedInverse_error _ _ _ hlo hl).trans
    calc
      _ ≤ actualInteriorMassProgramError n/(1/(8*(Parameters.modulus n : ℝ)))^2 :=
        div_le_div_of_nonneg_right hm.2 (sq_nonneg _)
      _ = 64*(Parameters.modulus n : ℝ)^2*actualInteriorMassProgramError n := by field_simp;ring
      _ ≤ actualInteriorReciprocalProgramError n := by
        unfold actualInteriorReciprocalProgramError
        have hq2 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ Parameters.modulus n) hq 2
        have hh := mul_le_mul_of_nonneg_right hq2 he0
        nlinarith [show ((2*(n : ℝ)^40)^2)=4*(n : ℝ)^80 by ring]

end
end AFT.V7Calibration
