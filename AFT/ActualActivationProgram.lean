import AFT.ActualAuxiliaryGaussianProgram
import AFT.ActivationSharp
import AFT.BetaGridParameters

/-! # Rational evaluation of the actual marked-chart activation -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators

/-- The exact program cutoff is shared by both Gaussian zero atoms. -/
def actualLegZeroApprox (constant scale n bits : ℕ) : ℚ :=
  windowApproxWeight (actualAuxiliarySquaredWidth scale n) (actualLegCutoffProgram constant n-1) bits
    ⟨0,Finset.mem_Icc.mpr ⟨by omega,by omega⟩⟩

def actualFeatureCountProgram (constant n : ℕ) : ℕ := (2*actualLegCutoffProgram constant n-1)^2

/-- Real exponentials are replaced by their proved rational programs, while
the mark weight and feature count are exact. -/
def actualActivationApprox (constant n bits : ℕ) : ℚ :=
  1/(100*(actualFeatureCountProgram constant n : ℚ))*
    (actualLegZeroApprox constant 1 n (bits+1)*actualLegZeroApprox constant 10 n (bits+1))

def actualActivationInverseApprox (constant n bits : ℕ) : ℚ :=
  (actualActivationApprox constant n bits)⁻¹

noncomputable section
open scoped Topology
set_option backward.isDefEq.respectTransparency false

theorem actualFeatureCountProgram_eq (constant n : ℕ) :
    actualFeatureCountProgram constant n=legFeatureCount (constant : ℝ) n := by
  unfold actualFeatureCountProgram legFeatureCount
  rw [actualLegCutoffProgram_eq]

private theorem windowApproxWeight_le_one (squaredWidth : ℚ) (cutoff bits : ℕ) (point : Window cutoff) :
    windowApproxWeight squaredWidth cutoff bits point≤1 := by
  have hh := Finset.single_le_sum (fun point (_ : point∈Finset.univ) =>
    (windowApproxWeight_positive squaredWidth cutoff bits point).le) (Finset.mem_univ point)
  simpa only [windowApproxWeight_sum] using hh

theorem actualLegZeroApprox_bounds (constant scale n bits : ℕ) :
    0<actualLegZeroApprox constant scale n bits ∧ actualLegZeroApprox constant scale n bits≤1 :=
  ⟨windowApproxWeight_positive _ _ _ _,windowApproxWeight_le_one _ _ _ _⟩

/-- Uniform pointwise accuracy at the true scalar zero atom. -/
theorem actualLegZeroApprox_error (constant scale n bits : ℕ) (hs : 0<scale) (hn : 0<n) :
    |(actualLegZeroApprox constant scale n bits : ℝ)-
      (windowGaussian ((scale : ℝ)*n) (legCutoff (constant : ℝ) n-1)).weight
        (windowZero (legCutoff (constant : ℝ) n-1))|≤1/(2 : ℝ)^bits := by
  have hwidth : 0<actualAuxiliarySquaredWidth scale n := by unfold actualAuxiliarySquaredWidth; positivity
  have hsquare : ((scale : ℝ)*n)^2=(actualAuxiliarySquaredWidth scale n : ℝ) := by
    unfold actualAuxiliarySquaredWidth
    push_cast
    rfl
  have hh := windowApproxLaw_l1 (actualAuxiliarySquaredWidth scale n) ((scale : ℝ)*n)
    (actualLegCutoffProgram constant n-1) bits hwidth hsquare
  have hpoint := (Finset.single_le_sum (f:=fun point =>
    |(windowApproxLaw (actualAuxiliarySquaredWidth scale n) (actualLegCutoffProgram constant n-1) bits).weight point-
      (windowGaussian ((scale : ℝ)*n) (actualLegCutoffProgram constant n-1)).weight point|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ (windowZero (actualLegCutoffProgram constant n-1)))).trans hh
  change |(actualLegZeroApprox constant scale n bits : ℝ)-
    (windowGaussian ((scale : ℝ)*n) (actualLegCutoffProgram constant n-1)).weight
      (windowZero (actualLegCutoffProgram constant n-1))|≤_ at hpoint
  rw [windowGaussian_zero] at hpoint ⊢
  simpa only [actualLegCutoffProgram_eq] using hpoint

private theorem finite_weight_le_one {Source : Type*} [Fintype Source]
    (law : FiniteDist Source) (point : Source) : law.weight point≤1 := by
  simpa only [law.sum_one] using Finset.single_le_sum
    (fun color (_ : color∈Finset.univ) => law.nonneg color) (Finset.mem_univ point)

/-- The computed activation approximates the actual two-source event, not
an asymptotic surrogate such as a power of the security parameter. -/
theorem actualActivationApprox_error (constant n bits : ℕ) (hc : 1≤constant) (hn : 1≤n) :
    |(actualActivationApprox constant n bits : ℝ)-v7Activation (constant : ℝ) n|≤1/(2 : ℝ)^bits := by
  let cutoff := legCutoff (constant : ℝ) n-1
  let first := (windowGaussian n cutoff).weight (windowZero cutoff)
  let second := (windowGaussian (10*n) cutoff).weight (windowZero cutoff)
  let a : ℝ := actualLegZeroApprox constant 1 n (bits+1)
  let b : ℝ := actualLegZeroApprox constant 10 n (bits+1)
  have ha : |a-first|≤1/(2 : ℝ)^(bits+1) := by
    simpa only [Nat.cast_one,one_mul] using actualLegZeroApprox_error constant 1 n (bits+1) (by decide) hn
  have hb : |b-second|≤1/(2 : ℝ)^(bits+1) := by
    simpa only [Nat.cast_ofNat] using actualLegZeroApprox_error constant 10 n (bits+1) (by decide) hn
  have hb0 : 0≤b := by dsimp only [b]; exact_mod_cast (actualLegZeroApprox_bounds constant 10 n (bits+1)).1.le
  have hb1 : b≤1 := by dsimp only [b]; exact_mod_cast (actualLegZeroApprox_bounds constant 10 n (bits+1)).2
  have hf0 : 0≤first := (windowGaussian n cutoff).nonneg _
  have hf1 : first≤1 := finite_weight_le_one _ _
  have hprod : |a*b-first*second|≤1/(2 : ℝ)^bits := by
    rw [show a*b-first*second=(a-first)*b+first*(b-second) by ring]
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul,abs_of_nonneg hb0,abs_of_nonneg hf0]
    calc
      _ ≤ (1/(2 : ℝ)^(bits+1))*1+1*(1/(2 : ℝ)^(bits+1)) := by gcongr
      _ = _ := by rw [pow_succ]; field_simp; ring
  have hfpos := legFeatureCount_positive (constant : ℝ) n (by exact_mod_cast hc) hn
  have hden : (1 : ℝ)≤100*(actualFeatureCountProgram constant n : ℝ) := by
    rw [actualFeatureCountProgram_eq]
    have hh : (1 : ℝ)≤legFeatureCount (constant : ℝ) n := by exact_mod_cast hfpos
    linarith
  have heq : (actualActivationApprox constant n bits : ℝ)-v7Activation (constant : ℝ) n=
      (a*b-first*second)/(100*(actualFeatureCountProgram constant n : ℝ)) := by
    simp only [actualActivationApprox,Rat.cast_mul,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Rat.cast_natCast,
      v7Activation,activation,FiniteDist.prod_weight,actualFeatureCountProgram_eq]
    dsimp only [a,b,first,second,cutoff]
    ring
  rw [heq,abs_div,abs_of_pos (by linarith : 0<100*(actualFeatureCountProgram constant n : ℝ))]
  exact (div_le_self (abs_nonneg _) hden).trans hprod

theorem actualActivationApprox_positive (constant n bits : ℕ) (hc : 1≤constant) (hn : 1≤n) :
    0<actualActivationApprox constant n bits := by
  have hf : 0<actualFeatureCountProgram constant n := by
    rw [actualFeatureCountProgram_eq]
    exact legFeatureCount_positive _ _ (by exact_mod_cast hc) hn
  unfold actualActivationApprox
  exact mul_pos (by positivity) (mul_pos (actualLegZeroApprox_bounds _ _ _ _).1 (actualLegZeroApprox_bounds _ _ _ _).1)

def actualActivationInverseError (n : ℕ) : ℝ := 2*(n : ℝ)^10/(2 : ℝ)^n

theorem actualActivationInverseError_negligible : Negligible actualActivationInverseError := by
  have hm : Negligible (fun n : ℕ => 1/(2 : ℝ)^n) := by
    convert betaGridMesh_negligible using 1
    funext n
    simp only [betaGridMesh,Nat.cast_pow,Nat.cast_ofNat]
  convert (hm.mul_polynomial 10).const_mul 2 using 1
  funext n
  unfold actualActivationInverseError
  ring

/-- Division by the actual activation has only a polynomial precision loss.
This provides the first numerical denominator required by calibration. -/
theorem actual_activation_inverse_program_eventually (constant : ℕ) (hc : 1≤constant) :
    ∀ᶠ n : ℕ in atTop,
      |(actualActivationInverseApprox constant n n : ℝ)-(v7Activation (constant : ℝ) n)⁻¹|≤
        actualActivationInverseError n := by
  have hm : Negligible (fun n : ℕ => 1/(2 : ℝ)^n) := by
    convert betaGridMesh_negligible using 1
    funext n
    simp only [betaGridMesh,Nat.cast_pow,Nat.cast_ofNat]
  have hsmall := (hm.mul_polynomial 5).tendsto_zero.eventually_le_const (by norm_num : (0 : ℝ)<1/2)
  filter_upwards [v7Activation_lower_eventually (constant : ℝ) (by exact_mod_cast hc),hsmall,
    eventually_ge_atTop 1] with n hlower hsmall hn
  have hn0 : (0 : ℝ)<n := by exact_mod_cast hn
  let a : ℝ := actualActivationApprox constant n n
  let rho := v7Activation (constant : ℝ) n
  have ha0 : 0<a := by dsimp only [a]; exact_mod_cast actualActivationApprox_positive constant n n hc hn
  have hrho : 0<rho := lt_of_lt_of_le (by positivity : 0<((n : ℝ)^5)⁻¹) hlower
  have he := actualActivationApprox_error constant n n hc hn
  change |a-rho|≤1/(2 : ℝ)^n at he
  have hehalf : 1/(2 : ℝ)^n≤((n : ℝ)^5)⁻¹/2 := by
    have hh : (n : ℝ)^5*(1/(2 : ℝ)^n)≤1/2 := hsmall
    rw [show ((n : ℝ)^5)⁻¹/2=1/(2*(n : ℝ)^5) by ring]
    apply (le_div_iff₀ (by positivity : (0 : ℝ)<2*(n : ℝ)^5)).mpr
    nlinarith
  have halower : 1/(2*(n : ℝ)^5)≤a := by
    have hh := (abs_le.mp he).1
    change ((n : ℝ)^5)⁻¹≤rho at hlower
    have hident : 1/(2*(n : ℝ)^5)=((n : ℝ)^5)⁻¹/2 := by ring
    rw [hident]
    linarith
  have haInv : a⁻¹≤2*(n : ℝ)^5 := by
    have hh := one_div_le_one_div_of_le (by positivity : 0<1/(2*(n : ℝ)^5)) halower
    simpa only [one_div,inv_inv] using hh
  have hrInv : rho⁻¹≤(n : ℝ)^5 := by
    have hh := one_div_le_one_div_of_le (by positivity : 0<((n : ℝ)^5)⁻¹) hlower
    simpa only [one_div,inv_inv] using hh
  rw [actualActivationInverseApprox,Rat.cast_inv]
  change |a⁻¹-rho⁻¹|≤actualActivationInverseError n
  have hid : a⁻¹-rho⁻¹=(rho-a)*a⁻¹*rho⁻¹ := by field_simp
  rw [hid,abs_mul,abs_mul,abs_of_pos (inv_pos.mpr ha0),abs_of_pos (inv_pos.mpr hrho),abs_sub_comm rho a]
  calc
    _ ≤ (1/(2 : ℝ)^n)*(2*(n : ℝ)^5)*(n : ℝ)^5 := by gcongr
    _ = actualActivationInverseError n := by unfold actualActivationInverseError; ring

end
end AFT.V7Calibration
