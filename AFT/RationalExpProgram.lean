import AFT.RationalPiProgram

/-! # Executable positive rational approximations to a negative exponential -/
namespace AFT.RationalNumerics
open scoped BigOperators

def expSum (value : ℚ) (terms : ℕ) : ℚ :=
  ∑ index∈Finset.range terms,value^index/(index.factorial : ℕ)

/-- Range reduction followed by a positive Taylor polynomial and an integer
power. In particular no exponential or real floor is evaluated by the code. -/
def expNegScaled (argument : ℚ) (scale bits : ℕ) : ℚ :=
  (expSum (argument/(scale : ℚ)) (bits+scale+1))⁻¹^scale

def expScale (argument : ℚ) : ℕ := 2*⌈max argument 0⌉₊+1

def expNegApprox (argument : ℚ) (bits : ℕ) : ℚ :=
  expNegScaled (max argument 0) (expScale argument) bits

noncomputable section
open scoped Classical

theorem expSum_ge_one (value : ℚ) (hv : 0 ≤ value) (terms : ℕ) (ht : 0 < terms) :
    1 ≤ (expSum value terms : ℝ) := by
  have hh := Finset.single_le_sum (f := fun i : ℕ => value^i/(i.factorial : ℕ))
    (fun i _ => by positivity) (Finset.mem_range.mpr ht)
  have hh' : (1 : ℚ) ≤ expSum value terms := by simpa only [pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,expSum] using hh
  exact_mod_cast hh'

theorem expSum_error (value : ℚ) (hv : 0 ≤ value) (hv' : value ≤ 1/2)
    (terms : ℕ) (ht : 0 < terms) :
    |(expSum value terms : ℝ)-Real.exp value| ≤ 2*(1/2 : ℝ)^terms := by
  have hv0 : (0 : ℝ) ≤ value := by exact_mod_cast hv
  have hv1 : (value : ℝ) ≤ 1/2 := by
    have hh : value*2 ≤ 1 := (le_div_iff₀ (by norm_num : (0 : ℚ) < 2)).mp hv'
    have hh' : (value : ℝ)*2 ≤ 1 := by exact_mod_cast hh
    linarith
  have hterm : (1 : ℝ) ≤ terms := by exact_mod_cast ht
  have hfactorial : (1 : ℝ) ≤ terms.factorial := by exact_mod_cast Nat.factorial_pos terms
  have hden : (0 : ℝ) < (terms.factorial : ℝ)*terms := by positivity
  have hquot : ((terms+1 : ℕ) : ℝ)/((terms.factorial : ℝ)*terms) ≤ 2 := by
    apply (div_le_iff₀ hden).mpr
    push_cast
    nlinarith
  have hh := Real.exp_bound (x := (value : ℝ)) (by rw [abs_of_nonneg hv0]; linarith) ht
  have he : (expSum value terms : ℝ)=∑ i∈Finset.range terms,(value : ℝ)^i/(i.factorial : ℕ) := by
    unfold expSum
    push_cast
    rfl
  rw [he,abs_sub_comm]
  apply hh.trans
  rw [abs_of_nonneg hv0]
  exact (mul_le_mul (pow_le_pow_left₀ hv0 hv1 terms) hquot (by positivity) (by positivity)).trans_eq (mul_comm _ _)

/-- Taking reciprocals of quantities at least one has Lipschitz constant
one; it avoids amplification by an exponentially large positive exponential. -/
theorem inv_error_of_ge_one (first second : ℝ) (hf : 1 ≤ first) (hs : 1 ≤ second) :
    |first⁻¹-second⁻¹| ≤ |first-second| := by
  have hfirst : first ≠ 0 := by linarith
  have hsecond : second ≠ 0 := by linarith
  have he : first⁻¹-second⁻¹=(second-first)/(first*second) := by field_simp
  rw [he,abs_div,abs_sub_comm,abs_of_nonneg (by positivity : 0 ≤ first*second)]
  exact div_le_self (abs_nonneg _) (by nlinarith)

theorem power_error_unit_interval (first second : ℝ)
    (hf : 0 ≤ first ∧ first ≤ 1) (hs : 0 ≤ second ∧ second ≤ 1) (count : ℕ) :
    |first^count-second^count| ≤ (count : ℝ)*|first-second| := by
  have hh := abs_pow_sub_pow_le first second count
  rw [abs_of_nonneg hf.1,abs_of_nonneg hs.1] at hh
  have hp : max first second^(count-1) ≤ 1 := pow_le_one₀ (le_max_of_le_left hf.1) (max_le hf.2 hs.2)
  calc
    _ ≤ |first-second| *count*max first second^(count-1) := hh
    _ ≤ |first-second| *count*1 := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

/-- A polynomial range reduction parameter is sufficient for any requested
number of binary digits. The approximation remains positive and bounded. -/
theorem expNegScaled_error (argument : ℚ) (scale bits : ℕ)
    (ha : 0 ≤ argument) (hscale : 0 < scale) (hbound : 2*argument ≤ (scale : ℚ)) :
    |(expNegScaled argument scale bits : ℝ)-Real.exp (-(argument : ℝ))| ≤ 1/(2 : ℝ)^bits := by
  let value : ℚ := argument/(scale : ℚ)
  let terms := bits+scale+1
  have hs0 : (0 : ℚ) < scale := by exact_mod_cast hscale
  have hv0 : 0 ≤ value := div_nonneg ha hs0.le
  have hv1 : value ≤ 1/2 := by
    apply (div_le_iff₀ hs0).mpr
    dsimp [value]
    linarith
  have ht : 0 < terms := by dsimp [terms]; omega
  have hfirst := expSum_ge_one value hv0 terms ht
  have hsecond : (1 : ℝ) ≤ Real.exp (value : ℝ) := Real.one_le_exp_iff.mpr (by exact_mod_cast hv0)
  have hpi := power_error_unit_interval ((expSum value terms : ℝ)⁻¹) ((Real.exp (value : ℝ))⁻¹)
    ⟨by positivity,inv_le_one_of_one_le₀ hfirst⟩ ⟨by positivity,inv_le_one_of_one_le₀ hsecond⟩ scale
  have hi := inv_error_of_ge_one (expSum value terms) (Real.exp (value : ℝ)) hfirst hsecond
  have happrox := (hpi.trans (mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg scale))).trans
    (mul_le_mul_of_nonneg_left (expSum_error value hv0 hv1 terms ht) (Nat.cast_nonneg scale))
  have hexp : (Real.exp (value : ℝ))⁻¹^scale=Real.exp (-(argument : ℝ)) := by
    rw [← Real.exp_neg,← Real.exp_nat_mul]
    congr 1
    dsimp [value]
    push_cast
    field_simp
  have hprogram : (expNegScaled argument scale bits : ℝ)=(expSum value terms : ℝ)⁻¹^scale := by
    simp only [expNegScaled,value,terms,Rat.cast_pow,Rat.cast_inv]
  rw [hprogram,← hexp]
  apply happrox.trans
  have hsbound : (scale : ℝ) ≤ (2 : ℝ)^scale := by exact_mod_cast (Nat.lt_two_pow_self (n:=scale)).le
  calc
    _ ≤ (2 : ℝ)^scale*(2*(1/2 : ℝ)^terms) := mul_le_mul_of_nonneg_right hsbound (by positivity)
    _ = _ := by
      dsimp [terms]
      rw [pow_add,pow_add,div_pow,one_pow,div_pow,one_pow]
      field_simp

theorem expScale_positive (argument : ℚ) : 0 < expScale argument := by
  unfold expScale
  omega

theorem expNegApprox_error (argument : ℚ) (bits : ℕ) :
    |(expNegApprox argument bits : ℝ)-Real.exp (-max (argument : ℝ) 0)| ≤ 1/(2 : ℝ)^bits := by
  have hb : 2*max argument 0 ≤ (expScale argument : ℚ) := by
    have hh := Nat.le_ceil (max argument 0)
    simp only [expScale,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    linarith
  have hh := expNegScaled_error (max argument 0) (expScale argument) bits
    (le_max_right _ _) (expScale_positive argument) hb
  simpa only [expNegApprox,Rat.cast_max,Rat.cast_zero] using hh

theorem expNegApprox_positive (argument : ℚ) (bits : ℕ) : 0 < expNegApprox argument bits := by
  have hs : (0 : ℚ) < expScale argument := by exact_mod_cast expScale_positive argument
  have hh := expSum_ge_one (max argument 0/(expScale argument : ℚ))
    (div_nonneg (le_max_right _ _) hs.le) (bits+expScale argument+1) (by omega)
  have hh' : (0 : ℚ) < expSum (max argument 0/(expScale argument : ℚ)) (bits+expScale argument+1) := by
    have hh0 : (0 : ℝ) < (expSum (max argument 0/(expScale argument : ℚ)) (bits+expScale argument+1) : ℝ) := by linarith
    exact_mod_cast hh0
  exact pow_pos (inv_pos.mpr hh') _

/-- On nonnegative arguments the negative exponential is globally
one-Lipschitz. This controls the separate rational argument approximation. -/
theorem exp_neg_lipschitz (first second : ℝ) (hf : 0 ≤ first) (hs : 0 ≤ second) :
    |Real.exp (-first)-Real.exp (-second)| ≤ |first-second| := by
  have ordered (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
      Real.exp (-a)-Real.exp (-b) ≤ b-a := by
    have he := Real.add_one_le_exp (a-b)
    have hm := mul_le_mul_of_nonneg_left he (Real.exp_pos (-a)).le
    have heq : Real.exp (-a)*Real.exp (a-b)=Real.exp (-b) := by rw [← Real.exp_add]; congr 1; ring
    rw [heq] at hm
    have hl : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hh := mul_le_mul_of_nonneg_left hl (sub_nonneg.mpr hab)
    nlinarith
  rcases le_total first second with h|h
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))),
      abs_of_nonpos (sub_nonpos.mpr h)]
    have hh := ordered first second hf h
    linarith
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr (by linarith))),
      abs_of_nonneg (sub_nonneg.mpr h)]
    have hh := ordered second first hs h
    linarith

end
end AFT.RationalNumerics
