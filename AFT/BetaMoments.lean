import AFT.BetaRationalCDF

/-! # Actual positive and negative moment bounds for beta tails -/
namespace AFT.BetaReference
open MeasureTheory
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

def momentCoefficient (K n s : ℕ) : ℝ :=
  ∏ j∈Finset.range s,((K+j+1 : ℕ) : ℝ)/(K+n+j+2 : ℕ)

theorem momentCoefficient_pos (K n s : ℕ) : 0 < momentCoefficient K n s := by
  apply Finset.prod_pos
  intro j _
  positivity

private theorem density_succ (K n : ℕ) (x : ℝ) :
    x*density K n x=(((K+1 : ℕ) : ℝ)/(K+n+2 : ℕ))*density (K+1) n x := by
  unfold density
  rw [show K+1+n+1=(K+n+1)+1 by omega,Nat.factorial_succ (K+n+1),Nat.factorial_succ K]
  simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
  have hK : (K.factorial : ℝ)≠0 := by positivity
  have hn : (n.factorial : ℝ)≠0 := by positivity
  have hK1 : (K : ℝ)+1≠0 := by positivity
  have hN : (K : ℝ)+(n : ℝ)+2≠0 := by positivity
  field_simp
  ring

/-- Multiplication by a power is an exact change of the integer beta shape. -/
theorem moment_density (K n s : ℕ) (x : ℝ) :
    x^s*density K n x=momentCoefficient K n s*density (K+s) n x := by
  induction s with
  | zero => simp [momentCoefficient]
  | succ s ih =>
    rw [pow_succ,mul_assoc,mul_comm x (density K n x),← mul_assoc,ih]
    rw [mul_assoc,mul_comm (density (K+s) n x) x,density_succ (K+s)]
    simp only [momentCoefficient,Finset.prod_range_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    ring

/-- Genuine beta moment integral, with no probabilistic approximation. -/
theorem moment_integral (K n s : ℕ) :
    (∫ x : ℝ in (0 : ℝ)..1,x^s*density K n x)=momentCoefficient K n s := by
  simp_rw [moment_density]
  rw [intervalIntegral.integral_const_mul _ (density (K+s) n),density_integral_one,mul_one]

theorem momentCoefficient_upper (K n s : ℕ) :
    momentCoefficient K n s ≤ (((K+s : ℕ) : ℝ)/(K+n+1 : ℕ))^s := by
  unfold momentCoefficient
  calc
    _  ≤  ∏ _j∈Finset.range s,(((K+s : ℕ) : ℝ)/(K+n+1 : ℕ)) := by
      apply Finset.prod_le_prod
      · intro j _; positivity
      · intro j hj
        have hj := Finset.mem_range.mp hj
        exact div_le_div₀ (by positivity) (by exact_mod_cast (show K+j+1 ≤ K+s by omega))
          (by positivity) (by exact_mod_cast (show K+n+1 ≤ K+n+j+2 by omega))
    _ = _ := by simp only [Finset.prod_const,Finset.card_range]

/-- A matching lower moment bound supplies negative-moment lower tails. -/
theorem momentCoefficient_lower (K n s : ℕ) :
    (((K+1 : ℕ) : ℝ)/(K+n+s+1 : ℕ))^s ≤ momentCoefficient K n s := by
  unfold momentCoefficient
  calc
    _ = ∏ _j∈Finset.range s,(((K+1 : ℕ) : ℝ)/(K+n+s+1 : ℕ)) := by simp only [Finset.prod_const,Finset.card_range]
    _  ≤  _ := by
      apply Finset.prod_le_prod
      · intro j _; positivity
      · intro j hj
        have hj := Finset.mem_range.mp hj
        exact div_le_div₀ (by positivity) (by exact_mod_cast (show K+1 ≤ K+j+1 by omega))
          (by positivity) (by exact_mod_cast (show K+n+j+2 ≤ K+n+s+1 by omega))

private theorem density_nonneg_unit (K n : ℕ) (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ density K n x := by unfold density; exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hx _)) (pow_nonneg (sub_nonneg.mpr hx1) _)

/-- Upper beta tail from the true moment integral. -/
theorem upper_tail_le_moment (K n s : ℕ) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    (∫ x : ℝ in a..1,density K n x) ≤ ((((K+s : ℕ) : ℝ)/(K+n+1 : ℕ))/a)^s := by
  have hi : Continuous (density K n) := by unfold density; fun_prop
  have hm : Continuous (fun x : ℝ => x^s*density K n x) := by fun_prop
  have hmono : a^s*(∫ x : ℝ in a..1,density K n x) ≤ ∫ x : ℝ in a..1,x^s*density K n x := by
    rw [← intervalIntegral.integral_const_mul (a^s) (fun x : ℝ => density K n x)]
    apply intervalIntegral.integral_mono_on ha1 ((continuous_const.mul hi).intervalIntegrable _ _) (hm.intervalIntegrable _ _)
    intro x hx
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le hx.1 s) (density_nonneg_unit K n x (ha.le.trans hx.1) hx.2)
  have hsub : (∫ x : ℝ in a..1,x^s*density K n x) ≤ momentCoefficient K n s := by
    rw [← moment_integral]
    apply intervalIntegral.integral_mono_interval ha.le ha1 le_rfl
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact mul_nonneg (pow_nonneg hx.1.le _) (density_nonneg_unit K n x hx.1.le hx.2)
    · exact hm.intervalIntegrable _ _
  have hh := hmono.trans (hsub.trans (momentCoefficient_upper K n s))
  rw [div_pow]
  apply (le_div_iff₀ (pow_pos ha s)).mpr
  simpa only [mul_comm] using hh

/-- Lower tail from an actual lower-shape beta density and its moment.
This remains effective at half the mean, unlike the crude `e N a/K` bound. -/
theorem lower_tail_le_negative_moment (K n s : ℕ) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (∫ x : ℝ in (0 : ℝ)..a,density (K+s) n x) ≤ 
      (a*((K+n+s+1 : ℕ) : ℝ)/(K+1 : ℕ))^s := by
  have hi : Continuous (density K n) := by unfold density; fun_prop
  have his : Continuous (density (K+s) n) := by unfold density; fun_prop
  have hmono : momentCoefficient K n s*(∫ x : ℝ in (0 : ℝ)..a,density (K+s) n x) ≤ 
      a^s*(∫ x : ℝ in (0 : ℝ)..a,density K n x) := by
    rw [← intervalIntegral.integral_const_mul _ (density (K+s) n),← intervalIntegral.integral_const_mul _ (density K n)]
    apply intervalIntegral.integral_mono_on ha ((continuous_const.mul his).intervalIntegrable _ _) ((continuous_const.mul hi).intervalIntegrable _ _)
    intro x hx
    change momentCoefficient K n s*density (K+s) n x ≤ a^s*density K n x
    rw [← moment_density]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx.1 hx.2 s) (density_nonneg_unit K n x hx.1 (hx.2.trans ha1))
  have htail : (∫ x : ℝ in (0 : ℝ)..a,density K n x) ≤ 1 := by
    rw [← density_integral_one K n]
    apply intervalIntegral.integral_mono_interval le_rfl ha ha1
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact density_nonneg_unit K n x hx.1.le hx.2
    · exact hi.intervalIntegrable _ _
  have hh : (∫ x : ℝ in (0 : ℝ)..a,density (K+s) n x) ≤ a^s/momentCoefficient K n s := by
    apply (le_div_iff₀ (momentCoefficient_pos _ _ _)).mpr
    simpa only [mul_comm,mul_one] using hmono.trans (mul_le_mul_of_nonneg_left htail (pow_nonneg ha _))
  apply hh.trans
  have hp : 0 < (((K+1 : ℕ) : ℝ)/(K+n+s+1 : ℕ))^s := by positivity
  apply (div_le_div_of_nonneg_left (pow_nonneg ha _) hp (momentCoefficient_lower K n s)).trans_eq
  rw [← div_pow]
  congr 1
  field_simp

end
end AFT.BetaReference
