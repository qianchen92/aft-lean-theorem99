import AFT.BetaMoments
import AFT.ActualBetaCutoff

/-! # Negligible beta tails at the actual V7 calibration scale -/
namespace AFT.BetaReference
open MeasureTheory Filter
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- A buffered typical interval. The upper endpoint `3K/(2N)` leaves
room for an upward grid round while staying below the final `2K/N` limit. -/
theorem buffered_typical_tail_le (K n : ℕ) (hK : 8 ≤ K) (hN : 3*K ≤ 2*(K+n+1)) :
    (∫ x : ℝ in (0 : ℝ)..(K : ℝ)/(2*(K+n+1 : ℕ)),density K n x)+
      (∫ x : ℝ in (3*(K : ℝ))/(2*(K+n+1 : ℕ))..1,density K n x) ≤
        2*(3/4 : ℝ)^(K/8) := by
  let s := K/8
  have hs : s ≤ K := Nat.div_le_self _ _
  have hs8 : 8*s ≤ K := Nat.mul_div_le K 8
  have hsR : 8*(s : ℝ) ≤ K := by exact_mod_cast hs8
  have hKp : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hNp : (0 : ℝ) < (K+n+1 : ℕ) := by positivity
  have hNR : 3*(K : ℝ) ≤ 2*(K+n+1 : ℕ) := by exact_mod_cast hN
  have hlo := lower_tail_le_negative_moment (K-s) n s ((K : ℝ)/(2*(K+n+1 : ℕ)))
    (by positivity) ((div_le_one (by positivity)).mpr (by linarith))
  have hsum : K-s+s=K := Nat.sub_add_cancel hs
  rw [hsum] at hlo
  have hloBase : ((K : ℝ)/(2*(K+n+1 : ℕ)))*((K-s+n+s+1 : ℕ) : ℝ)/(K-s+1 : ℕ) ≤ 3/4 := by
    have htotal : K-s+n+s+1=K+n+1 := by omega
    rw [htotal]
    have hpos : (0 : ℝ) < (K-s+1 : ℕ) := by positivity
    have hcancel : ((K : ℝ)/(2*(K+n+1 : ℕ)))*((K+n+1 : ℕ) : ℝ)/(K-s+1 : ℕ)=
        (K : ℝ)/(2*(K-s+1 : ℕ)) := by field_simp
    rw [hcancel]
    apply (div_le_iff₀ (by positivity)).mpr
    rw [Nat.cast_add,Nat.cast_sub hs,Nat.cast_one]
    nlinarith
  have hlower : (∫ x : ℝ in (0 : ℝ)..(K : ℝ)/(2*(K+n+1 : ℕ)),density K n x) ≤ (3/4 : ℝ)^s :=
    hlo.trans (pow_le_pow_left₀ (by positivity) hloBase s)
  have hhi := upper_tail_le_moment K n s ((3*(K : ℝ))/(2*(K+n+1 : ℕ)))
    (by positivity) ((div_le_one (by positivity)).mpr hNR)
  have hhiBase : ((((K+s : ℕ) : ℝ)/(K+n+1 : ℕ))/((3*(K : ℝ))/(2*(K+n+1 : ℕ)))) ≤ 3/4 := by
    have he : ((((K+s : ℕ) : ℝ)/(K+n+1 : ℕ))/((3*(K : ℝ))/(2*(K+n+1 : ℕ))))=
        2*((K+s : ℕ) : ℝ)/(3*K) := by field_simp
    rw [he]
    apply (div_le_iff₀ (by positivity)).mpr
    push_cast
    nlinarith
  have hupper : (∫ x : ℝ in (3*(K : ℝ))/(2*(K+n+1 : ℕ))..1,density K n x) ≤ (3/4 : ℝ)^s :=
    hhi.trans (pow_le_pow_left₀ (by positivity) hhiBase s)
  linarith

/-- Fixed-base geometric tails are negligible whenever their true exponent
grows at least linearly with the security parameter. -/
theorem negligible_geometric_population (constant base : ℝ) (hc : 0 ≤ constant)
    (hb : 0 < base) (hb1 : base < 1) (population : ℕ → ℕ)
    (hpop : ∀ᶠ n in atTop,n ≤ population n) :
    Negligible (fun n => constant*base^population n) := by
  have hh := negligible_polynomial_stretched_exponential constant 0 1 (-Real.log base) hc (by norm_num)
    (neg_pos.mpr (Real.log_neg hb hb1))
  apply hh.of_eventually_le
  filter_upwards [hpop] with n hn
  rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
  simp only [pow_zero,mul_one,Real.rpow_one,neg_neg]
  have he : Real.exp (Real.log base*(n : ℝ))=base^n := by rw [mul_comm,Real.exp_nat_mul,Real.exp_log hb]
  rw [he]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hb.le hb1.le hn) hc

end
end AFT.BetaReference

namespace AFT.V7Calibration
open GaussianSource BetaReference MeasureTheory Filter
open scoped Topology
noncomputable section

def actualBetaBufferedTail (n : ℕ) : ℝ :=
  (∫ x : ℝ in (0 : ℝ)..(Parameters.legs n : ℝ)/(2*Parameters.dimension n),
    density (Parameters.legs n) (Parameters.dimension n-Parameters.legs n-1) x)+
  (∫ x : ℝ in (3*(Parameters.legs n : ℝ))/(2*Parameters.dimension n)..1,
    density (Parameters.legs n) (Parameters.dimension n-Parameters.legs n-1) x)

theorem actual_beta_buffered_tail_eventually :
    ∀ᶠ n in atTop,0 ≤ actualBetaBufferedTail n ∧ actualBetaBufferedTail n ≤ 2*(3/4 : ℝ)^(Parameters.legs n/8) := by
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hpop := Parameters.population_identity n
  have hb := Parameters.bodies_positive n
  have hsum : Parameters.legs n+(Parameters.dimension n-Parameters.legs n-1)+1=Parameters.dimension n := by omega
  have hlegs : 8 ≤ Parameters.legs n := by
    unfold Parameters.legs
    rw [Parameters.security_eq n hn]
    exact (by norm_num : 8 ≤ 2^30).trans (Nat.pow_le_pow_left hn 30)
  have hhalf : 3*Parameters.legs n ≤ 2*Parameters.dimension n := by omega
  have hh := buffered_typical_tail_le (Parameters.legs n) (Parameters.dimension n-Parameters.legs n-1) hlegs (by rwa [hsum])
  rw [hsum] at hh
  refine ⟨?_,hh⟩
  have hN : (0 : ℝ) < Parameters.dimension n := by exact_mod_cast (by omega : 0 < Parameters.dimension n)
  have hNR : 3*(Parameters.legs n : ℝ) ≤ 2*Parameters.dimension n := by exact_mod_cast hhalf
  apply add_nonneg
  · apply intervalIntegral.integral_nonneg (by positivity)
    intro x hx
    unfold density
    have hx1 : x ≤ 1 := hx.2.trans ((div_le_one (by positivity)).mpr (by linarith))
    exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hx.1 _)) (pow_nonneg (sub_nonneg.mpr hx1) _)
  · apply intervalIntegral.integral_nonneg ((div_le_one (by positivity)).mpr hNR)
    intro x hx
    have hx0 : 0 ≤ x := (by positivity : (0 : ℝ) ≤ (3*(Parameters.legs n : ℝ))/(2*Parameters.dimension n)).trans hx.1
    unfold density
    exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hx0 _)) (pow_nonneg (sub_nonneg.mpr hx.2) _)

theorem actual_beta_buffered_tail_negligible : Negligible actualBetaBufferedTail := by
  have hpop : ∀ᶠ n in atTop,n ≤ Parameters.legs n/8 := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    unfold Parameters.legs
    rw [Parameters.security_eq n hn]
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 8)).mpr
    have hp : 8 ≤ n^29 := (by norm_num : 8 ≤ 2^29).trans (Nat.pow_le_pow_left hn 29)
    have hh := Nat.mul_le_mul_left n hp
    simpa only [pow_succ',Nat.mul_comm n 8] using hh
  have hh := negligible_geometric_population 2 (3/4) (by norm_num) (by norm_num) (by norm_num)
    (fun n => Parameters.legs n/8) hpop
  apply hh.of_eventually_le
  filter_upwards [actual_beta_buffered_tail_eventually] with n hn
  rw [abs_of_nonneg hn.1,abs_of_nonneg (by positivity)]
  exact hn.2

end
end AFT.V7Calibration
