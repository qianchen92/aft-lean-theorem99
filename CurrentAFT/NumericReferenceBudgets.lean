import CurrentAFT.RationalPairedLiftProgram
import CurrentAFT.FixedOrderAccuracy

/-! # Current numerical reference budgets at `bits = security`

All constants below are derived from the actual current prime and
population bounds. Exponential precision dominates every fixed public
polynomial; the number of precision bits is not fixed in security.
-/
namespace CurrentAFT.NumericReferenceBudgets
open Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.dimension

theorem base_pow_dyadic_tendsto (degree : ℕ) :
    Tendsto (fun security : ℕ => (Parameters.base security:ℝ)^degree/(2:ℝ)^security) atTop (𝓝 0) := by
  have h := (tendsto_pow_const_div_const_pow_of_one_lt degree (by norm_num : (1:ℝ)<2)).comp
    (tendsto_add_atTop_nat 2)
  convert h.const_mul 4 using 1
  · funext security
    simp only [Parameters.base, Nat.cast_add, Nat.cast_ofNat]
    norm_num
    ring
  · norm_num

theorem polynomial_dyadic_eventually (constant : ℝ) (degree accuracyOrder : ℕ) :
    ∀ᶠ security : ℕ in atTop,
      constant*(Parameters.base security:ℝ)^degree/(2:ℝ)^security ≤ inversePower security accuracyOrder := by
  have ht : Tendsto (fun security : ℕ => constant*((Parameters.base security:ℝ)^(degree+accuracyOrder)/(2:ℝ)^security))
      atTop (𝓝 0) := by simpa only [mul_zero] using (base_pow_dyadic_tendsto (degree+accuracyOrder)).const_mul constant
  have h := ht.eventually_le_const (by norm_num : (0:ℝ)<1)
  filter_upwards [h] with security hbound
  have hb := FirstResponse.base_pos security
  unfold inversePower
  apply (le_div_iff₀ (pow_pos hb accuracyOrder)).mpr
  convert hbound using 1
  rw [pow_add]
  ring

private theorem paired_coarse (base q dimension : ℝ) (hb : 1 ≤ base) (hq : 1 ≤ q) (hd : 1 ≤ dimension) :
    q+2*q^2*(64*base*dimension+1)+4*q^2*(64*base*dimension*q+2) ≤ 512*q^3*base*dimension := by
  have hb0 : 0 ≤ base := by linarith
  have hq0 : 0 ≤ q := by linarith
  have hd0 : 0 ≤ dimension := by linarith
  have hbd : 1 ≤ base*dimension := by nlinarith
  have hbdq : 1 ≤ base*dimension*q := by nlinarith
  have hq2 : q^2 ≤ q^3 := pow_le_pow_right₀ hq (by omega)
  have hq1 : q ≤ q^3 := by simpa using pow_le_pow_right₀ hq (by omega : 1 ≤ 3)
  calc
    _ ≤ q+2*q^2*(65*base*dimension)+4*q^2*(66*base*dimension*q) := by
      gcongr <;> nlinarith
    _ = q+130*q^2*base*dimension+264*q^3*base*dimension := by ring
    _ ≤ q^3*base*dimension+130*q^3*base*dimension+264*q^3*base*dimension := by
      apply add_le_add
      · apply add_le_add
        · exact hq1.trans (by nlinarith [mul_le_mul_of_nonneg_left hbd (pow_nonneg hq0 3)])
        · gcongr
      · rfl
    _ ≤ _ := by nlinarith [mul_nonneg (pow_nonneg hq0 3) (mul_nonneg hb0 hd0)]

def pairedConstant : ℝ := 512*131072^3*131074

theorem pairedConstant_nonneg : 0 ≤ pairedConstant := by unfold pairedConstant; positivity

theorem paired_errorConstant_le (security : ℕ) :
    RationalPairedLiftProgram.errorConstant security ≤ pairedConstant*(Parameters.base security:ℝ)^353 := by
  have hb : (1:ℝ) ≤ Parameters.base security := by exact_mod_cast (Parameters.base_ge_two security).trans' (by norm_num)
  have hq : (1:ℝ) ≤ Parameters.modulus security := by exact_mod_cast (Parameters.modulus_spec security).2.pos
  have hdN : 1 ≤ Parameters.dimension security := by
    have hp := (Parameters.dimension_bounds security).1
    have hb0 := Parameters.base_pos security
    have hpow : 0 < Parameters.base security^160 := pow_pos hb0 _
    omega
  have hd : (1:ℝ) ≤ Parameters.dimension security := by exact_mod_cast hdN
  have hqUpper : (Parameters.modulus security:ℝ) ≤ 131072*(Parameters.base security:ℝ)^64 := by
    exact_mod_cast (Parameters.modulus_bounds security).2
  have hdUpper : (Parameters.dimension security:ℝ) ≤ 131074*(Parameters.base security:ℝ)^160 := by
    exact_mod_cast (Parameters.dimension_bounds security).2
  unfold RationalPairedLiftProgram.errorConstant
  dsimp only
  calc
    _ ≤ 512*(Parameters.modulus security:ℝ)^3*(Parameters.base security:ℝ)*Parameters.dimension security :=
      paired_coarse _ _ _ hb hq hd
    _ ≤ 512*(131072*(Parameters.base security:ℝ)^64)^3*(Parameters.base security:ℝ)*
        (131074*(Parameters.base security:ℝ)^160) := by gcongr
    _ = _ := by unfold pairedConstant; rw [mul_pow, ← pow_mul]; ring_nf

theorem paired_error_negligible (accuracyOrder : ℕ) :
    ∀ᶠ security : ℕ in atTop,
      RationalPairedLiftProgram.errorConstant security/(2:ℝ)^security ≤ inversePower security accuracyOrder := by
  filter_upwards [polynomial_dyadic_eventually pairedConstant 353 accuracyOrder] with security h
  exact (div_le_div_of_nonneg_right (paired_errorConstant_le security) (by positivity)).trans h

theorem scalar_precision_eventually :
    ∀ᶠ security : ℕ in atTop,
      1/(2:ℝ)^security ≤ 1/(4*(Parameters.base security:ℝ)) := by
  filter_upwards [polynomial_dyadic_eventually 4 1 0] with security h
  have hb := FirstResponse.base_pos security
  apply (le_div_iff₀ (by positivity : (0:ℝ)<4*Parameters.base security)).mpr
  simpa only [inversePower, pow_zero, div_one, pow_one, mul_comm, one_div, mul_assoc, div_eq_mul_inv,
    inv_one, one_mul, mul_one] using h

theorem primary_precision_eventually :
    ∀ᶠ security : ℕ in atTop,
      64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^security) ≤
        1/(4*(Parameters.modulus security:ℝ)) := by
  filter_upwards [polynomial_dyadic_eventually (256*131072*131074) 225 0] with security h
  have hq := FirstResponse.modulus_pos security
  have hqUpper : (Parameters.modulus security:ℝ) ≤ 131072*(Parameters.base security:ℝ)^64 := by
    exact_mod_cast (Parameters.modulus_bounds security).2
  have hdUpper : (Parameters.dimension security:ℝ) ≤ 131074*(Parameters.base security:ℝ)^160 := by
    exact_mod_cast (Parameters.dimension_bounds security).2
  have hc : (4*(Parameters.modulus security:ℝ))*(64*(Parameters.base security:ℝ)*Parameters.dimension security) ≤
      (256*131072*131074)*(Parameters.base security:ℝ)^225 := by
    calc
      _ = 256*(Parameters.modulus security:ℝ)*(Parameters.base security:ℝ)*Parameters.dimension security := by ring
      _ ≤ 256*(131072*(Parameters.base security:ℝ)^64)*(Parameters.base security:ℝ)*
          (131074*(Parameters.base security:ℝ)^160) := by gcongr
      _ = _ := by ring_nf
  apply (le_div_iff₀ (by positivity : (0:ℝ)<4*Parameters.modulus security)).mpr
  calc
    _ = ((4*(Parameters.modulus security:ℝ))*(64*(Parameters.base security:ℝ)*Parameters.dimension security))/(2:ℝ)^security := by ring
    _ ≤ ((256*131072*131074)*(Parameters.base security:ℝ)^225)/(2:ℝ)^security :=
      div_le_div_of_nonneg_right hc (by positivity)
    _ ≤ 1 := by simpa only [inversePower, pow_zero, div_one] using h

theorem first_precision_eventually :
    ∀ᶠ security : ℕ in atTop, RationalFirstResponseProgram.PrecisionBudget security security := by
  filter_upwards [polynomial_dyadic_eventually (16*(8*131072+2)) 65 0] with security h
  have hb := FirstResponse.base_pos security
  have hb1 : (1:ℝ) ≤ Parameters.base security := by
    exact_mod_cast (Parameters.base_ge_two security).trans' (by norm_num)
  have hpower : (1:ℝ) ≤ (Parameters.base security:ℝ)^64 := one_le_pow₀ hb1
  have hqUpper : (Parameters.modulus security:ℝ) ≤ 131072*(Parameters.base security:ℝ)^64 := by
    exact_mod_cast (Parameters.modulus_bounds security).2
  have hc : (16*(Parameters.base security:ℝ))*(8*(Parameters.modulus security:ℝ)+2) ≤
      (16*(8*131072+2))*(Parameters.base security:ℝ)^65 := by
    calc
      _ ≤ (16*(Parameters.base security:ℝ))*(8*(131072*(Parameters.base security:ℝ)^64)+2*(Parameters.base security:ℝ)^64) := by
        gcongr
        nlinarith
      _ = _ := by ring_nf
  unfold RationalFirstResponseProgram.PrecisionBudget
  apply (le_div_iff₀ (by positivity : (0:ℝ)<16*Parameters.base security)).mpr
  calc
    _ = ((16*(Parameters.base security:ℝ))*(8*(Parameters.modulus security:ℝ)+2))/(2:ℝ)^security := by ring
    _ ≤ ((16*(8*131072+2))*(Parameters.base security:ℝ)^65)/(2:ℝ)^security :=
      div_le_div_of_nonneg_right hc (by positivity)
    _ ≤ 1 := by simpa only [inversePower, pow_zero, div_one] using h

theorem precision_budgets_eventually :
    ∀ᶠ security : ℕ in atTop,
      1/(2:ℝ)^security ≤ 1/(4*(Parameters.base security:ℝ)) ∧
      64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^security) ≤
        1/(4*(Parameters.modulus security:ℝ)) ∧
      RationalFirstResponseProgram.PrecisionBudget security security := by
  filter_upwards [scalar_precision_eventually, primary_precision_eventually, first_precision_eventually]
    with security hs hp hf
  exact ⟨hs, hp, hf⟩

end
end CurrentAFT.NumericReferenceBudgets
