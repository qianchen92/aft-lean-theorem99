import AFT.ActualPositiveReference
import AFT.BetaTail
import AFT.Negligible

/-! # The actual V7 inverse-beta cutoff has negligible rejected mass -/
namespace AFT.V7Calibration
open GaussianSource Filter MeasureTheory
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

def actualBoundaryFraction (C : ℝ) (n : ℕ) : ℝ :=
  (boundaryPalette (Parameters.modulus n) (boundaryHalf C n)).card/(Parameters.modulus n : ℝ)

def actualBetaCutoff (C : ℝ) (n : ℕ) : ℝ := actualBoundaryFraction C n/v7Activation C n

def actualBetaRejectedMass (C : ℝ) (n : ℕ) : ℝ :=
  ∫ x : ℝ in (0 : ℝ)..actualBetaCutoff C n,
    BetaReference.density (Parameters.legs n) (Parameters.dimension n-Parameters.legs n-1) x

theorem actual_boundary_fraction_eventually (C : ℝ) (hC : 1≤C) :
    ∀ᶠ n in atTop,0<actualBoundaryFraction C n ∧ actualBoundaryFraction C n≤40/(n : ℝ)^38 := by
  filter_upwards [actual_boundary_profiles_eventually C hC,body_support_scales_eventually C hC,
    eventually_ge_atTop 2] with n hu hs hn
  have hx : (0 : ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hq : (0 : ℝ)<Parameters.modulus n := Nat.cast_pos.mpr (Parameters.modulus_prime n).pos
  have hmargin := safeMargin_quarter n
  have hcard := boundaryPalette_card (Parameters.modulus n) (boundaryHalf C n) hs.2.2.1
    (by have hh := hs.2.2.2; omega)
  have hsize : ((boundaryPalette (Parameters.modulus n) (boundaryHalf C n)).card : ℝ)≤40*(n : ℝ)^2 := by
    have hh : ((boundaryPalette (Parameters.modulus n) (boundaryHalf C n)).card : ℝ)=2*boundaryHalf C n := by exact_mod_cast hcard
    rw [hh]
    have hh' : (boundaryHalf C n : ℝ)≤20*(n : ℝ)^2 := by
      have hi : boundaryHalf C n≤20*(n : ℤ)^2 := by simpa [Parameters.safeMargin,Parameters.security_eq n hn] using hs.2.2.2
      exact_mod_cast hi
    linarith
  have hqlo : (n : ℝ)^40≤Parameters.modulus n := by exact_mod_cast
    (by simpa only [Parameters.security_eq n hn] using (Parameters.modulus_bounds n).1)
  constructor
  · exact div_pos (by exact_mod_cast hu.1.card_pos) hq
  · change _/(Parameters.modulus n : ℝ)≤_
    calc
      _ ≤ (40*(n : ℝ)^2)/(n : ℝ)^40 := div_le_div₀ (by positivity) hsize (by positivity) hqlo
      _ = _ := by field_simp

theorem actual_beta_cutoff_eventually (C : ℝ) (hC : 1≤C) :
    ∀ᶠ n in atTop,0<actualBetaCutoff C n ∧ actualBoundaryFraction C n≤actualBetaCutoff C n ∧
      actualBetaCutoff C n≤40/(n : ℝ)^33 ∧ actualBetaCutoff C n<1 := by
  filter_upwards [actual_boundary_fraction_eventually C hC,v7Activation_lower_eventually C hC,
    eventually_ge_atTop 41] with n hb ha hn
  have hx : (0 : ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hx1 : (1 : ℝ)≤n := by exact_mod_cast (by omega : 1≤n)
  have hr : 0<v7Activation C n := activation_positive _ _ _ _ (legFeatureCount_positive C n hC (by omega))
  have hr1 : v7Activation C n≤1 := (activation_le_one_hundredth _ _ _ _).trans (by norm_num)
  have hc : actualBetaCutoff C n≤40/(n : ℝ)^33 := by
    unfold actualBetaCutoff
    calc
      _ ≤ (40/(n : ℝ)^38)/((n : ℝ)^5)⁻¹ := div_le_div₀ (by positivity) hb.2 (by positivity) ha
      _ = _ := by field_simp
  refine ⟨div_pos hb.1 hr,?_,hc,?_⟩
  · unfold actualBetaCutoff
    exact le_div_self hb.1.le hr hr1
  · apply hc.trans_lt
    apply (div_lt_one (by positivity : (0 : ℝ)<(n : ℝ)^33)).mpr
    have hlarge : (40 : ℝ)<n := by exact_mod_cast (by omega : 40<n)
    exact hlarge.trans_le (by simpa only [pow_one] using pow_le_pow_right₀ hx1 (by omega : 1≤33))

theorem actual_beta_normalized_cutoff_eventually (C : ℝ) (hC : 1≤C) :
    ∀ᶠ n in atTop,Real.exp 1*(Parameters.dimension n : ℝ)*actualBetaCutoff C n/(Parameters.legs n+1 : ℕ)≤1/(n : ℝ) := by
  filter_upwards [actual_beta_cutoff_eventually C hC,eventually_ge_atTop (max 2 ⌈80*Real.exp 1⌉₊)] with n hc hn
  have hn2 : 2≤n := (le_max_left _ _).trans hn
  have hx : (0 : ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hx1 : (1 : ℝ)≤n := by exact_mod_cast (by omega : 1≤n)
  have hN : (Parameters.dimension n : ℝ)≤2*(n : ℝ)^60 := by exact_mod_cast
    (by simpa only [Parameters.security_eq n hn2] using (Parameters.dimension_bounds n).2)
  have hm : (n : ℝ)^30≤(Parameters.legs n+1 : ℕ) := by
    simp only [Parameters.legs,Parameters.security_eq n hn2,Nat.cast_add,Nat.cast_pow,Nat.cast_one]
    linarith
  have hconstant : 80*Real.exp 1≤(n : ℝ)^2 := by
    apply (Nat.le_ceil (80*Real.exp 1)).trans
    apply (show (⌈80*Real.exp 1⌉₊ : ℝ)≤n by exact_mod_cast ((le_max_right _ _).trans hn)).trans
    simpa only [pow_one] using pow_le_pow_right₀ hx1 (by omega : 1≤2)
  calc
    _ ≤ (Real.exp 1*(2*(n : ℝ)^60)*(40/(n : ℝ)^33))/(n : ℝ)^30 :=
      div_le_div₀ (by positivity) (mul_le_mul (mul_le_mul_of_nonneg_left hN (by positivity)) hc.2.2.1 hc.1.le (by positivity)) (by positivity) hm
    _ = 80*Real.exp 1/(n : ℝ)^3 := by field_simp; ring
    _ ≤ (n : ℝ)^2/(n : ℝ)^3 := div_le_div_of_nonneg_right hconstant (by positivity)
    _ = _ := by field_simp

theorem actual_beta_rejected_mass_negligible (C : ℝ) (hC : 1≤C) :
    Negligible (actualBetaRejectedMass C) := by
  have hp : ∀ᶠ n : ℕ in atTop,n≤Parameters.legs n+1 := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hh : n≤n^30 := by simpa only [pow_one] using pow_le_pow_right₀ (by omega : 1≤n) (by omega : 1≤30)
    simpa only [Parameters.legs,Parameters.security_eq n hn] using hh.trans (Nat.le_succ _)
  have hg := negligible_growing_power 0 (fun n : ℕ => 1/(n : ℝ)) (fun n => Parameters.legs n+1)
    (Eventually.of_forall fun n => by positivity) (Eventually.of_forall fun _ => le_rfl) hp
  apply hg.of_eventually_le
  filter_upwards [actual_beta_cutoff_eventually C hC,actual_beta_normalized_cutoff_eventually C hC,
    eventually_ge_atTop 2] with n hc hn hn2
  have hpop : Parameters.legs n+(Parameters.dimension n-Parameters.legs n-1)+1=Parameters.dimension n := by
    have hh := Parameters.population_identity n
    have hb := Parameters.bodies_positive n
    omega
  have hnonneg : 0≤actualBetaRejectedMass C n := by
    apply intervalIntegral.integral_nonneg hc.1.le
    intro x hx
    have hx0 : 0≤x := hx.1
    unfold BetaReference.density
    exact mul_nonneg (by positivity) (pow_nonneg (by linarith [hx.2,hc.2.2.2]) _)
  rw [abs_of_nonneg hnonneg,abs_of_nonneg (by positivity),pow_zero,one_mul]
  apply BetaReference.lower_tail_le_geometric _ _ _ _ hc.1.le hc.2.2.2.le
  simpa only [hpop] using hn

end
end AFT.V7Calibration
