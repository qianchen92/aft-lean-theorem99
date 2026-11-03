import AFT.ActiveCanonicalInput

/-! # Actual V7 powers for all source-covariance input activities -/

namespace AFT.V7Calibration
open Filter GaussianSource
open scoped BigOperators Classical Topology
noncomputable section

theorem actual_covariance_components_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) :
    ∀ᶠ parameter : ℕ in atTop,
      Real.sqrt (1024*(Parameters.modulus parameter : ℝ)*legCutoff cutoffScale parameter /
        (Parameters.anchorWidth parameter : ℝ)^2) ≤ 64/(parameter : ℝ)^11 ∧
      16*(legCutoff cutoffScale parameter : ℝ)/Parameters.anchorWidth parameter ≤ 16/(parameter : ℝ)^30 ∧
      32*(legCutoff cutoffScale parameter : ℝ)/Parameters.anchorWidth parameter ≤ 32/(parameter : ℝ)^30 ∧
      32*(Parameters.modulus parameter : ℝ)/Parameters.anchorWidth parameter ≤ 64*(parameter : ℝ)^8 ∧
      Real.sqrt (384*(legCutoff cutoffScale parameter : ℝ)/Parameters.modulus parameter) ≤ 20/(parameter : ℝ)^19 ∧
      Real.sqrt (72*(Parameters.modulus parameter : ℝ)/Parameters.anchorWidth parameter) ≤ 12*(parameter : ℝ)^4 ∧
      36*(Parameters.modulus parameter : ℝ)/Parameters.anchorWidth parameter ≤ 72*(parameter : ℝ)^8 := by
  filter_upwards [legCutoff_le_square_eventually cutoffScale hscale, eventually_ge_atTop 2] with parameter hcut hp
  have hp0 : (0 : ℝ) < parameter := by exact_mod_cast (show 0 < parameter by omega)
  have hA : (Parameters.anchorWidth parameter : ℝ) = (parameter : ℝ)^32 := by
    simp only [Parameters.anchorWidth, Parameters.security_eq parameter hp, Nat.cast_pow]
  have hL : (legCutoff cutoffScale parameter : ℝ) ≤ (parameter : ℝ)^2 := by exact_mod_cast hcut
  have hq0 : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hq : (parameter : ℝ)^40 ≤ Parameters.modulus parameter ∧
      (Parameters.modulus parameter : ℝ) ≤ 2*(parameter : ℝ)^40 := by
    exact_mod_cast (show parameter^40 ≤ Parameters.modulus parameter ∧ Parameters.modulus parameter ≤ 2*parameter^40 by
      simpa only [Parameters.security_eq parameter hp] using Parameters.modulus_bounds parameter)
  have hLratio : (legCutoff cutoffScale parameter : ℝ)/Parameters.anchorWidth parameter ≤ 1/(parameter : ℝ)^30 := by
    rw [hA]
    exact (div_le_div_of_nonneg_right hL (by positivity)).trans_eq (by field_simp)
  have hqratio : (Parameters.modulus parameter : ℝ)/Parameters.anchorWidth parameter ≤ 2*(parameter : ℝ)^8 := by
    rw [hA]
    exact (div_le_div_of_nonneg_right hq.2 (by positivity)).trans_eq (by field_simp)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply (Real.sqrt_le_left (by positivity)).mpr
    rw [hA]
    calc
      _ ≤ 1024*(2*(parameter : ℝ)^40)*(parameter : ℝ)^2 / ((parameter : ℝ)^32)^2 := by gcongr; exact hq.2
      _ ≤ (64/(parameter : ℝ)^11)^2 := by field_simp; nlinarith [pow_pos hp0 22]
  · convert mul_le_mul_of_nonneg_left hLratio (by norm_num : (0 : ℝ) ≤ 16) using 1 <;> ring
  · convert mul_le_mul_of_nonneg_left hLratio (by norm_num : (0 : ℝ) ≤ 32) using 1 <;> ring
  · convert mul_le_mul_of_nonneg_left hqratio (by norm_num : (0 : ℝ) ≤ 32) using 1 <;> ring
  · apply (Real.sqrt_le_left (by positivity)).mpr
    calc
      _ ≤ 384*(parameter : ℝ)^2/(parameter : ℝ)^40 := by
        exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hL (by norm_num : (0 : ℝ) ≤ 384)) hq0.le).trans
          (div_le_div_of_nonneg_left (by positivity) (by positivity) hq.1)
      _ ≤ (20/(parameter : ℝ)^19)^2 := by field_simp; nlinarith [pow_pos hp0 40]
  · apply (Real.sqrt_le_left (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_left hqratio (by norm_num : (0 : ℝ) ≤ 72)
    convert hh using 1 <;> ring
  · convert mul_le_mul_of_nonneg_left hqratio (by norm_num : (0 : ℝ) ≤ 36) using 1 <;> ring

theorem inverse_power_antitone {x : ℝ} (hx : 1 ≤ x) {small large : ℕ} (h : small ≤ large) :
    1/x^large ≤ 1/x^small :=
  one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hx h)

theorem covariance_pool_rate (parameter pool : ℕ) (hp : 2 ≤ parameter)
    (hpool : Parameters.legs parameter ≤ 2*pool) :
    0 ≤ (Real.sqrt (pool : ℝ))⁻¹ ∧ (Real.sqrt (pool : ℝ))⁻¹ ≤ 1 ∧
      (Real.sqrt (pool : ℝ))⁻¹ ≤ 2/(parameter : ℝ)^15 := by
  have hh := v7_primary_pool_rate_bound parameter pool hpool
  rw [Parameters.security_eq parameter hp] at hh
  have hx : (1 : ℝ) ≤ parameter := by exact_mod_cast (show 1 ≤ parameter by omega)
  have hpow : (2 : ℝ) ≤ (parameter : ℝ)^15 := by
    have hp' : (2 : ℝ) ≤ parameter := by exact_mod_cast hp
    have hpower := pow_le_pow_right₀ hx (show 1 ≤ 15 by decide)
    simp only [pow_one] at hpower
    exact hp'.trans hpower
  simp only [one_div] at hh
  refine ⟨hh.1.le, hh.2.trans ?_, hh.2⟩
  exact (div_le_one (by positivity)).mpr hpow

/-- Actual finite input budgets at every retained primary-pool rate.
The inverse response cost is kept separate from the physical pool size. -/
theorem actual_covariance_activity_powers_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) :
    ∀ᶠ parameter : ℕ in atTop, ∀ rate : ℝ, 0 ≤ rate → rate ≤ 1 → rate ≤ 2/(parameter : ℝ)^15 →
      inactivePairActivityBound cutoffScale parameter rate ≤ 8192/(parameter : ℝ)^41 ∧
      inactiveBodyActivityBound cutoffScale parameter rate ≤ 104/(parameter : ℝ)^30 ∧
      activePairActivityBound parameter rate ≤ 16384/(parameter : ℝ)^26 := by
  filter_upwards [actual_covariance_components_eventually cutoffScale hscale, eventually_ge_atTop 2]
    with parameter hc hp a ha ha1 haBound
  have hx : (1 : ℝ) ≤ parameter := by exact_mod_cast (show 1 ≤ parameter by omega)
  have hx0 : (0 : ℝ) < parameter := by positivity
  have ha2 : a^2 ≤ 4/(parameter : ℝ)^30 := by
    exact (pow_le_pow_left₀ ha haBound 2).trans_eq (by ring)
  have hF := hc.1
  have hG := hc.2.1
  have hY := hc.2.2.1
  have hV := hc.2.2.2.1
  have hH := hc.2.2.2.2.1
  have hAF := hc.2.2.2.2.2.1
  have hAX := hc.2.2.2.2.2.2
  have hsmall (small large : ℕ) (h : small ≤ large) : 1/(parameter : ℝ)^large ≤ 1/(parameter : ℝ)^small :=
    inverse_power_antitone hx h
  have hI : inactivePairActivityBound cutoffScale parameter a ≤ 8192/(parameter : ℝ)^41 := by
    let F := Real.sqrt (1024*(Parameters.modulus parameter : ℝ)*legCutoff cutoffScale parameter /
      (Parameters.anchorWidth parameter : ℝ)^2)
    let G := 16*(legCutoff cutoffScale parameter : ℝ)/Parameters.anchorWidth parameter
    let Y := 32*(legCutoff cutoffScale parameter : ℝ)/Parameters.anchorWidth parameter
    let V := 32*(Parameters.modulus parameter : ℝ)/Parameters.anchorWidth parameter
    have haF : a*F ≤ 64/(parameter : ℝ)^11 := (mul_le_mul_of_nonneg_right ha1 (by positivity : 0 ≤ F)).trans (by simpa only [one_mul] using hF)
    have haY : a*Y ≤ 32/(parameter : ℝ)^30 := (mul_le_mul_of_nonneg_right ha1 (by positivity : 0 ≤ Y)).trans (by simpa only [one_mul] using hY)
    have haV : a^2*V ≤ 256/(parameter : ℝ)^22 := by
      exact (mul_le_mul ha2 hV (by positivity : 0 ≤ V) (by positivity)).trans_eq (by field_simp; norm_num)
    change a*a*(F+a*F+a*F+a*a*V)+2*a*a*(3+8*a)*(G+a*Y) ≤ _
    calc
      _ ≤ (4/(parameter : ℝ)^30)*(64/(parameter : ℝ)^11+64/(parameter : ℝ)^11+
          64/(parameter : ℝ)^11+256/(parameter : ℝ)^22)+
          2*(4/(parameter : ℝ)^30)*11*(16/(parameter : ℝ)^30+32/(parameter : ℝ)^30) := by
        have haa : a*a ≤ 4/(parameter : ℝ)^30 := by simpa only [sq] using ha2
        have haaV : a*a*V ≤ 256/(parameter : ℝ)^22 := by simpa only [sq] using haV
        have hone : 3+8*a ≤ 11 := by linarith
        calc
          _ = (a*a)*(F+a*F+a*F+a*a*V)+2*(a*a)*(3+8*a)*(G+a*Y) := by ring
          _ ≤ _ := by gcongr
      _ = 768/(parameter : ℝ)^41+1024/(parameter : ℝ)^52+4224/(parameter : ℝ)^60 := by field_simp; ring
      _ ≤ 8192/(parameter : ℝ)^41 := by
        have h52 := hsmall 41 52 (by decide)
        have h60 := hsmall 41 60 (by decide)
        simp only [div_eq_mul_inv, one_mul] at h52 h60 ⊢
        nlinarith [inv_nonneg.mpr (show 0 ≤ (parameter : ℝ)^41 by positivity)]
  have hB : inactiveBodyActivityBound cutoffScale parameter a ≤ 104/(parameter : ℝ)^30 := by
    unfold inactiveBodyActivityBound
    calc
      _ ≤ (2/(parameter : ℝ)^15)*(20/(parameter : ℝ)^19+16*(2/(parameter : ℝ)^15)) := by gcongr
      _ = 40/(parameter : ℝ)^34+64/(parameter : ℝ)^30 := by field_simp; ring
      _ ≤ _ := by
        have hh := hsmall 30 34 (by decide)
        simp only [div_eq_mul_inv, one_mul] at hh ⊢
        linarith
  refine ⟨hI,hB,?_⟩
  let F := Real.sqrt (72*(Parameters.modulus parameter : ℝ)/Parameters.anchorWidth parameter)
  let X := 36*(Parameters.modulus parameter : ℝ)/Parameters.anchorWidth parameter
  have haX : a*X ≤ 144*(parameter : ℝ)^4 := by
    calc
      _ ≤ (2/(parameter : ℝ)^15)*(72*(parameter : ℝ)^8) := mul_le_mul haBound hAX (by positivity) (by positivity)
      _ = 144/(parameter : ℝ)^7 := by field_simp; norm_num
      _ ≤ 144 := by
        have hh := hsmall 0 7 (by decide)
        norm_num at hh
        simpa only [mul_one, mul_div_assoc] using mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 144)
      _ ≤ _ := by nlinarith [one_le_pow₀ hx (n := 4)]
  have ha2X : a*a*X ≤ 144*(parameter : ℝ)^4 := by
    have hh := mul_le_mul_of_nonneg_left ha1 (show 0 ≤ a*X by positivity)
    have hh' : a*a*X ≤ a*X := by nlinarith
    exact hh'.trans haX
  change a*a*(F+a*X+a*X+a*a*X)+2*a*a*(3+8*a)*(F+a*X) ≤ _
  calc
    _ ≤ (4/(parameter : ℝ)^30)*(12*(parameter : ℝ)^4+144*(parameter : ℝ)^4+
        144*(parameter : ℝ)^4+144*(parameter : ℝ)^4)+
        2*(4/(parameter : ℝ)^30)*11*(12*(parameter : ℝ)^4+144*(parameter : ℝ)^4) := by
      have haa : a*a ≤ 4/(parameter : ℝ)^30 := by simpa only [sq] using ha2
      have hone : 3+8*a ≤ 11 := by linarith
      calc
        _ = (a*a)*(F+a*X+a*X+a*a*X)+2*(a*a)*(3+8*a)*(F+a*X) := by ring
        _ ≤ _ := by gcongr
    _ = 15504/(parameter : ℝ)^26 := by field_simp; ring
    _ ≤ _ := by gcongr; norm_num

def inactiveQuadraticActivityBound (cutoffScale : ℝ) (parameter : ℕ) (rate : ℝ) : ℝ :=
  rate * (16*(legCutoff cutoffScale parameter : ℝ)/Parameters.anchorWidth parameter +
    rate*(32*(legCutoff cutoffScale parameter : ℝ)/Parameters.anchorWidth parameter)) *
      inactiveBodyActivityBound cutoffScale parameter rate

def activeQuadraticActivityBound (cutoffScale : ℝ) (parameter : ℕ) (rate : ℝ) : ℝ :=
  rate * (Real.sqrt (72*(Parameters.modulus parameter : ℝ)/Parameters.anchorWidth parameter) +
    rate*(36*(Parameters.modulus parameter : ℝ)/Parameters.anchorWidth parameter)) *
      inactiveBodyActivityBound cutoffScale parameter rate

theorem actual_quadratic_covariance_powers_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) :
    ∀ᶠ parameter : ℕ in atTop, ∀ rate : ℝ, 0 ≤ rate → rate ≤ 1 → rate ≤ 2/(parameter : ℝ)^15 →
      inactiveQuadraticActivityBound cutoffScale parameter rate ≤ 9984/(parameter : ℝ)^75 ∧
      activeQuadraticActivityBound cutoffScale parameter rate ≤ 17472/(parameter : ℝ)^37 := by
  filter_upwards [actual_covariance_components_eventually cutoffScale hscale,
    actual_covariance_activity_powers_eventually cutoffScale hscale, eventually_ge_atTop 2]
    with parameter hc hbud hp a ha ha1 haBound
  have hx : (1 : ℝ) ≤ parameter := by exact_mod_cast (show 1 ≤ parameter by omega)
  have hx0 : (0 : ℝ) < parameter := by positivity
  have hbody := (hbud a ha ha1 haBound).2.1
  have hbody0 : 0 ≤ inactiveBodyActivityBound cutoffScale parameter a := by
    unfold inactiveBodyActivityBound
    positivity
  have hY : a*(32*(legCutoff cutoffScale parameter : ℝ)/Parameters.anchorWidth parameter) ≤ 32/(parameter : ℝ)^30 := by
    exact (mul_le_mul_of_nonneg_right ha1 (by positivity)).trans (by simpa only [one_mul] using hc.2.2.1)
  constructor
  · unfold inactiveQuadraticActivityBound
    calc
      _ ≤ (2/(parameter : ℝ)^15)*(16/(parameter : ℝ)^30+32/(parameter : ℝ)^30)*(104/(parameter : ℝ)^30) := by
        exact mul_le_mul (mul_le_mul haBound (add_le_add hc.2.1 hY) (by positivity) (by positivity))
          hbody hbody0 (by positivity)
      _ = _ := by field_simp; norm_num
  · have hX : a*(36*(Parameters.modulus parameter : ℝ)/Parameters.anchorWidth parameter) ≤ 72*(parameter : ℝ)^8 := by
      exact (mul_le_mul_of_nonneg_right ha1 (by positivity)).trans (by simpa only [one_mul] using hc.2.2.2.2.2.2)
    have hF : Real.sqrt (72*(Parameters.modulus parameter : ℝ)/Parameters.anchorWidth parameter) ≤ 12*(parameter : ℝ)^8 := by
      exact hc.2.2.2.2.2.1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (show 4 ≤ 8 by decide)) (by norm_num))
    unfold activeQuadraticActivityBound
    calc
      _ ≤ (2/(parameter : ℝ)^15)*(12*(parameter : ℝ)^8+72*(parameter : ℝ)^8)*(104/(parameter : ℝ)^30) := by gcongr
      _ = _ := by field_simp; norm_num

end
end AFT.V7Calibration
