import AFT.MarkedActivity
import AFT.RepresentedCovariance
import AFT.V7BodyPairActivity

/-! # Actual aggregate marked-pair input costs at the retained pool sizes -/

namespace AFT.V7Calibration
open GaussianSource Filter RepresentedPolynomial
open scoped BigOperators Classical Topology
noncomputable section

def markedAggregateConstant (cutoffScale : ℝ) : ℝ :=
  32*Real.sqrt (markedPairSquareConstant cutoffScale)+4608

/-- The actual marking probability cancels the primary inverse factor
before the sum over all physical legs is estimated. -/
theorem actual_marked_total_activity_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ)/(2*Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2*(Parameters.legs parameter : ℝ)/Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      ∀ primary body : FiniteDist (Fin (Parameters.modulus parameter)),
      primary.weight = actualPrimary cutoffScale parameter (beta parameter) →
      body.weight = actualBodyCenter cutoffScale parameter (beta parameter) →
      ∀ primaryPool bodyPool : ℕ, Parameters.legs parameter ≤ 2*primaryPool →
      Parameters.bodies parameter ≤ 2*bodyPool →
      (Parameters.legs parameter : ℝ)*v7Activation cutoffScale parameter *
        responseInputWeight primary body primaryPool bodyPool ((parameter : ℝ)^2)
          (4/v7Activation cutoffScale parameter) (actualMarkedInput cutoffScale parameter (beta parameter)) ≤
            markedAggregateConstant cutoffScale/(parameter : ℝ)^9 := by
  filter_upwards [actual_marked_input_activity_eventually cutoffScale hscale beta hbeta,
    eventually_ge_atTop 2] with parameter hmarked hp primary body hprimary hbody pool bpool hpool hbpool
  let a := (Real.sqrt (pool : ℝ))⁻¹
  let b := (Real.sqrt (bpool : ℝ))⁻¹
  let K := Real.sqrt (markedPairSquareConstant cutoffScale)
  have ha := covariance_pool_rate parameter pool hp hpool
  have hb := body_pair_pool_rate parameter bpool hp hbpool
  have hx : (1 : ℝ) ≤ parameter := by exact_mod_cast (show 1 ≤ parameter by omega)
  have hx0 : (0 : ℝ) < parameter := by positivity
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  have hF : a*(K*(parameter : ℝ)^4) ≤ K*(parameter : ℝ)^4 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ha.2.1 (show 0 ≤ K*(parameter : ℝ)^4 by positivity)
  have hH : b*(72*(parameter : ℝ)^8) ≤ 144*(parameter : ℝ)^4 := by
    calc
      _ ≤ (2/(parameter : ℝ)^30)*(72*(parameter : ℝ)^8) := mul_le_mul_of_nonneg_right hb.2.2 (by positivity)
      _ = 144/(parameter : ℝ)^22 := by field_simp; norm_num
      _ ≤ 144 := by
        have hh := inverse_power_antitone hx (show 0 ≤ 22 by decide)
        norm_num at hh
        simpa only [mul_one,mul_div_assoc] using mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 144)
      _ ≤ _ := by nlinarith [one_le_pow₀ hx (n := 4)]
  have hAH : a*b*(72*(parameter : ℝ)^8) ≤ 144*(parameter : ℝ)^4 := by
    calc
      _ = a*(b*(72*(parameter : ℝ)^8)) := by ring
      _ ≤ a*(144*(parameter : ℝ)^4) := mul_le_mul_of_nonneg_left hH ha.1
      _ ≤ 1*(144*(parameter : ℝ)^4) := mul_le_mul_of_nonneg_right ha.2.1 (by positivity)
      _ = _ := by ring
  have hbracket : K*(parameter : ℝ)^4+a*(K*(parameter : ℝ)^4)+b*(72*(parameter : ℝ)^8)+a*b*(72*(parameter : ℝ)^8) ≤
      (2*K+288)*(parameter : ℝ)^4 := by linarith
  have hraw := hmarked primary body hprimary hbody pool bpool ((parameter : ℝ)^2) (by positivity)
  have hinput : inputWeight primary body pool bpool ((parameter : ℝ)^2)
      (actualMarkedInput cutoffScale parameter (beta parameter)) ≤ (8*K+1152)/(parameter : ℝ)^39 := by
    apply hraw.trans
    change (parameter : ℝ)^2*a*b*_ ≤ _
    calc
      _ ≤ (parameter : ℝ)^2*(2/(parameter : ℝ)^15)*(2/(parameter : ℝ)^30)*((2*K+288)*(parameter : ℝ)^4) := by
        exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left ha.2.2 (by positivity)) hb.2.2 hb.1 (by positivity))
          hbracket (by positivity) (by positivity)
      _ = _ := by field_simp; ring
  have hrho : 0 < v7Activation cutoffScale parameter := activation_positive _ _ _ _
    (legFeatureCount_positive cutoffScale parameter hscale (by omega))
  have hm : (Parameters.legs parameter : ℝ) = (parameter : ℝ)^30 := by
    simp only [Parameters.legs, Parameters.security_eq parameter hp, Nat.cast_pow]
  change (Parameters.legs parameter : ℝ)*v7Activation cutoffScale parameter *
    ((4/v7Activation cutoffScale parameter)^1*inputWeight primary body pool bpool ((parameter : ℝ)^2) _) ≤ _
  rw [pow_one]
  calc
    _ = 4*(Parameters.legs parameter : ℝ)*inputWeight primary body pool bpool ((parameter : ℝ)^2) _ := by field_simp
    _ ≤ 4*(Parameters.legs parameter : ℝ)*((8*K+1152)/(parameter : ℝ)^39) := mul_le_mul_of_nonneg_left hinput (by positivity)
    _ = _ := by rw [hm]; unfold markedAggregateConstant; dsimp only [K]; field_simp; ring

end
end AFT.V7Calibration
