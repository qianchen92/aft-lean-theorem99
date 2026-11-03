import AFT.ActualTableEnvelope
import AFT.ActualChargeTransfer
import AFT.RootErrorAlgebra

/-! # Negligible charge errors after the actual fixed-order rejection envelope -/

namespace AFT
open Filter
open scoped Topology

theorem Negligible.mul_envelope_power {error envelope : ℕ → ℝ} (herror : Negligible error)
    (constant : ℝ) (hconstant : 0 ≤ constant) (degree power : ℕ)
    (henvelope : ∀ᶠ n in atTop, |envelope n| ≤ constant * (n : ℝ)^degree) :
    Negligible (fun n => error n * envelope n^power) := by
  apply ((herror.mul_polynomial (degree * power)).const_mul (constant^power)).of_eventually_le
  filter_upwards [henvelope] with n he
  rw [abs_mul, abs_pow]
  calc
    _ ≤ |error n| * (constant * (n : ℝ)^degree)^power :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) he power) (abs_nonneg _)
    _ = |constant^power * ((n : ℝ)^(degree * power) * error n)| := by
      simp only [abs_mul, abs_pow, abs_of_nonneg hconstant,
        abs_of_nonneg (show (0 : ℝ) ≤ n from Nat.cast_nonneg n), mul_pow, ← pow_mul]
      ring

end AFT

namespace AFT.V7Calibration
open GaussianSource RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section

theorem actual_table_charge_envelope_negligible (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n)
    (primaryPool bodyPool : ℕ → ℕ)
    (hcaps : ∀ᶠ n in atTop, primaryPool n ≤ Parameters.legs n ∧ bodyPool n ≤ Parameters.bodies n)
    (table : (n : ℕ) → Table (InputSeed (Fin (Parameters.modulus n))))
    (order cutoff power : ℕ) (bound : ℝ) (hbound : 0 ≤ bound)
    (hactivity : ∀ᶠ n in atTop, activity
      (inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
        (primaryPool n) (bodyPool n) ((n : ℝ)^2)) (table n) ≤ bound) :
    Negligible (fun n => actualChargeError C n (beta n) cutoff *
      tableInputEnvelope (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
        (primaryPool n) (bodyPool n) ((n : ℝ)^2) (table n) order ^ power) := by
  apply (actual_charge_error_negligible C hC beta hbeta cutoff).mul_envelope_power
    ((2 : ℝ)^(2 * order) * bound) (by positivity) (120 * order) power
  filter_upwards [hcaps, hactivity, eventually_ge_atTop 2] with n hc ha hn
  rw [abs_of_nonneg (show 0 ≤ tableInputEnvelope (actualPrimaryLaw C n (beta n))
    (actualBodyLaw C n (beta n)) (primaryPool n) (bodyPool n) ((n : ℝ)^2) (table n) order from
      mul_nonneg (by positivity) (activity_nonneg _ (fun seed => inputWeight_nonneg _ _ _ _ _ seed (sq_nonneg _)) _))]
  apply (actual_table_envelope_power_bound C n (beta n) hn (primaryPool n) (bodyPool n) hc.1 hc.2 (table n) order).trans
  exact (mul_le_mul_of_nonneg_left ha (by positivity)).trans_eq (by ring)

end
end AFT.V7Calibration
