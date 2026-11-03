import AFT.RepresentedLocalSum

/-! # The actual finite control envelope is an explicit security polynomial -/
namespace AFT.V7Calibration
open GaussianSource RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section

/-- The true V7 population sizes turn the retained-pool envelope into a
fixed polynomial; the degree depends only on the actual input cutoff. -/
theorem actual_table_envelope_power_bound (C : ℝ) (parameter : ℕ) (beta : ℝ)
    (hp : 2 ≤ parameter) (primaryPool bodyPool : ℕ)
    (hprimary : primaryPool ≤ Parameters.legs parameter) (hbody : bodyPool ≤ Parameters.bodies parameter)
    (table : Table (InputSeed (Fin (Parameters.modulus parameter)))) (order : ℕ) :
    tableInputEnvelope (actualPrimaryLaw C parameter beta) (actualBodyLaw C parameter beta)
      primaryPool bodyPool ((parameter : ℝ)^2) table order ≤
      (2 : ℝ)^(2 * order) * (parameter : ℝ)^(120 * order) *
        activity (inputWeight (actualPrimaryLaw C parameter beta) (actualBodyLaw C parameter beta)
          primaryPool bodyPool ((parameter : ℝ)^2)) table := by
  have hd : Parameters.dimension parameter ≤ 2 * parameter^60 := by
    simpa only [Parameters.security_eq parameter hp] using (Parameters.dimension_bounds parameter).2
  have hm : Parameters.legs parameter ≤ Parameters.dimension parameter := by
    have hh := Parameters.four_legs_le_dimension parameter
    omega
  have hb : Parameters.bodies parameter ≤ Parameters.dimension parameter := Nat.sub_le _ _
  have hmax : max (primaryPool : ℝ) (bodyPool : ℝ) ≤ 2 * (parameter : ℝ)^60 := by
    apply max_le
    · exact_mod_cast hprimary.trans (hm.trans hd)
    · exact_mod_cast hbody.trans (hb.trans hd)
  unfold tableInputEnvelope
  apply mul_le_mul_of_nonneg_right _ (activity_nonneg _ (fun seed => inputWeight_nonneg _ _ _ _ _ seed (sq_nonneg _)) _)
  calc
    _ ≤ (2 * (parameter : ℝ)^60)^(2 * order) := pow_le_pow_left₀ (by positivity) hmax _
    _ = _ := by
      rw [mul_pow, ← pow_mul]
      congr 1
      congr 1
      omega

end
end AFT.V7Calibration
