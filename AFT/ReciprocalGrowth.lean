import AFT.LocalQuotientAlgebra

/-! # Finite positive-factor reciprocals close to the literal unit -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
variable {Seed : Type*}

theorem activity_le_one_add_of_sub_one (weight : Seed → ℝ) (hw : ∀ seed,0 ≤ weight seed)
    (factor : Table Seed) (delta : ℝ) (herror : activity weight (factor-1) ≤ delta) :
    activity weight factor ≤ 1+delta := by
  have hh := activity_add_le weight hw (factor-1) 1
  rw [sub_add_cancel,activity_one] at hh
  linarith

theorem activity_pow_sub_one_le (weight : Seed → ℝ) (hw : ∀ seed,0 ≤ weight seed)
    (factor : Table Seed) (delta : ℝ) (hdelta : 0 ≤ delta)
    (herror : activity weight (factor-1) ≤ delta) (power : ℕ) :
    activity weight (factor^power-1) ≤ (1+delta)^power-1 := by
  have hf := activity_le_one_add_of_sub_one weight hw factor delta herror
  induction power with
  | zero => simp
  | succ power ih =>
    have he : factor^(power+1)-1=(factor^power-1)*factor+(factor-1) := by ring
    rw [he]
    apply (activity_add_le weight hw _ _).trans
    have hp : activity weight ((factor^power-1)*factor) ≤ ((1+delta)^power-1)*(1+delta) := by
      apply (activity_mul_le weight hw _ _).trans
      exact mul_le_mul ih hf (activity_nonneg weight hw factor)
        (sub_nonneg.mpr (one_le_pow₀ (by linarith)))
    exact (add_le_add hp herror).trans_eq (by rw [pow_succ]; ring)

/-- Multiply an already controlled literal correction by an actual reciprocal.
The identity term is preserved exactly before taking coefficient absolute values. -/
theorem activity_mul_perturbation_le (weight : Seed → ℝ) (hw : ∀ seed,0 ≤ weight seed)
    (base value factor : Table Seed) (mass growth factorGrowth : ℝ)
    (hmass : 0 ≤ mass) (hgrowth : 1 ≤ growth)
    (hbase : activity weight base ≤ mass)
    (hvalue : activity weight value ≤ growth*mass)
    (herror : activity weight (value-base) ≤ (growth-1)*mass)
    (hfactor : activity weight factor ≤ factorGrowth)
    (hfactorError : activity weight (factor-1) ≤ factorGrowth-1) :
    activity weight (value*factor) ≤ growth*factorGrowth*mass ∧
    activity weight (value*factor-base) ≤ (growth*factorGrowth-1)*mass := by
  constructor
  · exact (activity_mul_le weight hw _ _).trans
      ((mul_le_mul hvalue hfactor (activity_nonneg weight hw _) (mul_nonneg (by linarith) hmass)).trans_eq (by ring))
  · have he : value*factor-base=(value-base)*factor+base*(factor-1) := by ring
    rw [he]
    apply (activity_add_le weight hw _ _).trans
    have hfirst := (activity_mul_le weight hw (value-base) factor).trans
      (mul_le_mul herror hfactor (activity_nonneg weight hw _) (mul_nonneg (sub_nonneg.mpr hgrowth) hmass))
    have hsecond := (activity_mul_le weight hw base (factor-1)).trans
      (mul_le_mul hbase hfactorError (activity_nonneg weight hw _) hmass)
    exact (add_le_add hfirst hsecond).trans_eq (by ring)

end
end AFT.RepresentedPolynomial
