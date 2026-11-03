import CurrentAFT.ActualCalibrationMoments
import CurrentAFT.FixedOrderAccuracy

/-! # Negligible charge-amplified clipping for the same actual weight

The requested decay exponent changes only the moment used to estimate the
loss. The calibration order and the public coefficient family stay fixed.
-/
namespace CurrentAFT.ActualCalibrationClipping
open AFT ActualCompleteStability ActualCalibrationMoments PublicOutputExperiment
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

def loss (security order : ℕ) (horder : 2 ≤ order) (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) : ℝ :=
  (reference security).expectation (fun controls =>
    |actualWeight security order (coefficients security order horder hsecurity layout) controls -
      clip (actualWeight security order (coefficients security order horder hsecurity layout) controls)|)

theorem loss_nonneg (security order : ℕ) (horder : 2 ≤ order) (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    0 ≤ loss security order horder hsecurity layout := by
  unfold loss FiniteDist.expectation
  exact Finset.sum_nonneg (fun controls _ => mul_nonneg ((reference security).nonneg controls) (abs_nonneg _))

theorem charged_loss_negligible (order : ℕ) (horder : 2 ≤ order) (decayOrder : ℕ) :
    ∃ cutoff : ℕ, ∀ security ≥ cutoff, ∀ hsecurity : threshold order horder ≤ security,
      ∀ layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security,
      (Parameters.modulus security : ℝ) * loss security order horder hsecurity layout ≤
        inversePower security decayOrder := by
  let moment := decayOrder + 66
  obtain ⟨constantCutoff, hconstantCutoff⟩ := exists_nat_ge (momentConstant order moment)
  refine ⟨max constantCutoff 131072, ?_⟩
  intro security hlarge hsecurity layout
  have hb : (0 : ℝ) < Parameters.base security := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security from (by have := Parameters.base_ge_two security; omega))
  have hconstant : momentConstant order moment ≤ (Parameters.base security : ℝ) :=
    hconstantCutoff.trans (Nat.cast_le.mpr (by unfold Parameters.base; omega))
  have hlargeBase : (131072 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 131072 ≤ Parameters.base security by unfold Parameters.base; omega)
  have hmodulus : (Parameters.modulus security : ℝ) ≤ (Parameters.base security : ℝ)^65 := by
    have hbound : (Parameters.modulus security : ℝ) ≤ 131072 * (Parameters.base security : ℝ)^64 := by
      exact_mod_cast (Parameters.modulus_bounds security).2
    apply hbound.trans
    calc
      _ ≤ (Parameters.base security : ℝ) * (Parameters.base security : ℝ)^64 :=
        mul_le_mul_of_nonneg_right hlargeBase (pow_nonneg hb.le _)
      _ = _ := by rw [pow_succ]; ring
  have hratio : momentConstant order moment / (Parameters.base security : ℝ)^6 ≤
      1 / (Parameters.base security : ℝ)^5 := by
    calc
      _ ≤ (Parameters.base security : ℝ) / (Parameters.base security : ℝ)^6 :=
        div_le_div_of_nonneg_right hconstant (pow_nonneg hb.le _)
      _ = _ := by rw [show (6 : ℕ) = 5 + 1 by omega, pow_succ]; field_simp
  have hloss := actual_weight_clipping security order horder hsecurity layout moment (by dsimp [moment]; omega)
  have hlossBound : loss security order horder hsecurity layout ≤
      (1 / (Parameters.base security : ℝ)^5)^(2 * moment) :=
    hloss.trans (pow_le_pow_left₀
      (div_nonneg (momentConstant_nonneg order moment) (pow_nonneg hb.le _)) hratio _)
  calc
    _ ≤ (Parameters.base security : ℝ)^65 * (1 / (Parameters.base security : ℝ)^5)^(2 * moment) :=
      mul_le_mul hmodulus hlossBound (loss_nonneg security order horder hsecurity layout) (pow_nonneg hb.le _)
    _ = (Parameters.base security : ℝ)^65 / (Parameters.base security : ℝ)^(5 * (2 * moment)) := by
      rw [div_pow, one_pow, ← pow_mul]
      ring
    _ ≤ inversePower security decayOrder := by
      unfold inversePower
      apply (div_le_div_iff₀ (pow_pos hb _) (pow_pos hb _)).mpr
      rw [← pow_add, one_mul]
      exact pow_le_pow_right₀ hb1 (by dsimp [moment]; omega)

end
end CurrentAFT.ActualCalibrationClipping
