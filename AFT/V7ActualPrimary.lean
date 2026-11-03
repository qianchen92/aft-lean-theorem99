import AFT.BodyBlurParameters
import AFT.ReflectionCalibration

/-! # The calibrated primary and inverse for the actual V7 source laws -/

namespace AFT.GaussianSource

open Filter
open scoped BigOperators Classical Topology

noncomputable section

def actualPrimary (cutoffScale beta : ℝ) (parameter : ℕ) : Fin (Parameters.modulus parameter) → ℝ :=
  V7Calibration.primary parameter cutoffScale beta (boundaryHalf cutoffScale parameter)
    (bodyShift cutoffScale parameter) (bodyBlur cutoffScale parameter)
    (startsPlus cutoffScale parameter) (startsMinus cutoffScale parameter)
    (pairSourceShift cutoffScale parameter) (pairSourceLaw cutoffScale parameter)

/-- Unattached compensators receive the root error and no leg or queue error. -/
def compensatorRootShift (cutoffScale : ℝ) (parameter : ℕ)
    (sample : pairSample cutoffScale parameter) : ℤ := sample.1.1

def actualResponse (cutoffScale : ℝ) (parameter : ℕ) :
    Module.End ℝ (Fin (Parameters.modulus parameter) → ℝ) :=
  V7Calibration.responseOperator parameter cutoffScale (boundaryHalf cutoffScale parameter)
    (startsPlus cutoffScale parameter) (startsMinus cutoffScale parameter)
    (pairSourceShift cutoffScale parameter) (pairSourceLaw cutoffScale parameter)
    (fun sample => bodyShift cutoffScale parameter sample.1)
    (compensatorRootShift cutoffScale parameter) (pairSourceLaw cutoffScale parameter)

def pairReverse (cutoffScale : ℝ) (parameter : ℕ) :
    pairSample cutoffScale parameter ≃ pairSample cutoffScale parameter :=
  (bodyReverse cutoffScale parameter).prodCongr (windowNegateEquiv (legCutoff cutoffScale parameter - 1))

theorem pairReverse_apply (cutoffScale : ℝ) (parameter : ℕ) (sample : pairSample cutoffScale parameter) :
    pairReverse cutoffScale parameter sample =
      (bodyReverse cutoffScale parameter sample.1, windowNegateEquiv (legCutoff cutoffScale parameter - 1) sample.2) := rfl

/-- Reflection of the primary is derived from the genuine zero-sum root
and the two independent optional-noise laws. -/
theorem actualPrimary_reflection (cutoffScale beta : ℝ) (parameter : ℕ)
    (color : Fin (Parameters.modulus parameter)) :
    actualPrimary cutoffScale beta parameter color.rev = actualPrimary cutoffScale beta parameter color := by
  apply V7Calibration.primary_reflection
  intro color
  apply V7Calibration.basePrimary_reflection _ _ _ _ _ _ _ _ _
    (bodyReverse cutoffScale parameter) (pairReverse cutoffScale parameter)
  · exact bodyBlur_reflection cutoffScale parameter
  · exact bodyShift_reverse cutoffScale parameter
  · intro sample
    simp only [pairSourceLaw, FiniteDist.prod_weight, pairReverse_apply,
      bodyBlur_reflection, windowGaussian_reflection]
  · intro sample
    simp only [pairSourceShift, pairReverse_apply, windowNegateEquiv_val]
  · intro sample
    simp only [startsPlus, startsMinus, pairReverse_apply, bodyShift_reverse, TrimmedSlice.reflectedStart]
    ring
  · intro sample
    simp only [startsPlus, startsMinus, pairReverse_apply, bodyShift_reverse, TrimmedSlice.reflectedStart]
    ring
  · have hh := Parameters.safeSize_positive parameter
    unfold Parameters.safeSize at hh
    omega

/-- The primary-driven sign mixture is exactly fair for the actual law. -/
theorem actualPrimary_sign_fair (cutoffScale beta : ℝ) (parameter : ℕ) :
    (∑ color, actualPrimary cutoffScale beta parameter color *
      V7Calibration.paletteSign (Parameters.modulus parameter) color) = 0 :=
  V7Calibration.paletteSign_mean_zero _ _ (actualPrimary_reflection cutoffScale beta parameter)

theorem actual_shift_bound_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) :
    ∀ᶠ parameter : ℕ in atTop, ∀ sample : pairSample cutoffScale parameter,
      ((bodyShift cutoffScale parameter sample.1 - compensatorRootShift cutoffScale parameter sample).natAbs : ℝ) ≤
        6 * (Parameters.security parameter : ℝ) ^ 2 := by
  filter_upwards [legCutoff_le_square_eventually cutoffScale hscale, eventually_ge_atTop 2]
    with parameter hl hp
  intro sample
  have he := (abs_add_le (optionalShift sample.1.2.1) (optionalShift sample.1.2.2)).trans
    (add_le_add (optionalShift_abs_le sample.1.2.1) (optionalShift_abs_le sample.1.2.2))
  have hd : bodyShift cutoffScale parameter sample.1 - compensatorRootShift cutoffScale parameter sample =
      optionalShift sample.1.2.1 + optionalShift sample.1.2.2 := by
    simp only [bodyShift, compensatorRootShift, extraShift]
    ring
  have hab : |bodyShift cutoffScale parameter sample.1 - compensatorRootShift cutoffScale parameter sample| ≤
      (6 * parameter ^ 2 : ℕ) := by
    rw [hd]
    refine he.trans ?_
    have hsum : legCutoff cutoffScale parameter - 1 + queueCutoff parameter ≤ 6 * parameter ^ 2 := by
      unfold queueCutoff
      omega
    exact_mod_cast hsum
  have hh : (bodyShift cutoffScale parameter sample.1 - compensatorRootShift cutoffScale parameter sample).natAbs ≤ 6 * parameter ^ 2 := by
    exact_mod_cast (show ((bodyShift cutoffScale parameter sample.1 - compensatorRootShift cutoffScale parameter sample).natAbs : ℤ) ≤ (6 * parameter ^ 2 : ℕ) by
      simpa only [Int.natCast_natAbs] using hab)
  simpa only [Parameters.security_eq parameter hp, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using
    (show ((bodyShift cutoffScale parameter sample.1 - compensatorRootShift cutoffScale parameter sample).natAbs : ℝ) ≤
      (6 * parameter ^ 2 : ℕ) by exact_mod_cast hh)

/-- For the actual V7 distributions all source and anchor hypotheses are
discharged. Only the retained pool and typical beta count remain. -/
theorem actual_response_inverse_fibers_eventually
    (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ parameter : ℕ in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter ∧
      Parameters.legs parameter ≤ 2 * pool parameter) :
    ∀ᶠ parameter in atTop,
      ∃ operator : (Fin (Parameters.modulus parameter) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus parameter) → ℝ),
        operator.toLinearMap = actualResponse cutoffScale parameter ∧
        (∀ target, primaryActivity (1 / Real.sqrt (pool parameter : ℝ)) (actualPrimary cutoffScale (beta parameter) parameter)
          (operator.symm target) ≤
          2 * primaryActivity (1 / Real.sqrt (pool parameter : ℝ)) (actualPrimary cutoffScale (beta parameter) parameter) target) ∧
        (∀ (κ : Type*) [Fintype κ], ∀ (remaining : κ → ℝ) (kernel : Fin (Parameters.modulus parameter) → κ → ℝ),
          (∀ rest, 0 ≤ remaining rest) →
          coordinateActivity (1 / Real.sqrt (pool parameter : ℝ)) (actualPrimary cutoffScale (beta parameter) parameter) remaining
            (partialProfileOperator operator.symm.toLinearMap (actualPrimary cutoffScale (beta parameter) parameter) kernel) ≤
            2 * coordinateActivity (1 / Real.sqrt (pool parameter : ℝ)) (actualPrimary cutoffScale (beta parameter) parameter) remaining kernel) := by
  apply V7Calibration.response_inverse_fibers_eventually cutoffScale 6 hscale (by norm_num)
    beta (boundaryHalf cutoffScale) pool (bodyShift cutoffScale) (bodyBlur cutoffScale)
    (startsPlus cutoffScale) (startsMinus cutoffScale) (pairSourceShift cutoffScale) (pairSourceLaw cutoffScale)
    (fun parameter sample => bodyShift cutoffScale parameter sample.1) (compensatorRootShift cutoffScale) (pairSourceLaw cutoffScale)
  filter_upwards [actual_physical_supports_eventually cutoffScale hscale,
    actual_shift_bound_eventually cutoffScale hscale, htypical] with parameter hs hd ht
  exact ⟨⟨hs.1, hs.2, ht.1, ht.2.1⟩, ht.2.2, hd⟩

/-- Fixed-alphabet specialization of the actual uniform finite-fiber inverse. -/
theorem actual_response_inverse_eventually {κ : Type*} [Fintype κ]
    (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ parameter : ℕ in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter ∧
      Parameters.legs parameter ≤ 2 * pool parameter) :
    ∀ᶠ parameter in atTop,
      ∃ operator : (Fin (Parameters.modulus parameter) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus parameter) → ℝ),
        operator.toLinearMap = actualResponse cutoffScale parameter ∧
        (∀ target, primaryActivity (1 / Real.sqrt (pool parameter : ℝ)) (actualPrimary cutoffScale (beta parameter) parameter)
          (operator.symm target) ≤
          2 * primaryActivity (1 / Real.sqrt (pool parameter : ℝ)) (actualPrimary cutoffScale (beta parameter) parameter) target) ∧
        (∀ (remaining : κ → ℝ) (kernel : Fin (Parameters.modulus parameter) → κ → ℝ),
          (∀ rest, 0 ≤ remaining rest) →
          coordinateActivity (1 / Real.sqrt (pool parameter : ℝ)) (actualPrimary cutoffScale (beta parameter) parameter) remaining
            (partialProfileOperator operator.symm.toLinearMap (actualPrimary cutoffScale (beta parameter) parameter) kernel) ≤
            2 * coordinateActivity (1 / Real.sqrt (pool parameter : ℝ)) (actualPrimary cutoffScale (beta parameter) parameter) remaining kernel) := by
  apply V7Calibration.response_inverse_eventually cutoffScale 6 hscale (by norm_num)
    beta (boundaryHalf cutoffScale) pool (bodyShift cutoffScale) (bodyBlur cutoffScale)
    (startsPlus cutoffScale) (startsMinus cutoffScale) (pairSourceShift cutoffScale) (pairSourceLaw cutoffScale)
    (fun parameter sample => bodyShift cutoffScale parameter sample.1) (compensatorRootShift cutoffScale) (pairSourceLaw cutoffScale)
  filter_upwards [actual_physical_supports_eventually cutoffScale hscale,
    actual_shift_bound_eventually cutoffScale hscale, htypical] with parameter hs hd ht
  exact ⟨⟨hs.1, hs.2, ht.1, ht.2.1⟩, ht.2.2, hd⟩

end
end AFT.GaussianSource
