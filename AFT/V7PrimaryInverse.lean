import AFT.V7PrimaryCalibration
import AFT.InverseMixedActivity

/-!
# The actual V7 calibrated inverse on finite mixed fibers
-/

namespace AFT

open Filter
open scoped BigOperators Topology

namespace V7Calibration

/-- V7's public sign: below, at, and above the palette midpoint. -/
def paletteSign (modulus : ℕ) (color : Fin modulus) : ℝ :=
  if 2 * color.val < modulus - 1 then -1 else if modulus - 1 < 2 * color.val then 1 else 0

theorem paletteSign_abs_le (modulus : ℕ) (color : Fin modulus) : |paletteSign modulus color| ≤ 1 := by
  unfold paletteSign
  split_ifs <;> norm_num

/-- Uniform width-W anchors reflected about q-1-c, with a fair direction
at the midpoint. The Boolean is irrelevant off the midpoint. -/
def publicAnchorStart (modulus width : ℕ) (color : Fin modulus) (coin : Bool) : ℤ :=
  if 2 * color.val < modulus - 1 then (modulus : ℤ) - color.val - 2 * width
  else if modulus - 1 < 2 * color.val then (modulus : ℤ) - 1 - color.val + width
  else if coin then (modulus : ℤ) - color.val - 2 * width
    else (modulus : ℤ) - 1 - color.val + width

noncomputable def errorLaw {υ : Type*} [Fintype υ] (noiseLaw : FiniteDist υ) : FiniteDist (υ × Bool) :=
  noiseLaw.prod (FiniteDist.uniform Bool)

noncomputable def errorStarts {υ : Type*} (parameter : ℕ) (sourceShift : υ → ℤ) :
    υ × Bool → Fin (Parameters.modulus parameter) → ℤ :=
  fun noise color => publicAnchorStart (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
    color noise.2 + sourceShift noise.1

def errorShift {υ : Type*} (bodyShift sourceShift : υ → ℤ) : υ × Bool → ℤ :=
  fun noise => bodyShift noise.1 - sourceShift noise.1

/-- This is the actual averaged `(body blur - source shift) anchor` matrix:
each row uses the same noise state in its two translated intervals. -/
noncomputable def anchorError {υ : Type*} [Fintype υ] (parameter : ℕ)
    (bodyShift sourceShift : υ → ℤ) (noiseLaw : FiniteDist υ) :
    Module.End ℝ (Fin (Parameters.modulus parameter) → ℝ) :=
  averagedIntervalTranslationOperator (fun color => (color.val : ℤ))
    (errorStarts parameter sourceShift) (errorShift bodyShift sourceShift)
    (Parameters.anchorWidth parameter) (errorLaw noiseLaw).weight

/-- The calibrated primary response uses the exact rank response and the
actual physical difference of blurred anchor laws. -/
noncomputable def responseOperator {τ υ : Type*} [Fintype τ] [Fintype υ]
    (parameter : ℕ) (cutoffScale : ℝ) (boundary : ℤ)
    (startsPlus startsMinus sources : τ → ℤ) (sourceLaw : FiniteDist τ)
    (bodyShift sourceShift : υ → ℤ) (noiseLaw : FiniteDist υ) :
    Module.End ℝ (Fin (Parameters.modulus parameter) → ℝ) :=
  primaryRankOperator (GaussianSource.v7Activation cutoffScale parameter)
    (signResponse parameter cutoffScale boundary startsPlus startsMinus sources sourceLaw)
    (profileSignMap (paletteSign (Parameters.modulus parameter))) +
    anchorError parameter bodyShift sourceShift noiseLaw

/-- The actual rank and translation constants are eventually at most
4/3 and 1/4. In particular their inverse bound is at most 2. -/
theorem inverse_constants_eventually {palette : ℕ → Type*}
    [∀ parameter, Fintype (palette parameter)]
    (cutoffScale shiftConstant : ℝ) (hscale : 1 ≤ cutoffScale) (hshift : 0 ≤ shiftConstant)
    (pool : ℕ → ℕ) (response sign : (parameter : ℕ) → palette parameter → ℝ)
    (hcalibrated : ∀ᶠ parameter in atTop,
      Parameters.legs parameter ≤ 2 * pool parameter ∧
      (∀ color, |sign parameter color| ≤ 1) ∧
      (∑ color, |response parameter color|) ≤
        32 * ((Parameters.anchorWidth parameter : ℝ) / Parameters.modulus parameter)) :
    ∀ᶠ parameter in atTop,
      let rank := rankInverseActivityConstant (1 / Real.sqrt (pool parameter : ℝ))
        (GaussianSource.v7Activation cutoffScale parameter) (2 * GaussianSource.v7Activation cutoffScale parameter)
        (response parameter) (sign parameter)
      let err := intervalTranslationActivityConstant (1 / Real.sqrt (pool parameter : ℝ))
        (shiftConstant * (Parameters.security parameter : ℝ) ^ 2) (Parameters.anchorWidth parameter)
        ((1 / 4 : ℝ) / Parameters.modulus parameter)
      (∑ color, |response parameter color|) < GaussianSource.v7Activation cutoffScale parameter ∧
      rank * err < 1 ∧ rank / (1 - rank * err) ≤ 2 := by
  have hsmall := ((tendsto_const_div_pow (32 : ℝ) 3 (by decide)).comp Parameters.security_tendsto).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hrankSmall := (primaryRankEnvelope_tendsto 2 32).eventually
    (gt_mem_nhds (by norm_num : (1 : ℝ) < 4 / 3))
  have herrSmall := (primaryTranslationEnvelope_tendsto shiftConstant (1 / 4)).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [hcalibrated, hsmall, hrankSmall, herrSmall,
    GaussianSource.v7Activation_lower_eventually cutoffScale hscale, eventually_ge_atTop 2]
    with parameter hc hs hr he ha hlarge
  dsimp only
  have hx : 0 < (Parameters.security parameter : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) (Parameters.security_ge_two parameter)
  have hq : 0 < (Parameters.modulus parameter : ℝ) := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have ha' : 1 / (Parameters.security parameter : ℝ) ^ 5 ≤ GaussianSource.v7Activation cutoffScale parameter := by
    simpa only [Parameters.security_eq parameter hlarge, one_div] using ha
  have hap : 0 < GaussianSource.v7Activation cutoffScale parameter := lt_of_lt_of_le (by positivity) ha'
  have hrate := v7_primary_pool_rate_bound parameter (pool parameter) hc.1
  have hl1 : (∑ color, |response parameter color|) ≤ 32 / (Parameters.security parameter : ℝ) ^ 8 := by
    exact (hc.2.2.trans (mul_le_mul_of_nonneg_left (v7_anchor_ratio_bound parameter) (by norm_num))).trans_eq (by ring)
  have hrank := rankInverseActivity_le_envelope (Parameters.security parameter)
    (1 / Real.sqrt (pool parameter : ℝ)) (GaussianSource.v7Activation cutoffScale parameter) 2 32
    (response parameter) (sign parameter) hx hrate.1.le hrate.2 ha' (by norm_num) (by norm_num) hc.2.1 hl1 hs.le
  have herr := intervalTranslationActivity_le_envelope (Parameters.security parameter) (Parameters.modulus parameter)
    (1 / Real.sqrt (pool parameter : ℝ)) shiftConstant (1 / 4) (Parameters.anchorWidth parameter) hx hq
    (by exact_mod_cast (Parameters.modulus_bounds parameter).2)
    (by simp [Parameters.anchorWidth]) hrate.2 hshift (by norm_num)
  let rank := rankInverseActivityConstant (1 / Real.sqrt (pool parameter : ℝ))
    (GaussianSource.v7Activation cutoffScale parameter) (2 * GaussianSource.v7Activation cutoffScale parameter)
    (response parameter) (sign parameter)
  let err := intervalTranslationActivityConstant (1 / Real.sqrt (pool parameter : ℝ))
    (shiftConstant * (Parameters.security parameter : ℝ) ^ 2) (Parameters.anchorWidth parameter)
    ((1 / 4 : ℝ) / Parameters.modulus parameter)
  have hrankBound : rank ≤ 4 / 3 := hrank.trans hr.le
  have herrBound : err ≤ 1 / 4 := herr.trans he.le
  have hrankNonneg : 0 ≤ rank := by dsimp [rank, rankInverseActivityConstant]; positivity
  have herrNonneg : 0 ≤ err := by dsimp [err, intervalTranslationActivityConstant]; positivity
  have hproduct : rank * err ≤ 1 / 3 := by
    have hh := mul_le_mul hrankBound herrBound herrNonneg (by norm_num : (0 : ℝ) ≤ 4 / 3)
    norm_num at hh ⊢
    exact hh
  refine ⟨?_, by change rank * err < 1; linarith, ?_⟩
  · have hh := calibrated_sign_small_of_power_bounds (Parameters.security parameter)
      (GaussianSource.v7Activation cutoffScale parameter) 32 (response parameter) hx ha' hl1 hs.le
    linarith
  · change rank / (1 - rank * err) ≤ 2
    apply (div_le_iff₀ (by linarith : 0 < 1 - rank * err)).mpr
    linarith

/-- For the actual primary law, anchor rows, clipped activation, and V7
powers, the local response has an inverse with uniform bound 2 on every
finite Hilbert-valued mixed fiber. Only physical support and retained-pool
conditions are premises. -/
theorem response_inverse_fibers_eventually {σ τ υ : ℕ → Type*}
    [∀ parameter, Fintype (σ parameter)] [∀ parameter, Fintype (τ parameter)]
    [∀ parameter, Fintype (υ parameter)]
    (cutoffScale shiftConstant : ℝ) (hscale : 1 ≤ cutoffScale) (hshiftConstant : 0 ≤ shiftConstant)
    (beta : ℕ → ℝ) (boundary : ℕ → ℤ) (pool : ℕ → ℕ)
    (bodyShifts : (parameter : ℕ) → σ parameter → ℤ)
    (bodyLaw : (parameter : ℕ) → FiniteDist (σ parameter))
    (startsPlus startsMinus sources : (parameter : ℕ) → τ parameter → ℤ)
    (sourceLaw : (parameter : ℕ) → FiniteDist (τ parameter))
    (bodyShift sourceShift : (parameter : ℕ) → υ parameter → ℤ)
    (noiseLaw : (parameter : ℕ) → FiniteDist (υ parameter))
    (hmodel : ∀ᶠ parameter in atTop,
      (PhysicalSupports parameter cutoffScale (boundary parameter)
        (startsPlus parameter) (startsMinus parameter) (sources parameter) ∧
      (∀ index, |bodyShifts parameter index| ≤ (Parameters.safeMargin parameter : ℤ) - boundary parameter) ∧
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) ∧
      Parameters.legs parameter ≤ 2 * pool parameter ∧
      (∀ index, ((bodyShift parameter index - sourceShift parameter index).natAbs : ℝ) ≤
        shiftConstant * (Parameters.security parameter : ℝ) ^ 2)) :
    ∀ᶠ parameter in atTop,
      let p := primary parameter cutoffScale (beta parameter) (boundary parameter)
        (bodyShifts parameter) (bodyLaw parameter) (startsPlus parameter) (startsMinus parameter)
        (sources parameter) (sourceLaw parameter)
      ∃ operator : (Fin (Parameters.modulus parameter) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus parameter) → ℝ),
        operator.toLinearMap = responseOperator parameter cutoffScale (boundary parameter)
          (startsPlus parameter) (startsMinus parameter) (sources parameter) (sourceLaw parameter)
          (bodyShift parameter) (sourceShift parameter) (noiseLaw parameter) ∧
        (∀ target, primaryActivity (1 / Real.sqrt (pool parameter : ℝ)) p (operator.symm target) ≤
          2 * primaryActivity (1 / Real.sqrt (pool parameter : ℝ)) p target) ∧
        (∀ (κ : Type*) [Fintype κ], ∀ (remaining : κ → ℝ) (kernel : Fin (Parameters.modulus parameter) → κ → ℝ),
          (∀ rest, 0 ≤ remaining rest) →
          coordinateActivity (1 / Real.sqrt (pool parameter : ℝ)) p remaining
            (partialProfileOperator operator.symm.toLinearMap p kernel) ≤
            2 * coordinateActivity (1 / Real.sqrt (pool parameter : ℝ)) p remaining kernel) := by
  have he := primary_estimates_eventually cutoffScale hscale beta boundary bodyShifts bodyLaw
    startsPlus startsMinus sources sourceLaw (hmodel.mono fun _ h => h.1)
  have hc := inverse_constants_eventually cutoffScale shiftConstant hscale hshiftConstant pool
    (fun parameter => signResponse parameter cutoffScale (boundary parameter) (startsPlus parameter)
      (startsMinus parameter) (sources parameter) (sourceLaw parameter))
    (fun parameter => paletteSign (Parameters.modulus parameter))
    (by filter_upwards [he, hmodel] with parameter he hm; exact ⟨hm.2.1, paletteSign_abs_le _, he.2.2.1⟩)
  filter_upwards [he, hc, hmodel] with parameter he hc hm
  dsimp only at he hc ⊢
  let p := primary parameter cutoffScale (beta parameter) (boundary parameter)
    (bodyShifts parameter) (bodyLaw parameter) (startsPlus parameter) (startsMinus parameter)
    (sources parameter) (sourceLaw parameter)
  let v := signResponse parameter cutoffScale (boundary parameter) (startsPlus parameter)
    (startsMinus parameter) (sources parameter) (sourceLaw parameter)
  let rate := 1 / Real.sqrt (pool parameter : ℝ)
  have hrate := (v7_primary_pool_rate_bound parameter (pool parameter) hm.2.1).1
  have hq : 0 < (Parameters.modulus parameter : ℝ) := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hlower : 0 < (1 / 4 : ℝ) / Parameters.modulus parameter := by positivity
  have hp : ∀ color, 0 < p color := fun color => lt_of_lt_of_le (by positivity) (he.1 color)
  have hout : ∀ color, (1 / 4 : ℝ) / Parameters.modulus parameter ≤ p color := fun color => by
    exact (show (1 / 4 : ℝ) / Parameters.modulus parameter = 1 / (4 * (Parameters.modulus parameter : ℝ)) by ring) ▸ he.1 color
  have hinj : Function.Injective (fun color : Fin (Parameters.modulus parameter) => (color.val : ℤ)) := by
    intro a b heq
    apply Fin.ext
    dsimp only at heq
    exact_mod_cast heq
  have hamajorant : 0 ≤ 2 * GaussianSource.v7Activation cutoffScale parameter := by
    have hh := hc.1
    have hn := Finset.sum_nonneg (fun color (_ : color ∈ Finset.univ) => abs_nonneg (v color))
    change (∑ color, |v color|) < GaussianSource.v7Activation cutoffScale parameter at hh
    linarith
  obtain ⟨operator, hoperator, hbound⟩ := finiteIntervalPrimary_inverse_exists
    (fun color : Fin (Parameters.modulus parameter) => (color.val : ℤ))
    (errorStarts parameter (sourceShift parameter)) (errorShift (bodyShift parameter) (sourceShift parameter))
    (Parameters.anchorWidth parameter) (errorLaw (noiseLaw parameter)).weight hinj rate
    (shiftConstant * (Parameters.security parameter : ℝ) ^ 2) ((1 / 4 : ℝ) / Parameters.modulus parameter)
    (GaussianSource.v7Activation cutoffScale parameter) (2 * GaussianSource.v7Activation cutoffScale parameter)
    p v (paletteSign (Parameters.modulus parameter)) (errorLaw _).nonneg (errorLaw _).sum_one
    hrate hp he.2.2.2.2 hlower hout (fun index => hm.2.2 index.1) hamajorant
    (paletteSign_abs_le _) he.2.1 hc.1 hc.2.1
  refine ⟨operator, hoperator, ?_, ?_⟩
  · intro target
    exact (hbound target).trans (mul_le_mul_of_nonneg_right hc.2.2
      (primaryActivity_nonneg rate p target hrate.le))
  · intro κ _ remaining kernel hremaining
    have hh := finiteIntervalPrimary_inverse_fiber_bound
      (fun color : Fin (Parameters.modulus parameter) => (color.val : ℤ))
      (errorStarts parameter (sourceShift parameter)) (errorShift (bodyShift parameter) (sourceShift parameter))
      (Parameters.anchorWidth parameter) (errorLaw (noiseLaw parameter)).weight hinj rate
      (shiftConstant * (Parameters.security parameter : ℝ) ^ 2) ((1 / 4 : ℝ) / Parameters.modulus parameter)
      (GaussianSource.v7Activation cutoffScale parameter) (2 * GaussianSource.v7Activation cutoffScale parameter)
      p v (paletteSign (Parameters.modulus parameter)) remaining kernel (errorLaw _).nonneg (errorLaw _).sum_one
      hrate.le hp he.2.2.2.2 hremaining hlower hout (fun index => hm.2.2 index.1) hamajorant
      (paletteSign_abs_le _) he.2.1 hc.1 hc.2.1 operator hoperator
    exact hh.trans (mul_le_mul_of_nonneg_right hc.2.2 (by
      unfold coordinateActivity integratedFiberNorm fixedFiberNorm
      positivity))

/-- Fixed-alphabet specialization of the uniform finite-fiber inverse. -/
theorem response_inverse_eventually {σ τ υ : ℕ → Type*} {κ : Type*} [Fintype κ]
    [∀ parameter, Fintype (σ parameter)] [∀ parameter, Fintype (τ parameter)]
    [∀ parameter, Fintype (υ parameter)]
    (cutoffScale shiftConstant : ℝ) (hscale : 1 ≤ cutoffScale) (hshiftConstant : 0 ≤ shiftConstant)
    (beta : ℕ → ℝ) (boundary : ℕ → ℤ) (pool : ℕ → ℕ)
    (bodyShifts : (parameter : ℕ) → σ parameter → ℤ)
    (bodyLaw : (parameter : ℕ) → FiniteDist (σ parameter))
    (startsPlus startsMinus sources : (parameter : ℕ) → τ parameter → ℤ)
    (sourceLaw : (parameter : ℕ) → FiniteDist (τ parameter))
    (bodyShift sourceShift : (parameter : ℕ) → υ parameter → ℤ)
    (noiseLaw : (parameter : ℕ) → FiniteDist (υ parameter))
    (hmodel : ∀ᶠ parameter in atTop,
      (PhysicalSupports parameter cutoffScale (boundary parameter)
        (startsPlus parameter) (startsMinus parameter) (sources parameter) ∧
      (∀ index, |bodyShifts parameter index| ≤ (Parameters.safeMargin parameter : ℤ) - boundary parameter) ∧
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) ∧
      Parameters.legs parameter ≤ 2 * pool parameter ∧
      (∀ index, ((bodyShift parameter index - sourceShift parameter index).natAbs : ℝ) ≤
        shiftConstant * (Parameters.security parameter : ℝ) ^ 2)) :
    ∀ᶠ parameter in atTop,
      let p := primary parameter cutoffScale (beta parameter) (boundary parameter)
        (bodyShifts parameter) (bodyLaw parameter) (startsPlus parameter) (startsMinus parameter)
        (sources parameter) (sourceLaw parameter)
      ∃ operator : (Fin (Parameters.modulus parameter) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus parameter) → ℝ),
        operator.toLinearMap = responseOperator parameter cutoffScale (boundary parameter)
          (startsPlus parameter) (startsMinus parameter) (sources parameter) (sourceLaw parameter)
          (bodyShift parameter) (sourceShift parameter) (noiseLaw parameter) ∧
        (∀ target, primaryActivity (1 / Real.sqrt (pool parameter : ℝ)) p (operator.symm target) ≤
          2 * primaryActivity (1 / Real.sqrt (pool parameter : ℝ)) p target) ∧
        (∀ (remaining : κ → ℝ) (kernel : Fin (Parameters.modulus parameter) → κ → ℝ),
          (∀ rest, 0 ≤ remaining rest) →
          coordinateActivity (1 / Real.sqrt (pool parameter : ℝ)) p remaining
            (partialProfileOperator operator.symm.toLinearMap p kernel) ≤
            2 * coordinateActivity (1 / Real.sqrt (pool parameter : ℝ)) p remaining kernel) := by
  filter_upwards [response_inverse_fibers_eventually cutoffScale shiftConstant hscale hshiftConstant
    beta boundary pool bodyShifts bodyLaw startsPlus startsMinus sources sourceLaw
    bodyShift sourceShift noiseLaw hmodel] with parameter h
  obtain ⟨operator, hoperator, hscalar, hfiber⟩ := h
  exact ⟨operator, hoperator, hscalar, hfiber κ⟩

end V7Calibration
end AFT
