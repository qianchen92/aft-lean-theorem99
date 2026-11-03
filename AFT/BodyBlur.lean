import AFT.BackgroundMeanParameters
import AFT.GaussianReflection
import AFT.RootErrorParameters

/-!
# The actual body blur of referenceV7

The finite sample includes the true root marginal and independent marginal
attachment/queue indicators. It asserts no independence among different
physical body coordinates.
-/

namespace AFT

open scoped BigOperators Classical

noncomputable section

namespace FiniteDist

variable {α : Type*} [Fintype α]

def optional (source : FiniteDist α) (rate : ℝ) (h0 : 0 ≤ rate) (h1 : rate ≤ 1) : FiniteDist (Option α) where
  weight value := match value with | none => 1 - rate | some a => rate * source.weight a
  nonneg value := by cases value with
    | none => exact sub_nonneg.mpr h1
    | some a => exact mul_nonneg h0 (source.nonneg a)
  sum_one := by
    rw [Fintype.sum_option]
    simp only [← Finset.mul_sum, source.sum_one, mul_one]
    ring

@[simp] theorem optional_none (source : FiniteDist α) (rate : ℝ) (h0 h1) :
    (optional source rate h0 h1).weight none = 1 - rate := rfl

@[simp] theorem optional_some (source : FiniteDist α) (rate : ℝ) (h0 h1) (a : α) :
    (optional source rate h0 h1).weight (some a) = rate * source.weight a := rfl

/-- Retaining a component of mass at least one half controls its upper
profile deficit by twice the total mixture's deficit. -/
theorem component_deficit_le_twice {β : Type*} [Fintype β]
    (root : FiniteDist α) (extra : FiniteDist β) (selected : β)
    (kernel : α → β → ℝ) (upper : ℝ)
    (hselected : 1 / 2 ≤ extra.weight selected)
    (hupper : ∀ a b, kernel a b ≤ upper) :
    upper - (∑ a, root.weight a * kernel a selected) ≤
      2 * (upper - (∑ a, ∑ b, root.weight a * extra.weight b * kernel a b)) := by
  let deficit := fun b => upper - ∑ a, root.weight a * kernel a b
  have hd (b) : 0 ≤ deficit b := by
    apply sub_nonneg.mpr
    calc
      _ ≤ ∑ a, root.weight a * upper := Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_left (hupper a b) (root.nonneg a)
      _ = _ := by rw [← Finset.sum_mul, root.sum_one, one_mul]
  have hsum : ∑ b, extra.weight b * deficit b =
      upper - (∑ a, ∑ b, root.weight a * extra.weight b * kernel a b) := by
    dsimp only [deficit]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, extra.sum_one, one_mul]
    congr 1
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hsingle := Finset.single_le_sum (fun b (_ : b ∈ Finset.univ) => mul_nonneg (extra.nonneg b) (hd b))
    (Finset.mem_univ selected)
  have hh := mul_le_mul_of_nonneg_right hselected (hd selected)
  rw [hsum] at hsingle
  dsimp only [deficit] at hh
  nlinarith

end FiniteDist

namespace GaussianSource

def queueCutoff (parameter : ℕ) : ℕ := parameter ^ 2 - 1

def legRate (parameter : ℕ) : ℝ := (Parameters.legs parameter : ℝ) / Parameters.bodies parameter

def queueRate (parameter : ℕ) : ℝ := (Parameters.modulus parameter : ℝ) / Parameters.bodies parameter

theorem body_rates_le_quarter (parameter : ℕ) : legRate parameter ≤ 1 / 4 ∧ queueRate parameter ≤ 1 / 4 := by
  have hx := Parameters.security_ge_two parameter
  have hm8 : 8 ≤ Parameters.legs parameter := by
    have hh := Nat.pow_le_pow_left hx 30
    change 8 ≤ Parameters.security parameter ^ 30
    omega
  have hdim8m : 8 * Parameters.legs parameter ≤ Parameters.dimension parameter := by
    have hh := (Parameters.dimension_bounds parameter).1
    have heq : Parameters.security parameter ^ 60 = Parameters.legs parameter * Parameters.legs parameter := by
      unfold Parameters.legs
      rw [← pow_add]
    rw [heq] at hh
    exact (Nat.mul_le_mul_right _ hm8).trans hh
  have hx20 : 8 ≤ Parameters.security parameter ^ 20 := by
    have hh := Nat.pow_le_pow_left hx 20
    omega
  have hdim8q : 8 * Parameters.modulus parameter ≤ Parameters.dimension parameter := by
    have hh := Nat.mul_le_mul_left (Parameters.modulus parameter) hx20
    simpa only [Parameters.dimension, Parameters.meanDensity, Nat.mul_comm] using hh
  have hpop := Parameters.population_identity parameter
  have hm4 : 4 * Parameters.legs parameter ≤ Parameters.bodies parameter := by omega
  have hq4 : 4 * Parameters.modulus parameter ≤ Parameters.bodies parameter := by omega
  have hN : (0 : ℝ) < Parameters.bodies parameter := by exact_mod_cast Parameters.bodies_positive parameter
  constructor
  · unfold legRate
    apply (div_le_iff₀ hN).mpr
    have hh : 4 * (Parameters.legs parameter : ℝ) ≤ Parameters.bodies parameter := by exact_mod_cast hm4
    linarith
  · unfold queueRate
    apply (div_le_iff₀ hN).mpr
    have hh : 4 * (Parameters.modulus parameter : ℝ) ≤ Parameters.bodies parameter := by exact_mod_cast hq4
    linarith

def optionalShift {cutoff : ℕ} : Option (Window cutoff) → ℤ
  | none => 0
  | some z => z

def extraSample (cutoffScale : ℝ) (parameter : ℕ) :=
  Option (Window (legCutoff cutoffScale parameter - 1)) × Option (Window (queueCutoff parameter))

instance extraSampleFintype (cutoffScale : ℝ) (parameter : ℕ) : Fintype (extraSample cutoffScale parameter) :=
  inferInstanceAs (Fintype (_ × _))

def extraShift (cutoffScale : ℝ) (parameter : ℕ) (sample : extraSample cutoffScale parameter) : ℤ :=
  optionalShift sample.1 + optionalShift sample.2

def extraBlur (cutoffScale : ℝ) (parameter : ℕ) : FiniteDist (extraSample cutoffScale parameter) :=
  (FiniteDist.optional (windowGaussian (10 * parameter) (legCutoff cutoffScale parameter - 1))
    (legRate parameter) (by unfold legRate; positivity) ((body_rates_le_quarter parameter).1.trans (by norm_num))).prod
  (FiniteDist.optional (windowGaussian parameter (queueCutoff parameter))
    (queueRate parameter) (by unfold queueRate; positivity) ((body_rates_le_quarter parameter).2.trans (by norm_num)))

def bodySample (cutoffScale : ℝ) (parameter : ℕ) :=
  Window (v7RootCutoff parameter) × extraSample cutoffScale parameter

instance bodySampleFintype (cutoffScale : ℝ) (parameter : ℕ) : Fintype (bodySample cutoffScale parameter) :=
  inferInstanceAs (Fintype (_ × _))

def bodyShift (cutoffScale : ℝ) (parameter : ℕ) (sample : bodySample cutoffScale parameter) : ℤ :=
  (sample.1 : ℤ) + extraShift cutoffScale parameter sample.2

def bodyBlur (cutoffScale : ℝ) (parameter : ℕ) : FiniteDist (bodySample cutoffScale parameter) :=
  (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
    (Parameters.bodies_positive parameter)).prod (extraBlur cutoffScale parameter)


def extraReverse (cutoffScale : ℝ) (parameter : ℕ) : extraSample cutoffScale parameter ≃ extraSample cutoffScale parameter :=
  (Equiv.optionCongr (windowNegateEquiv (legCutoff cutoffScale parameter - 1))).prodCongr
    (Equiv.optionCongr (windowNegateEquiv (queueCutoff parameter)))

def bodyReverse (cutoffScale : ℝ) (parameter : ℕ) : bodySample cutoffScale parameter ≃ bodySample cutoffScale parameter :=
  (windowNegateEquiv (v7RootCutoff parameter)).prodCongr (extraReverse cutoffScale parameter)

theorem extraReverse_apply (cutoffScale : ℝ) (parameter : ℕ) (sample : extraSample cutoffScale parameter) :
    extraReverse cutoffScale parameter sample =
      ((Equiv.optionCongr (windowNegateEquiv (legCutoff cutoffScale parameter - 1))) sample.1,
        (Equiv.optionCongr (windowNegateEquiv (queueCutoff parameter))) sample.2) := rfl

theorem bodyReverse_apply (cutoffScale : ℝ) (parameter : ℕ) (sample : bodySample cutoffScale parameter) :
    bodyReverse cutoffScale parameter sample =
      (windowNegateEquiv (v7RootCutoff parameter) sample.1, extraReverse cutoffScale parameter sample.2) := rfl

theorem optionalShift_reverse (cutoff : ℕ) (value : Option (Window cutoff)) :
    optionalShift ((Equiv.optionCongr (windowNegateEquiv cutoff)) value) = -optionalShift value := by
  cases value <;> rfl

theorem extraShift_reverse (cutoffScale : ℝ) (parameter : ℕ) (sample : extraSample cutoffScale parameter) :
    extraShift cutoffScale parameter (extraReverse cutoffScale parameter sample) = -extraShift cutoffScale parameter sample := by
  rcases sample with ⟨a, b⟩
  simp only [extraReverse_apply, extraShift, optionalShift_reverse]
  ring

theorem bodyShift_reverse (cutoffScale : ℝ) (parameter : ℕ) (sample : bodySample cutoffScale parameter) :
    bodyShift cutoffScale parameter (bodyReverse cutoffScale parameter sample) = -bodyShift cutoffScale parameter sample := by
  rcases sample with ⟨a, b⟩
  simp only [bodyReverse_apply, bodyShift, windowNegateEquiv_val, extraShift_reverse]
  ring

theorem optionalGaussian_reflection (width : ℝ) (cutoff : ℕ) (rate : ℝ) (h0 h1)
    (value : Option (Window cutoff)) :
    (FiniteDist.optional (windowGaussian width cutoff) rate h0 h1).weight
      ((Equiv.optionCongr (windowNegateEquiv cutoff)) value) =
      (FiniteDist.optional (windowGaussian width cutoff) rate h0 h1).weight value := by
  cases value with
  | none => rfl
  | some z => simpa only [FiniteDist.optional] using congrArg (fun x => rate * x) (windowGaussian_reflection width cutoff z)

theorem extraBlur_reflection (cutoffScale : ℝ) (parameter : ℕ) (sample : extraSample cutoffScale parameter) :
    (extraBlur cutoffScale parameter).weight (extraReverse cutoffScale parameter sample) =
      (extraBlur cutoffScale parameter).weight sample := by
  rcases sample with ⟨a, b⟩
  simp only [extraReverse_apply, extraBlur, FiniteDist.prod_weight, optionalGaussian_reflection]

theorem bodyBlur_reflection (cutoffScale : ℝ) (parameter : ℕ) (sample : bodySample cutoffScale parameter) :
    (bodyBlur cutoffScale parameter).weight (bodyReverse cutoffScale parameter sample) =
      (bodyBlur cutoffScale parameter).weight sample := by
  rcases sample with ⟨a, b⟩
  simp only [bodyReverse_apply, bodyBlur, FiniteDist.prod_weight, rootMarginal_reflection, extraBlur_reflection]

/-- The actual extra blur gives its no-leg, no-queue component at least
one half of its total mass, for every security parameter. -/
theorem extraBlur_none_mass (cutoffScale : ℝ) (parameter : ℕ) :
    1 / 2 ≤ (extraBlur cutoffScale parameter).weight (none, none) := by
  have hl := (body_rates_le_quarter parameter).1
  have hq := (body_rates_le_quarter parameter).2
  have hl0 : 0 ≤ legRate parameter := by unfold legRate; positivity
  have hq0 : 0 ≤ queueRate parameter := by unfold queueRate; positivity
  change 1 / 2 ≤ (1 - legRate parameter) * (1 - queueRate parameter)
  nlinarith [mul_nonneg hl0 hq0]

def maxBodyShift (cutoffScale : ℝ) (parameter : ℕ) : ℕ :=
  v7RootCutoff parameter + (legCutoff cutoffScale parameter - 1) + queueCutoff parameter

theorem optionalShift_abs_le {cutoff : ℕ} (sample : Option (Window cutoff)) :
    |optionalShift sample| ≤ (cutoff : ℤ) := by
  cases sample with
  | none => simp [optionalShift]
  | some z =>
    have hz := Finset.mem_Icc.mp z.property
    exact abs_le.mpr hz

theorem bodyShift_abs_le (cutoffScale : ℝ) (parameter : ℕ) (sample : bodySample cutoffScale parameter) :
    |bodyShift cutoffScale parameter sample| ≤ (maxBodyShift cutoffScale parameter : ℤ) := by
  have hz := Finset.mem_Icc.mp sample.1.property
  have hroot : |(sample.1 : ℤ)| ≤ (v7RootCutoff parameter : ℤ) := abs_le.mpr hz
  have he := (abs_add_le (optionalShift sample.2.1) (optionalShift sample.2.2)).trans
    (add_le_add (optionalShift_abs_le sample.2.1) (optionalShift_abs_le sample.2.2))
  have hh := (abs_add_le (sample.1 : ℤ) (extraShift cutoffScale parameter sample.2)).trans (add_le_add hroot he)
  simpa only [bodyShift, maxBodyShift, Nat.cast_add, add_assoc] using hh

/-- The real root component's deficit is controlled by the actual full
body blur, owing to its explicitly constructed no-placement component. -/
theorem root_bodyMean_deficit_le_twice (cutoffScale : ℝ) (parameter : ℕ) (color : ℤ)
    (hwidth : 2 * Parameters.safeMargin parameter < Parameters.modulus parameter) :
    1 / ((Parameters.modulus parameter : ℝ) - 2 * Parameters.safeMargin parameter) -
      TrimmedSlice.blurredSafeLaw (Parameters.modulus parameter) (Parameters.safeMargin parameter)
        (fun z : Window (v7RootCutoff parameter) => (z : ℤ))
        (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
          (Parameters.bodies_positive parameter)).weight color ≤
    2 * (1 / ((Parameters.modulus parameter : ℝ) - 2 * Parameters.safeMargin parameter) -
      TrimmedSlice.blurredSafeLaw (Parameters.modulus parameter) (Parameters.safeMargin parameter)
        (bodyShift cutoffScale parameter) (bodyBlur cutoffScale parameter).weight color) := by
  have hcast : (((Parameters.modulus parameter : ℤ) - 2 * Parameters.safeMargin parameter).toNat : ℝ) =
      (Parameters.modulus parameter : ℝ) - 2 * Parameters.safeMargin parameter := by
    have hh : (((Parameters.modulus parameter : ℤ) - 2 * Parameters.safeMargin parameter).toNat : ℤ) =
        (Parameters.modulus parameter : ℤ) - 2 * Parameters.safeMargin parameter := Int.toNat_of_nonneg (by omega)
    exact_mod_cast hh
  have hh := FiniteDist.component_deficit_le_twice
    (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
      (Parameters.bodies_positive parameter)) (extraBlur cutoffScale parameter) (none, none)
    (fun z e => intervalAnchorLaw (Parameters.safeMargin parameter)
      ((Parameters.modulus parameter : ℤ) - 2 * Parameters.safeMargin parameter).toNat
        (color - ((z : ℤ) + extraShift cutoffScale parameter e)))
    (1 / ((Parameters.modulus parameter : ℝ) - 2 * Parameters.safeMargin parameter))
    (extraBlur_none_mass cutoffScale parameter)
    (by
      intro z e
      simpa only [hcast, one_div] using (intervalAnchorLaw_bound (Parameters.safeMargin parameter)
        (color - ((z : ℤ) + extraShift cutoffScale parameter e))
        ((Parameters.modulus parameter : ℤ) - 2 * Parameters.safeMargin parameter).toNat))
  simpa only [TrimmedSlice.blurredSafeLaw, extraShift, optionalShift, zero_add, add_zero,
    bodyBlur, bodyShift, FiniteDist.prod_weight, bodySampleFintype, bodySample, Fintype.sum_prod_type] using hh

end GaussianSource

end

end AFT
