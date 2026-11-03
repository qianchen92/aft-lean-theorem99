import AFT.BodyBlur

/-! # Physical support of the genuine body blur and public pair inputs -/

namespace AFT.GaussianSource

open Filter
open scoped BigOperators Classical Topology

noncomputable section

theorem legCutoff_le_square_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) :
    ∀ᶠ parameter : ℕ in atTop, legCutoff cutoffScale parameter ≤ parameter ^ 2 := by
  have ht := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 8)).comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (cutoffScale + 1))
  filter_upwards [ht, eventually_ge_atTop 1] with parameter ht hp
  dsimp only [Function.comp_apply] at ht
  have hp' : (1 : ℝ) ≤ parameter := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < parameter := by positivity
  have hr : 1 ≤ (parameter : ℝ) ^ (9 / 8 : ℝ) := Real.one_le_rpow hp' (by norm_num)
  have hceil := (Nat.ceil_lt_add_one (show 0 ≤ cutoffScale * (parameter : ℝ) ^ (9 / 8 : ℝ) by positivity)).le
  have hh : (legCutoff cutoffScale parameter : ℝ) ≤ (parameter : ℝ) ^ 2 := by
    calc
      _ ≤ (cutoffScale + 1) * (parameter : ℝ) ^ (9 / 8 : ℝ) := by dsimp only [legCutoff]; nlinarith
      _ ≤ (parameter : ℝ) ^ (7 / 8 : ℝ) * (parameter : ℝ) ^ (9 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg hp0.le _)
      _ = _ := by
        rw [← Real.rpow_add hp0]
        norm_num
        exact Real.rpow_two _
  exact_mod_cast hh

def boundaryHalf (cutoffScale : ℝ) (parameter : ℕ) : ℤ :=
  (Parameters.safeMargin parameter : ℤ) - maxBodyShift cutoffScale parameter

theorem body_support_scales_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) :
    ∀ᶠ parameter : ℕ in atTop,
      maxBodyShift cutoffScale parameter ≤ Parameters.safeMargin parameter ∧
      maxBodyShift cutoffScale parameter ≤ Parameters.anchorWidth parameter ∧
      0 ≤ boundaryHalf cutoffScale parameter ∧ boundaryHalf cutoffScale parameter ≤ Parameters.safeMargin parameter := by
  filter_upwards [legCutoff_le_square_eventually cutoffScale hscale, eventually_ge_atTop 2]
    with parameter hl hp
  have hmax : maxBodyShift cutoffScale parameter ≤ 5 * parameter ^ 2 := by
    unfold maxBodyShift v7RootCutoff queueCutoff
    omega
  have hm : 5 * parameter ^ 2 ≤ Parameters.safeMargin parameter := by
    simp only [Parameters.safeMargin, Parameters.security_eq parameter hp]
    omega
  have ha : 5 * parameter ^ 2 ≤ Parameters.anchorWidth parameter := by
    have hh : 5 ≤ parameter ^ 30 := by
      have hh := Nat.pow_le_pow_left hp 30
      omega
    have hh' := Nat.mul_le_mul_right (parameter ^ 2) hh
    simpa only [Parameters.anchorWidth, Parameters.security_eq parameter hp, ← pow_add] using hh'
  refine ⟨hmax.trans hm, hmax.trans ha, ?_, ?_⟩ <;> unfold boundaryHalf <;> omega

def pairSample (cutoffScale : ℝ) (parameter : ℕ) :=
  bodySample cutoffScale parameter × Window (legCutoff cutoffScale parameter - 1)

instance pairSampleFintype (cutoffScale : ℝ) (parameter : ℕ) : Fintype (pairSample cutoffScale parameter) :=
  inferInstanceAs (Fintype (_ × _))

def pairSourceLaw (cutoffScale : ℝ) (parameter : ℕ) : FiniteDist (pairSample cutoffScale parameter) :=
  (bodyBlur cutoffScale parameter).prod (windowGaussian (10 * parameter) (legCutoff cutoffScale parameter - 1))

def pairSourceShift (cutoffScale : ℝ) (parameter : ℕ) (sample : pairSample cutoffScale parameter) : ℤ :=
  sample.2

def startsPlus (cutoffScale : ℝ) (parameter : ℕ) (sample : pairSample cutoffScale parameter) : ℤ :=
  (Parameters.anchorWidth parameter : ℤ) + bodyShift cutoffScale parameter sample.1

def startsMinus (cutoffScale : ℝ) (parameter : ℕ) (sample : pairSample cutoffScale parameter) : ℤ :=
  -(2 * (Parameters.anchorWidth parameter : ℤ)) + 1 + bodyShift cutoffScale parameter sample.1

/-- The real root/optional-noise product law provides the physical inputs
required by all previously proved primary and mean estimates. -/
theorem actual_physical_supports_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) :
    ∀ᶠ parameter : ℕ in atTop,
      V7Calibration.PhysicalSupports parameter cutoffScale (boundaryHalf cutoffScale parameter)
        (startsPlus cutoffScale parameter) (startsMinus cutoffScale parameter) (pairSourceShift cutoffScale parameter) ∧
      (∀ sample, |bodyShift cutoffScale parameter sample| ≤
        (Parameters.safeMargin parameter : ℤ) - boundaryHalf cutoffScale parameter) := by
  filter_upwards [body_support_scales_eventually cutoffScale hscale] with parameter hs
  refine ⟨⟨⟨hs.2.2.1, hs.2.2.2⟩, ?_, ?_, ?_⟩, ?_⟩
  · intro sample shift hshift
    have hb := abs_le.mp (bodyShift_abs_le cutoffScale parameter sample.1)
    have hA : (maxBodyShift cutoffScale parameter : ℤ) ≤ Parameters.anchorWidth parameter := by exact_mod_cast hs.2.1
    simp only [anchorInterval, Finset.mem_Ico, startsPlus] at hshift
    exact abs_le.mpr (by constructor <;> omega)
  · intro sample shift hshift
    have hb := abs_le.mp (bodyShift_abs_le cutoffScale parameter sample.1)
    have hA : (maxBodyShift cutoffScale parameter : ℤ) ≤ Parameters.anchorWidth parameter := by exact_mod_cast hs.2.1
    simp only [anchorInterval, Finset.mem_Ico, startsMinus] at hshift
    exact abs_le.mpr (by constructor <;> omega)
  · intro sample
    have hh := Finset.mem_Icc.mp sample.2.property
    dsimp only [pairSourceShift]
    exact (abs_le.mpr hh).trans (by exact_mod_cast Nat.sub_le (legCutoff cutoffScale parameter) 1)
  · intro sample
    simpa only [boundaryHalf, sub_sub_cancel] using bodyShift_abs_le cutoffScale parameter sample

end

end AFT.GaussianSource
