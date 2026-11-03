import AFT.ChartGaussianOutput
import AFT.ActualPairSourceDifference

/-! # The true primary-dependent public sign branch -/

namespace AFT.V7Calibration

open GaussianSource BoundaryCalibration Filter
open scoped BigOperators Classical Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance conditionalPairFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- The baseline interval of the pair sum, before its actual body blur. -/
def conditionalBaselineStart (modulus width : ℕ) (mark : Fin modulus) (coin : Bool) : ℤ :=
  publicAnchorStart modulus width mark coin + mark.val - ((modulus : ℤ) - 1)

theorem conditionalBaselineStart_formula (modulus width : ℕ) (mark : Fin modulus) (coin : Bool) :
    conditionalBaselineStart modulus width mark coin =
      if 2 * mark.val < modulus - 1 then -(2 * (width : ℤ)) + 1
      else if modulus - 1 < 2 * mark.val then (width : ℤ)
      else if coin then -(2 * (width : ℤ)) + 1 else (width : ℤ) := by
  unfold conditionalBaselineStart publicAnchorStart
  split_ifs <;> ring

def conditionalPairStart (cutoffScale : ℝ) (parameter : ℕ) (mark : Fin (Parameters.modulus parameter))
    (sample : bodySample cutoffScale parameter × Bool) : ℤ :=
  conditionalBaselineStart (Parameters.modulus parameter) (Parameters.anchorWidth parameter) mark sample.2 +
    bodyShift cutoffScale parameter sample.1

/-- The diffuse pair at a given primary mark keeps the real sign branch;
the fair coin is used only when the mark is at the midpoint. -/
def conditionalPairAtSource (cutoffScale : ℝ) (parameter : ℕ) (mark : Fin (Parameters.modulus parameter))
    (source : ℤ) (first second : Fin (Parameters.modulus parameter)) : ℝ :=
  TrimmedSlice.mixedPair (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
    (conditionalPairStart cutoffScale parameter mark) (fun _ => source)
    (errorLaw (bodyBlur cutoffScale parameter)).weight (Parameters.anchorWidth parameter) first second

def signedPairAtSource (cutoffScale : ℝ) (parameter : ℕ) (source : ℤ)
    (first second : Fin (Parameters.modulus parameter)) : ℝ :=
  (TrimmedSlice.mixedPair (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
    (fun sample => (Parameters.anchorWidth parameter : ℤ) + bodyShift cutoffScale parameter sample)
    (fun _ => source) (bodyBlur cutoffScale parameter).weight (Parameters.anchorWidth parameter) first second -
   TrimmedSlice.mixedPair (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
    (fun sample => -(2 * (Parameters.anchorWidth parameter : ℤ)) + 1 + bodyShift cutoffScale parameter sample)
    (fun _ => source) (bodyBlur cutoffScale parameter).weight (Parameters.anchorWidth parameter) first second) / 2

/-- The exact sign-affine identity is proved from the actual reflected
anchor intervals, including the midpoint coin. -/
theorem conditionalPairAtSource_formula (cutoffScale : ℝ) (parameter : ℕ)
    (mark : Fin (Parameters.modulus parameter)) (source : ℤ)
    (first second : Fin (Parameters.modulus parameter)) :
    conditionalPairAtSource cutoffScale parameter mark source first second =
      inactivePairAtSource cutoffScale parameter source first second +
      paletteSign (Parameters.modulus parameter) mark * signedPairAtSource cutoffScale parameter source first second := by
  simp only [conditionalPairAtSource, conditionalPairStart, conditionalBaselineStart_formula,
    TrimmedSlice.mixedPair, errorLaw, Fintype.sum_prod_type, FiniteDist.prod_weight,
    FiniteDist.uniform_weight, Fintype.card_bool, Nat.cast_ofNat, Fintype.sum_bool,
    Bool.false_eq_true, if_false, if_true, inactivePairAtSource, signedPairAtSource, paletteSign]
  split_ifs <;> simp only [Finset.sum_add_distrib]
  all_goals ring_nf
  all_goals simp only [← Finset.sum_mul]
  all_goals ring

/-- Canonical primary profiles remove the diffuse mean; only the actual
bounded sign functional multiplies the signed source-dependent pair. -/
theorem conditionalPairAtSource_signed (cutoffScale : ℝ) (parameter : ℕ)
    (profile : Fin (Parameters.modulus parameter) → ℝ) (hcanonical : ∑ mark, profile mark = 0)
    (source : ℤ) (first second : Fin (Parameters.modulus parameter)) :
    (∑ mark, profile mark * conditionalPairAtSource cutoffScale parameter mark source first second) =
      (∑ mark, paletteSign (Parameters.modulus parameter) mark * profile mark) *
        signedPairAtSource cutoffScale parameter source first second := by
  simp only [conditionalPairAtSource_formula, mul_add, Finset.sum_add_distrib,
    ← Finset.sum_mul, hcanonical, zero_mul, zero_add]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro mark _
  ring

/-- Every conditional anchor interval lies within the proved legal chart
baseline range. No extra hypothesis on primary marks is needed. -/
theorem conditional_chart_legal_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) :
    ∀ᶠ parameter in atTop,
      0 ≤ boundaryHalf cutoffScale parameter ∧
      ∀ (mark : Fin (Parameters.modulus parameter)) (sample : bodySample cutoffScale parameter × Bool),
      ∀ baseline ∈ anchorInterval (conditionalPairStart cutoffScale parameter mark sample) (Parameters.anchorWidth parameter),
        V7ChartExists cutoffScale parameter (boundaryHalf cutoffScale parameter) baseline
          ((ZMod.finEquiv (Parameters.modulus parameter)) mark) := by
  filter_upwards [v7_marked_chart_eventually cutoffScale hscale, body_support_scales_eventually cutoffScale hscale]
    with parameter hc hs
  refine ⟨hs.2.2.1, ?_⟩
  intro mark sample baseline hbase
  apply hc _ _ hs.2.2.1 hs.2.2.2
  have hb := abs_le.mp (bodyShift_abs_le cutoffScale parameter sample.1)
  have hmax : (maxBodyShift cutoffScale parameter : ℤ) ≤ Parameters.anchorWidth parameter := by exact_mod_cast hs.2.1
  simp only [conditionalPairStart, conditionalBaselineStart_formula] at hbase
  split_ifs at hbase <;> simp only [anchorInterval, Finset.mem_Ico] at hbase <;>
    exact abs_le.mpr (by constructor <;> omega)

end
end AFT.V7Calibration
