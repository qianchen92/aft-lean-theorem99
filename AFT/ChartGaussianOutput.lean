import AFT.ChartPairOutput
import AFT.ActualTriples

/-! # Averaging the real chart output over its two protected Gaussian sources -/

namespace AFT

open scoped BigOperators Classical

noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance chartGaussianFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

namespace FiniteDist

/-- Extract the marked atom from a product source without conditioning or
resampling the retained second source. -/
theorem product_marked_average {First Second : Type*} [Fintype First] [Fintype Second]
    [DecidableEq First] [DecidableEq Second]
    (firstLaw : FiniteDist First) (secondLaw : FiniteDist Second)
    (firstZero : First) (secondZero : Second) (atom : ℝ) (base marked : Second → ℝ) :
    (∑ input : First × Second, (firstLaw.prod secondLaw).weight input *
      ((1 - if input = (firstZero,secondZero) then atom else 0) * base input.2 +
        (if input = (firstZero,secondZero) then atom else 0) * marked input.2)) =
      (∑ source, secondLaw.weight source * base source) -
        (firstLaw.weight firstZero * secondLaw.weight secondZero * atom) * base secondZero +
        (firstLaw.weight firstZero * secondLaw.weight secondZero * atom) * marked secondZero := by
  have hextract (function : First × Second → ℝ) :
      (∑ input, (firstLaw.prod secondLaw).weight input *
        (if input = (firstZero,secondZero) then atom else 0) * function input) =
      (firstLaw.weight firstZero * secondLaw.weight secondZero * atom) * function (firstZero,secondZero) := by
    simp only [mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, prod_weight]
  have hbase : (∑ input : First × Second, (firstLaw.prod secondLaw).weight input * base input.2) =
      ∑ source, secondLaw.weight source * base source := by
    simp only [Fintype.sum_prod_type, prod_weight, mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul,
      firstLaw.sum_one, one_mul]
  simp only [sub_mul, one_mul, mul_add, mul_sub, ← mul_assoc, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, hextract, hbase]

end FiniteDist

namespace BoundaryCalibration
open GaussianSource Filter
open scoped Topology
attribute [local instance] actualModulusNeZero

/-- The chart's two genuine clipped Gaussian source laws. -/
def protectedGaussianLaw (cutoffScale : ℝ) (parameter : ℕ) : FiniteDist (V7Input cutoffScale parameter) :=
  (windowGaussian parameter (legCutoff cutoffScale parameter - 1)).prod
    (windowGaussian (10 * parameter) (legCutoff cutoffScale parameter - 1))

theorem protected_mark_probability (cutoffScale : ℝ) (parameter : ℕ)
    (hscale : 1 ≤ cutoffScale) (hp : 1 ≤ parameter) :
    (protectedGaussianLaw cutoffScale parameter).weight (windowZero _,windowZero _) * chartAtom (V7Input cutoffScale parameter) =
      v7Activation cutoffScale parameter := by
  rw [v7_chartAtom_eq cutoffScale parameter hscale hp]
  unfold protectedGaussianLaw v7Activation activation
  rw [one_div]
  ring

/-- Marking the zero input preserves the exact original source weights.
The arbitrary two functions may include a body depending on that same source. -/
theorem protected_gaussian_marked_average (cutoffScale : ℝ) (parameter : ℕ)
    (hscale : 1 ≤ cutoffScale) (hp : 1 ≤ parameter)
    (base marked : Window (legCutoff cutoffScale parameter - 1) → ℝ) :
    (∑ input : V7Input cutoffScale parameter, (protectedGaussianLaw cutoffScale parameter).weight input *
      ((1 - if input = (windowZero _,windowZero _) then chartAtom (V7Input cutoffScale parameter) else 0) * base input.2 +
        (if input = (windowZero _,windowZero _) then chartAtom (V7Input cutoffScale parameter) else 0) * marked input.2)) =
      (1 - v7Activation cutoffScale parameter) *
        (∑ source, (inactiveLegSource cutoffScale parameter).weight source * base source) +
      v7Activation cutoffScale parameter * marked (windowZero _) := by
  have hh := FiniteDist.product_marked_average
    (windowGaussian parameter (legCutoff cutoffScale parameter - 1))
    (windowGaussian (10 * parameter) (legCutoff cutoffScale parameter - 1))
    (windowZero _) (windowZero _) (chartAtom (V7Input cutoffScale parameter)) base marked
  have hmark := protected_mark_probability cutoffScale parameter hscale hp
  change _ * _ * _ = _ at hmark
  rw [hmark] at hh
  apply hh.trans
  have hinactive : (1 - v7Activation cutoffScale parameter) *
      (∑ source, (inactiveLegSource cutoffScale parameter).weight source * base source) =
      (∑ source, (windowGaussian (10 * parameter) (legCutoff cutoffScale parameter - 1)).weight source * base source) -
        v7Activation cutoffScale parameter * base (windowZero _) := by
    simp only [Finset.mul_sum, ← mul_assoc]
    have hpoint (source : Window (legCutoff cutoffScale parameter - 1)) :
        (1 - v7Activation cutoffScale parameter) * (inactiveLegSource cutoffScale parameter).weight source =
          (windowGaussian (10 * parameter) (legCutoff cutoffScale parameter - 1)).weight source -
            (if source = windowZero _ then v7Activation cutoffScale parameter else 0) := by
      linarith [inactiveLegSource_mixture cutoffScale parameter source]
    simp only [hpoint, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hinactive]

/-- The actual affine chart followed by the genuine Gaussian errors yields
its retained-source diffuse pair and the full marked pair probability. -/
theorem gaussian_chart_joint_output (cutoffScale : ℝ) (parameter : ℕ)
    (hscale : 1 ≤ cutoffScale) (hp : 1 ≤ parameter) (boundary baseline : ℤ)
    (hb : 0 ≤ boundary) (mark : Fin (Parameters.modulus parameter))
    (hchart : V7ChartExists cutoffScale parameter boundary baseline
      ((ZMod.finEquiv (Parameters.modulus parameter)) mark)) :
    ∃ chartLaw : FiniteDist (Chart (ZMod (Parameters.modulus parameter))),
      ∀ first second : Fin (Parameters.modulus parameter),
      ∀ attached : Window (legCutoff cutoffScale parameter - 1) → ℝ,
      (∑ input : V7Input cutoffScale parameter, (protectedGaussianLaw cutoffScale parameter).weight input *
        (chartPairOutput cutoffScale parameter baseline chartLaw input).weight (first,second) * attached input.2) =
      (1 - v7Activation cutoffScale parameter) *
        (∑ source, (inactiveLegSource cutoffScale parameter).weight source *
          (TrimmedSlice.orderedPairSlice (Parameters.modulus parameter) boundary (baseline - source) first second * attached source)) +
      v7Activation cutoffScale parameter *
        ((if first = mark then 1 else 0) *
          (if second = paletteEmbedding parameter ((Parameters.modulus parameter : ℤ) - 1 + baseline - mark.val) then 1 else 0) *
          attached (windowZero _)) := by
  obtain ⟨law, hlaw⟩ := chart_joint_output cutoffScale parameter boundary baseline hb mark hchart
  refine ⟨law, ?_⟩
  intro first second attached
  have hh := protected_gaussian_marked_average cutoffScale parameter hscale hp
    (fun source => TrimmedSlice.orderedPairSlice (Parameters.modulus parameter) boundary (baseline - source) first second * attached source)
    (fun source => (if first = mark then 1 else 0) *
      (if second = paletteEmbedding parameter ((Parameters.modulus parameter : ℤ) - 1 + baseline - source - mark.val) then 1 else 0) * attached source)
  calc
    _ = ∑ input : V7Input cutoffScale parameter, (protectedGaussianLaw cutoffScale parameter).weight input *
        ((1 - if input = (windowZero _,windowZero _) then chartAtom (V7Input cutoffScale parameter) else 0) *
            (TrimmedSlice.orderedPairSlice (Parameters.modulus parameter) boundary (baseline - input.2) first second * attached input.2) +
          (if input = (windowZero _,windowZero _) then chartAtom (V7Input cutoffScale parameter) else 0) *
            ((if first = mark then 1 else 0) *
              (if second = paletteEmbedding parameter ((Parameters.modulus parameter : ℤ) - 1 + baseline - input.2 - mark.val) then 1 else 0) * attached input.2)) := by
      apply Finset.sum_congr rfl
      intro input _
      rw [hlaw]
      ring
    _ = _ := by simpa only [windowZero, sub_zero] using hh

end BoundaryCalibration
end
end AFT
