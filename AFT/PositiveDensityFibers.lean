import AFT.ChannelMixedFibers

/-! # Full and singleton fibers of a genuine positive finite mass -/
namespace AFT
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- A probability mass with density at most `D` has density squared integral
at most `D`, with no minimum atom or output-cardinality loss. -/
theorem positiveDensity_l2Sq_le {Output : Type*} [Fintype Output]
    (reference : FiniteDist Output) (mass : Output → ℝ) (bound : ℝ)
    (href : ∀ output,0 < reference.weight output) (hbound : 0 ≤ bound)
    (hmass : ∀ output,0 ≤ mass output) (htotal : (∑ output,mass output) ≤ 1)
    (hdensity : ∀ output,mass output ≤ bound*reference.weight output) :
    reference.l2Sq (fun output => mass output/reference.weight output) ≤ bound := by
  calc
    _ ≤ ∑ output,bound*mass output := by
      apply Finset.sum_le_sum
      intro output _
      have hd := (div_le_iff₀ (href output)).mpr (hdensity output)
      have hh := mul_le_mul_of_nonneg_left hd (hmass output)
      convert hh using 1 <;> field_simp
    _ ≤ bound := by
      rw [← Finset.mul_sum]
      exact (mul_le_mul_of_nonneg_left htotal hbound).trans_eq (mul_one _)

theorem positiveDensity_abs_le {Output : Type*} (reference mass : Output → ℝ) (bound : ℝ)
    (href : ∀ output,0 < reference output) (hmass : ∀ output,0 ≤ mass output)
    (hdensity : ∀ output,mass output ≤ bound*reference output) (output : Output) :
    |mass output/reference output| ≤ bound := by
  rw [abs_of_nonneg (div_nonneg (hmass output) (href output).le)]
  exact (div_le_iff₀ (href output)).mpr (hdensity output)

namespace MixedKernel
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color] [DecidableEq Slot]

/-- A genuine singleton positive marginal is enough for the sharp
one-fixed fiber bound of the full output density. -/
theorem positiveDensity_singleton_square_le (reference : Slot → FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (densityBound marginalBound : ℝ)
    (href : ∀ slot color,0 < (reference slot).weight color) (hD : 0 ≤ densityBound)
    (hmass : ∀ output,0 ≤ mass output)
    (hdensity : ∀ output,mass output ≤ densityBound*(FiniteDist.independent reference).weight output)
    (hmarginal : ∀ slot color,(∑ word,if word slot=color then mass word else 0) ≤
      marginalBound*(reference slot).weight color)
    (slot : Slot) (values : Slot → Color) :
    fiberSq reference (fun output => mass output/(FiniteDist.independent reference).weight output)
      {slot} values ≤ densityBound*marginalBound := by
  have hh := channelDensity_singleton_square_le (FiniteDist.uniform Unit) reference
    (fun _ output => mass output) densityBound marginalBound 1 href hD (by norm_num)
    (fun _ output => hmass output)
    (by intro output; simpa [FiniteDist.uniform] using hdensity output)
    (by intro fixed color; simpa [FiniteDist.uniform] using hmarginal fixed color)
    (fun _ => 1) (by intro point; norm_num) slot values
  unfold channelDensity at hh
  simpa [FiniteDist.uniform] using hh

end MixedKernel
end
end AFT
