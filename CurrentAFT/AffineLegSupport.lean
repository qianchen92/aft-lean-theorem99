import CurrentAFT.AffineLegLaw

/-! # Pointwise flag and support guarantees of the complete public law -/

namespace CurrentAFT.AffineFlagCalibration

open AFT AFT.BoundaryCalibration
open scoped Classical

noncomputable section

variable {F I : Type*} [Field F] [Fintype F] [Fintype I]
variable {inputs : I → F × F} {allowed : I → Finset F} {mark : F} {atom : ℝ}

theorem SimultaneousLaw.regular_of_supported (model : SimultaneousLaw inputs allowed mark atom)
    (chart : Chart F) (hweight : model.joint.weight (false, chart) ≠ 0) :
    chart.2.1 ≠ 0 ∧ ∀ i, feature (inputs i).1 (inputs i).2 chart ∈ allowed i := by
  by_contra hn
  apply hweight
  rw [model.decomposition, model.regular_support chart hn]
  simp

theorem SimultaneousLaw.marked_of_supported (model : SimultaneousLaw inputs allowed mark atom)
    (chart : Chart F) (hweight : model.joint.weight (true, chart) ≠ 0) :
    chart.1 = mark ∧ chart.2.2 = 0 ∧ chart.2.1 ≠ 0 ∧
      ∀ i, (inputs i).1 ≠ 0 → feature (inputs i).1 (inputs i).2 chart ∈ allowed i := by
  by_contra hn
  apply hweight
  rw [model.decomposition, model.marked_support chart hn]
  simp

theorem SimultaneousLaw.supported_scale (model : SimultaneousLaw inputs allowed mark atom)
    (point : Bool × Chart F) (hweight : model.joint.weight point ≠ 0) : point.2.2.1 ≠ 0 := by
  rcases point with ⟨flag, chart⟩
  cases flag
  · exact (model.regular_of_supported chart hweight).1
  · exact (model.marked_of_supported chart hweight).2.2.1

theorem SimultaneousLaw.supported_off_line (model : SimultaneousLaw inputs allowed mark atom)
    (point : Bool × Chart F) (hweight : model.joint.weight point ≠ 0)
    (i : I) (hi : (inputs i).1 ≠ 0) : feature (inputs i).1 (inputs i).2 point.2 ∈ allowed i := by
  rcases point with ⟨flag, chart⟩
  cases flag
  · exact (model.regular_of_supported chart hweight).2 i
  · exact (model.marked_of_supported chart hweight).2.2.2 i hi

theorem SimultaneousLaw.marked_on_line (model : SimultaneousLaw inputs allowed mark atom)
    (chart : Chart F) (hweight : model.joint.weight (true, chart) ≠ 0)
    (i : I) (hi : (inputs i).1 = 0) : feature (inputs i).1 (inputs i).2 chart = mark := by
  obtain ⟨hbase, hshear, _, _⟩ := model.marked_of_supported chart hweight
  simp only [feature, hi, hshear, mul_zero, zero_mul, add_zero, hbase]

end
end CurrentAFT.AffineFlagCalibration
