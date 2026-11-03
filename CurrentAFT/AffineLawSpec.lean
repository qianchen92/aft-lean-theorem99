import CurrentAFT.AffineFlagLaw

/-! # The simultaneous public flag and affine-map specification -/
namespace CurrentAFT.AffineFlagCalibration
open AFT AFT.BoundaryCalibration
open scoped BigOperators Classical
noncomputable section

structure SimultaneousLaw {F I : Type*} [Field F] [Fintype F] [Fintype I]
    (inputs : I → F × F) (allowed : I → Finset F) (mark : F) (atom : ℝ) where
  regular : FiniteDist (Chart F)
  marked : FiniteDist (Chart F)
  joint : FiniteDist (Bool × Chart F)
  decomposition : ∀ point, joint.weight point = if point.1 then atom * marked.weight point.2
    else (1 - atom) * regular.weight point.2
  regular_support : ∀ chart, ¬ (chart.2.1 ≠ 0 ∧
    ∀ i, feature (inputs i).1 (inputs i).2 chart ∈ allowed i) → regular.weight chart = 0
  regular_lower : ∀ chart, chart.2.1 ≠ 0 →
    (∀ i, feature (inputs i).1 (inputs i).2 chart ∈ allowed i) →
    (Fintype.card (Chart F) : ℝ)⁻¹ / 3 ≤ regular.weight chart
  marked_support : ∀ chart, ¬ (chart.1 = mark ∧ chart.2.2 = 0 ∧ chart.2.1 ≠ 0 ∧
    ∀ i, (inputs i).1 ≠ 0 → feature (inputs i).1 (inputs i).2 chart ∈ allowed i) →
    marked.weight chart = 0
  flag_marginal : ∀ flag, (joint.map Prod.fst).weight flag = if flag then atom else 1 - atom
  on_line : ∀ i, (inputs i).1 = 0 → ∀ c,
    (joint.map (fun point => feature (inputs i).1 (inputs i).2 point.2)).weight c =
      (1 - atom) * (if c ∈ allowed i then ((allowed i).card : ℝ)⁻¹ else 0) +
        atom * (if c = mark then 1 else 0)
  off_line : ∀ i, (inputs i).1 ≠ 0 → ∀ c,
    (joint.map (fun point => feature (inputs i).1 (inputs i).2 point.2)).weight c =
      if c ∈ allowed i then ((allowed i).card : ℝ)⁻¹ else 0

end
end CurrentAFT.AffineFlagCalibration
