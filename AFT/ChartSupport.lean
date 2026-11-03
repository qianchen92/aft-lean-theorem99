import AFT.PublicChartGaussian

/-! # The same positive affine chart has its exact response and legal support -/
namespace AFT.BoundaryCalibration
open GaussianSource Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
local instance supportedChartFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance supportedChartFieldDecEq (n : ℕ) : DecidableEq (ZMod (Parameters.modulus n)) := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- Every nonzero chart has nonzero scale. Its only possible untrimmed
feature is the designated mark at the zero protected input. -/
def ProtectedChartSupport (C : ℝ) (n : ℕ) (boundary baseline : ℤ)
    (mark : Fin (Parameters.modulus n)) (law : FiniteDist (Chart (ZMod (Parameters.modulus n)))) : Prop :=
  ∀ chart, law.weight chart ≠ 0 → chart.2.1 ≠ 0 ∧
    ∀ input : V7Input C n,
      feature ((input.1 : ℤ) : ZMod (Parameters.modulus n)) ((input.2 : ℤ) : ZMod (Parameters.modulus n)) chart ∈
          v7ProtectedPalettes C n boundary baseline input ∨
      (input = (windowZero _,windowZero _) ∧
        feature ((input.1 : ℤ) : ZMod (Parameters.modulus n)) ((input.2 : ℤ) : ZMod (Parameters.modulus n)) chart =
          (ZMod.finEquiv (Parameters.modulus n)) mark)

theorem protectedChartSupport_of_mixture (C : ℝ) (n : ℕ) (boundary baseline : ℤ)
    (mark : Fin (Parameters.modulus n))
    (interior spike law : FiniteDist (Chart (ZMod (Parameters.modulus n))))
    (hmix : ∀ chart,law.weight chart=(1-chartAtom (V7Input C n))*interior.weight chart+
      chartAtom (V7Input C n)*spike.weight chart)
    (hinterior : ∀ chart,¬(chart.2.1 ≠ 0 ∧ ∀ input : V7Input C n,
      feature ((input.1 : ℤ) : ZMod (Parameters.modulus n)) ((input.2 : ℤ) : ZMod (Parameters.modulus n)) chart ∈
        v7ProtectedPalettes C n boundary baseline input) → interior.weight chart=0)
    (hspike : ∀ chart,¬(feature 0 0 chart=(ZMod.finEquiv (Parameters.modulus n)) mark ∧ chart.2.1 ≠ 0 ∧
      ∀ input : V7Input C n,input ≠ (windowZero _,windowZero _) →
        feature ((input.1 : ℤ) : ZMod (Parameters.modulus n)) ((input.2 : ℤ) : ZMod (Parameters.modulus n)) chart ∈
          v7ProtectedPalettes C n boundary baseline input) → spike.weight chart=0) :
    ProtectedChartSupport C n boundary baseline mark law := by
  intro chart hnonzero
  by_cases hi : interior.weight chart ≠ 0
  · have hs := of_not_not (fun hn => hi (hinterior chart hn))
    exact ⟨hs.1,fun input => Or.inl (hs.2 input)⟩
  · have hs : spike.weight chart ≠ 0 := by
      intro hz
      apply hnonzero
      rw [hmix,not_not.mp hi,hz]
      ring
    have hh := of_not_not (fun hn => hs (hspike chart hn))
    refine ⟨hh.2.1,fun input => ?_⟩
    by_cases hz : input=(windowZero _,windowZero _)
    · right
      refine ⟨hz,?_⟩
      simpa only [hz,windowZero,Int.cast_zero] using hh.1
    · exact Or.inl (hh.2.2 input hz)

theorem chart_joint_output_supported (cutoffScale : ℝ) (parameter : ℕ) (boundary baseline : ℤ)
    (hb : 0 ≤ boundary) (mark : Fin (Parameters.modulus parameter))
    (hchart : V7ChartExists cutoffScale parameter boundary baseline
      ((ZMod.finEquiv (Parameters.modulus parameter)) mark)) :
    ∃ chartLaw : FiniteDist (Chart (ZMod (Parameters.modulus parameter))),
      ProtectedChartSupport cutoffScale parameter boundary baseline mark chartLaw ∧
      ∀ input : V7Input cutoffScale parameter, ∀ first second : Fin (Parameters.modulus parameter),
      (chartPairOutput cutoffScale parameter baseline chartLaw input).weight (first,second) =
        (1 - if input = (windowZero _,windowZero _) then chartAtom (V7Input cutoffScale parameter) else 0) *
          TrimmedSlice.orderedPairSlice (Parameters.modulus parameter) boundary (baseline - input.2) first second +
        (if input = (windowZero _,windowZero _) then chartAtom (V7Input cutoffScale parameter) else 0) *
          (if first = mark then 1 else 0) *
          (if second = paletteEmbedding parameter ((Parameters.modulus parameter : ℤ) - 1 + baseline - input.2 - mark.val) then 1 else 0) := by
  obtain ⟨interior, spike, law, hmix, hinterior, hspike, hzero, hnonzero⟩ := hchart
  refine ⟨law, ?_, ?_⟩
  · apply protectedChartSupport_of_mixture cutoffScale parameter boundary baseline mark interior spike law hmix hinterior
    simpa only [protectedInputs,windowZero,Int.cast_zero] using hspike
  intro input first second
  rw [chartPairOutput, FiniteDist.graph_weight, chartPaletteFeature_weight]
  have hmark : (ZMod.finEquiv (Parameters.modulus parameter)) first =
      (ZMod.finEquiv (Parameters.modulus parameter)) mark ↔ first = mark :=
    (ZMod.finEquiv (Parameters.modulus parameter)).injective.eq_iff
  have hunif : (if (ZMod.finEquiv (Parameters.modulus parameter)) first ∈
      v7ProtectedPalettes cutoffScale parameter boundary baseline input then
        ((v7ProtectedPalettes cutoffScale parameter boundary baseline input).card : ℝ)⁻¹ else 0) =
      TrimmedSlice.law (Parameters.modulus parameter) boundary (baseline - input.2) first.val :=
    fieldPalette_uniform parameter boundary (baseline - input.2) hb first
  have hshift : (Parameters.modulus parameter : ℤ) - 1 + baseline - input.2 - first.val =
      (Parameters.modulus parameter : ℤ) - 1 + (baseline - input.2) - first.val := by ring
  by_cases hi : input = (windowZero _,windowZero _)
  · subst input
    have hz := hzero ((ZMod.finEquiv (Parameters.modulus parameter)) first)
    dsimp only [protectedInputs] at hz
    rw [hz, hunif]
    simp only [hmark, if_true, add_mul, mul_assoc]
    rw [hshift, slice_companion_graph parameter boundary _ hb]
    by_cases hf : first = mark
    · subst first
      simp only [if_true, hshift]
    · simp only [if_neg hf, mul_zero, zero_mul, add_zero]
  · have hn := hnonzero input hi ((ZMod.finEquiv (Parameters.modulus parameter)) first)
    dsimp only [protectedInputs] at hn
    rw [hn, hunif, if_neg hi]
    simp only [sub_zero, one_mul, zero_mul, add_zero]
    rw [hshift]
    exact slice_companion_graph parameter boundary _ hb first second

end
end AFT.BoundaryCalibration
