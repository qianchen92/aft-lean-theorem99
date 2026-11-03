import CurrentAFT.CurrentFlagCoordinateEquiv
import AFT.ChartProgramHeight

/-! The correct marked array has fixed base and zero shear, with all line inputs exempted. -/

namespace CurrentAFT.CurrentFlagMarkedArray

open AFT AFT.BoundaryCalibration AffineFlagCalibration CurrentRationalFlagLaw
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 300000

variable {F I : Type*} [Field F] [Fintype F] [Fintype I]

def markedEmbedding (mark : F) : F ↪ Chart F where
  toFun scale := (mark, scale, 0)
  inj' _ _ h := congrArg (fun chart => chart.2.1) h

def fiber {charts : ℕ} (chartEquiv : Fin charts ≃ Chart F) (inputs : I → F × F)
    (allowed : I → Finset F) (mark : F) : Finset (Fin charts) :=
  ((markedScaleSet inputs allowed mark).map (markedEmbedding mark)).map chartEquiv.symm.toEmbedding

omit [Fintype I] in
theorem fiber_card {charts : ℕ} (chartEquiv : Fin charts ≃ Chart F) (inputs : I → F × F)
    (allowed : I → Finset F) (mark : F) :
    (fiber chartEquiv inputs allowed mark).card = (markedScaleSet inputs allowed mark).card := by
  simp only [fiber, Finset.card_map]

omit [Fintype I] in
theorem mem_fiber {charts : ℕ} (chartEquiv : Fin charts ≃ Chart F) (inputs : I → F × F)
    (allowed : I → Finset F) (mark : F) (point : Fin charts) :
    point ∈ fiber chartEquiv inputs allowed mark ↔
      (chartEquiv point).1 = mark ∧ (chartEquiv point).2.2 = 0 ∧
        markedScaleSafe inputs allowed mark (chartEquiv point).2.1 := by
  constructor
  · intro hm
    rcases Finset.mem_map.mp hm with ⟨chart, hchart, hpoint⟩
    rcases Finset.mem_map.mp hchart with ⟨scale, hs, he⟩
    have hc : chartEquiv point = (mark, scale, 0) := by
      rw [← hpoint, Equiv.toEmbedding_apply, Equiv.apply_symm_apply, ← he]
      rfl
    rw [hc]
    exact ⟨rfl, rfl, (Finset.mem_filter.mp hs).2⟩
  · rintro ⟨hb, hh, hs⟩
    apply Finset.mem_map.mpr
    refine ⟨chartEquiv point, ?_, chartEquiv.symm_apply_apply point⟩
    apply Finset.mem_map.mpr
    refine ⟨(chartEquiv point).2.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩, ?_⟩
    apply Prod.ext
    · exact hb.symm
    · exact Prod.ext rfl hh.symm

omit [Fintype I] in
theorem spike_eq {charts : ℕ} (chartEquiv : Fin charts ≃ Chart F) (inputs : I → F × F)
    (allowed : I → Finset F) (mark : F) (point : Fin charts) :
    chartSpikeProgram charts (fiber chartEquiv inputs allowed mark) point =
      markedDensityQ inputs allowed mark (chartEquiv point) := by
  have hc : charts = Fintype.card F ^ 3 := by
    have hh := Fintype.card_congr chartEquiv
    simpa only [Fintype.card_fin, Chart, Fintype.card_prod, pow_succ, pow_zero, one_mul, mul_assoc] using hh
  have hcast : (charts : ℚ) = (Fintype.card F : ℚ) ^ 3 := by exact_mod_cast hc
  rw [chartSpikeProgram, fiber_card]
  have hm := mem_fiber chartEquiv inputs allowed mark point
  simp only [markedDensityQ, markedSurvivalQ]
  by_cases hs : (chartEquiv point).1 = mark ∧ (chartEquiv point).2.2 = 0 ∧
      markedScaleSafe inputs allowed mark (chartEquiv point).2.1
  · rw [if_pos (hm.mpr hs), if_pos hs, mul_one, hcast, div_div_eq_mul_div]
    ring
  · rw [if_neg (fun h => hs (hm.mp h)), if_neg hs, mul_zero]

local instance markedArrayPrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩

theorem current_table (security : ℕ) (baseline : ℤ)
    (hbaseline : |baseline| ≤ legOffsetBound security) (mark : ZMod (Parameters.modulus security))
    (atom : ℚ) (ha0 : 0 ≤ (atom : ℝ)) (haHalf : (atom : ℝ) ≤ 1 / 2) :
    (CurrentFlagProgram.current security baseline hbaseline mark atom ha0 haHalf).table =
      CurrentFlagProgram.table
        (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security))
        (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline)
        mark atom := by
  rw [CurrentFlagProgram.current, CurrentFlagProgram.make]

end
end CurrentAFT.CurrentFlagMarkedArray
