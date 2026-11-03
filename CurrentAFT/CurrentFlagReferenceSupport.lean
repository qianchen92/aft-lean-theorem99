import CurrentAFT.CurrentFlagIdealArrays

/-! The exact branch laws are supported on their generated public masks. -/

namespace CurrentAFT.CurrentFlagReferenceSupport

open AFT AFT.BoundaryCalibration AFT.BinaryArithmetic AffineFlagCalibration CurrentRationalFlagLaw
open CurrentFlagIdealArrays CurrentFlagBinaryMetadata CurrentFlagFiniteCoordinates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 400000

local instance referenceSupportPrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩
local instance referenceSupportNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩

theorem regular_support (security : ℕ) (baselineSign : Bool) (baseline : List Bool)
    (hbaseline : |signedValue baselineSign baseline| ≤ legOffsetBound security)
    (mark : Fin (Parameters.modulus security))
    (point : Fin (Parameters.modulus security * (Parameters.modulus security * Parameters.modulus security)))
    (hnot : point ∉ maskSet (build (Parameters.sourceCutoff security - 1) (Parameters.modulus security)
      false baselineSign [true] baseline mark).value.safe) :
    (regularLaw security (signedValue baselineSign baseline) hbaseline mark).weight point = 0 := by
  rw [regularLaw, FiniteDist.map_equiv_weight]
  simp only [Equiv.symm_symm]
  apply (model security (signedValue baselineSign baseline) hbaseline mark).model.regular_support
  intro hs
  have hs' : affineSafe (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security))
      (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1
        (signedValue baselineSign baseline)) (finiteChartEquiv (Parameters.modulus security) point) := by
    simpa only [affineSafe, legalChart, affineFeatures, Finset.mem_erase, Finset.mem_univ, and_true] using hs
  have hm := (safe_equiv (Parameters.sourceCutoff security - 1) (Parameters.modulus security)
    (signedValue baselineSign baseline) point).mpr hs'
  have hb := (build_safe (Parameters.sourceCutoff security - 1) (Parameters.modulus security)
    false baselineSign [true] baseline mark point).mpr
      (by simpa only [CurrentFlagMetadataSemantics.boundary_one] using hm)
  exact hnot (by simpa only [maskSet, Finset.mem_filter, Finset.mem_univ, true_and] using hb)

theorem marked_support (security : ℕ) (baselineSign : Bool) (baseline : List Bool)
    (hbaseline : |signedValue baselineSign baseline| ≤ legOffsetBound security)
    (mark : Fin (Parameters.modulus security))
    (point : Fin (Parameters.modulus security * (Parameters.modulus security * Parameters.modulus security)))
    (hnot : point ∉ maskSet (build (Parameters.sourceCutoff security - 1) (Parameters.modulus security)
      false baselineSign [true] baseline mark).value.fiber) :
    (markedLaw security (signedValue baselineSign baseline) hbaseline mark).weight point = 0 := by
  rw [CurrentFlagMetadataSemantics.fiber_exact _ _ (leg_input_separation security)] at hnot
  rw [marked_weight, chartSpikeProgram, if_neg hnot, Rat.cast_zero, zero_div]

end
end CurrentAFT.CurrentFlagReferenceSupport
