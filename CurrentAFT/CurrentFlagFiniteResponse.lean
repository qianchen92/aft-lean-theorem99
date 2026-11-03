import CurrentAFT.CurrentFlagMarkedArray
import CurrentAFT.CurrentFlagCompletion
import AFT.FiniteAffineFeatures

/-!
# Actual finite-coordinate flag response

These arrays use the current protected inputs, the full affine chart,
the two prescribed trimmed palettes, and the exact marked scale fiber.
Coordinate changes preserve the canonical rational inverse exactly.
-/

namespace CurrentAFT.CurrentFlagFiniteResponse

open AFT AFT.BoundaryCalibration AffineFlagCalibration CurrentRationalFlagLaw
open CurrentFlagIteration CurrentFlagReindex CurrentFlagMarkedArray
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 400000

variable {F I : Type*} [Field F] [Fintype F] [Fintype I]

def finiteRegular {charts colors inputsCount : ℕ}
    (chartEquiv : Fin charts ≃ Chart F) (colorEquiv : Fin colors ≃ F) (inputEquiv : Fin inputsCount ≃ I)
    (inputs : I → F × F) (allowed : I → Finset F) (mark : F) (atom : ℚ) (steps : ℕ) : Fin charts → ℚ :=
  regularIterate
    (fun index point => colorEquiv.symm (feature (inputs (inputEquiv index)).1
      (inputs (inputEquiv index)).2 (chartEquiv point)))
    (fun index => (allowed (inputEquiv index)).map colorEquiv.symm.toEmbedding)
    (fun index => (inputs (inputEquiv index)).1 = 0)
    (fun point => affineSafe inputs allowed (chartEquiv point)) atom
    (chartSpikeProgram charts (fiber chartEquiv inputs allowed mark)) steps

theorem finiteRegular_eq {charts colors inputsCount : ℕ}
    (chartEquiv : Fin charts ≃ Chart F) (colorEquiv : Fin colors ≃ F) (inputEquiv : Fin inputsCount ≃ I)
    (inputs : I → F × F) (allowed : I → Finset F) (mark : F) (atom : ℚ) (steps : ℕ) :
    finiteRegular chartEquiv colorEquiv inputEquiv inputs allowed mark atom steps =
      regularIterate (affineFeatures inputs) allowed (fun index => (inputs index).1 = 0)
        (affineSafe inputs allowed) atom (markedDensityQ inputs allowed mark) steps ∘ chartEquiv := by
  have hs : chartSpikeProgram charts (fiber chartEquiv inputs allowed mark) =
      markedDensityQ inputs allowed mark ∘ chartEquiv := funext (spike_eq chartEquiv inputs allowed mark)
  unfold finiteRegular
  rw [hs]
  change regularIterate
    ((fun index => colorEquiv.symm ∘ (affineFeatures inputs index ∘ chartEquiv)) ∘ inputEquiv)
    ((fun index => (allowed index).map colorEquiv.symm.toEmbedding) ∘ inputEquiv)
    ((fun index => (inputs index).1 = 0) ∘ inputEquiv)
    (affineSafe inputs allowed ∘ chartEquiv) atom (markedDensityQ inputs allowed mark ∘ chartEquiv) steps = _
  rw [regular_input inputEquiv, regular_color colorEquiv,
    regular_reindex chartEquiv]

local instance finiteResponseZModDecidableEq (security : ℕ) : DecidableEq (ZMod (Parameters.modulus security)) :=
  Classical.decEq _
local instance finiteResponsePrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩
local instance finiteResponseNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩

def currentRegular (security : ℕ) (baseline : ℤ) (mark : ZMod (Parameters.modulus security))
    (atom : ℚ) (steps : ℕ) : Fin (Parameters.modulus security *
      (Parameters.modulus security * Parameters.modulus security)) → ℚ :=
  finiteRegular (finiteChartEquiv (Parameters.modulus security))
    (ZMod.finEquiv (Parameters.modulus security)).toEquiv
    (finiteInputEquiv (Parameters.sourceCutoff security - 1))
    (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security))
    (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline)
    mark atom steps

theorem currentRegular_error (security : ℕ) (baseline : ℤ)
    (hbaseline : |baseline| ≤ legOffsetBound security) (mark : ZMod (Parameters.modulus security))
    (atom : ℚ) (steps : ℕ)
    (point : Fin (Parameters.modulus security * (Parameters.modulus security * Parameters.modulus security))) :
    |(currentRegular security baseline mark atom steps point : ℝ) -
      (CurrentFlagProgram.regularDensity
        (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security))
        (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline)
        mark atom (finiteChartEquiv (Parameters.modulus security) point) : ℝ)| ≤
      (1 / 4 : ℝ) ^ steps * ((4 / 3) *
        ‖realVector (1 - (atom / (1 - atom)) • offLineDefectQ
          (affineFeatures (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security)))
          (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline)
          (fun index => (protectedInputs (Parameters.sourceCutoff security - 1)
            (Parameters.modulus security) index).1 = 0)
          (markedDensityQ (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security))
            (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline) mark))‖) := by
  unfold currentRegular
  rw [finiteRegular_eq]
  simpa only [Function.comp_apply, CurrentFlagProgram.regularDensity] using regularIterate_error
    (affineFeatures (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security)))
    (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline)
    (fun index => (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security) index).1 = 0)
    (affineSafe (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security))
      (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline))
    atom (markedDensityQ (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security))
      (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline) mark)
    (current_quarter security baseline hbaseline) steps (finiteChartEquiv (Parameters.modulus security) point)

end
end CurrentAFT.CurrentFlagFiniteResponse
