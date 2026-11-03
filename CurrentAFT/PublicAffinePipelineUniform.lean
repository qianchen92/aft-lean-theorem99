import CurrentAFT.PublicAffinePipelineLaw

/-! Exact public-input uniformity for every executed binary output, including
all fallback branches. The whole random tape is independent of the source. -/
namespace CurrentAFT.PublicAffinePipeline
open AFT
open scoped Classical
noncomputable section
local instance uniformFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentProposalDimensions.current CurrentEmissionMetadata.current run
  PublicParameterProgram.modulus PublicBitTapes.current

local instance modulusNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩

def runData (security order : ℕ) (producer : Producer security order) (word : PublicBitTapes.Tapes security) :
    CurrentAffineData.Data security where
  matrix := CurrentBinaryAffineEmitter.matrix security (run security order producer word)
  offset := CurrentBinaryAffineEmitter.offset security (run security order producer word)
  invertible := run_invertible security order producer word

def fairData (security order : ℕ) (producer : Producer security order)
    (word : Fin (PublicBitTapes.current security).bits → Fin 2) : CurrentAffineData.Data security :=
  runData security order producer ((PublicBitTapes.current security).equiv word)

theorem fairData_matrix (security order : ℕ) (producer : Producer security order)
    (word : Fin (PublicBitTapes.current security).bits → Fin 2) :
    (fairData security order producer word).matrix =
      CurrentBinaryAffineEmitter.matrix security (fairBitRun security order producer word) := rfl

theorem fairData_offset (security order : ℕ) (producer : Producer security order)
    (word : Fin (PublicBitTapes.current security).bits → Fin 2) :
    (fairData security order producer word).offset =
      CurrentBinaryAffineEmitter.offset security (fairBitRun security order producer word) := rfl

theorem public_matrix_error_independent (security order columns : ℕ) (producer : Producer security order)
    (source : FiniteDist (ModularCoordinates (Parameters.dimension security) (Parameters.modulus security))) :
    ((FiniteDist.uniform (Fin (PublicBitTapes.current security).bits → Fin 2)).prod source).mix (fun draw =>
      (FiniteDist.uniform (Fin columns → ModularCoordinates (Parameters.dimension security) (Parameters.modulus security))).map
        (fun matrix => (((fairData security order producer draw.1).reduced).columnsEquiv (Fin columns) matrix,
          ((fairData security order producer draw.1).reduced).eval draw.2))) =
      (FiniteDist.uniform (Fin columns → ModularCoordinates (Parameters.dimension security) (Parameters.modulus security))).prod
        (transportedLaw (FiniteDist.uniform (Fin (PublicBitTapes.current security).bits → Fin 2))
          (fun word => (fairData security order producer word).reduced) source) :=
  modular_public_matrix_error_independent (Parameters.dimension security) columns (Parameters.modulus security)
    (FiniteDist.uniform (Fin (PublicBitTapes.current security).bits → Fin 2))
    (fun word => (fairData security order producer word).reduced) source

theorem ideal_response_preserved (security order columns : ℕ) (producer : Producer security order) :
    (FiniteDist.uniform (Fin (PublicBitTapes.current security).bits → Fin 2)).mix (fun word =>
      ((FiniteDist.uniform (Fin columns → ModularCoordinates (Parameters.dimension security) (Parameters.modulus security))).prod
        (FiniteDist.uniform (ModularCoordinates (Parameters.dimension security) (Parameters.modulus security)))).map
          ((((fairData security order producer word).reduced).columnsEquiv (Fin columns)).prodCongr
            ((fairData security order producer word).reduced).equiv)) =
      (FiniteDist.uniform (Fin columns → ModularCoordinates (Parameters.dimension security) (Parameters.modulus security))).prod
        (FiniteDist.uniform (ModularCoordinates (Parameters.dimension security) (Parameters.modulus security))) :=
  modular_ideal_response_preserved (Parameters.dimension security) columns (Parameters.modulus security)
    (FiniteDist.uniform (Fin (PublicBitTapes.current security).bits → Fin 2))
    (fun word => (fairData security order producer word).reduced)

end
end CurrentAFT.PublicAffinePipeline
