import CurrentAFT.CurrentBinaryEmitterSemantic
import CurrentAFT.PublicBitResources

/-! Composition of the table producer with the executed public sampler and
integer emitter. Placement is sampled once, before calibration and rejection.
The producer's resource and approximation obligations are explicit here. -/
namespace CurrentAFT.PublicAffinePipeline
open AFT BinaryArithmetic RationalRejectionProgram
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentBinaryAffineEmitter.emit CurrentMaterializedCompletion.current CurrentLayoutDraw.draw

abbrev Table (security order : ℕ) := BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order
abbrev Producer (security order : ℕ) := CurrentLayoutDraw.Cache security → CountedValue (Table security order)

def addWork (security extra : ℕ) (data : CurrentBinaryAffineEmitter.Data security) :
    CurrentBinaryAffineEmitter.Data security := ⟨data.columns, data.offset, extra+data.work⟩

def forLayout (security order : ℕ) (producer : Producer security order)
    (layout : CurrentLayoutDraw.Cache security) (word : CurrentMaterializedCompletion.Tapes security) :
    CurrentBinaryAffineEmitter.Data security :=
  let table := producer layout
  let sample := CurrentMaterializedCompletion.current security order table.value word
  let result := CurrentBinaryAffineEmitter.emit security layout sample.value
  ⟨result.columns, result.offset, table.work+sample.work+result.work+3⟩

def run (security order : ℕ) (producer : Producer security order) (word : PublicBitTapes.Tapes security) :
    CurrentBinaryAffineEmitter.Data security :=
  let layout := CurrentLayoutDraw.draw security security word.1
  let result := forLayout security order producer layout.value word.2
  addWork security (layout.work+2) result

def fairBitRun (security order : ℕ) (producer : Producer security order)
    (word : Fin (PublicBitTapes.current security).bits → Fin 2) : CurrentBinaryAffineEmitter.Data security :=
  run security order producer ((PublicBitTapes.current security).equiv word)

noncomputable section
open scoped Classical

theorem addWork_matrix (security extra : ℕ) (data : CurrentBinaryAffineEmitter.Data security) :
    CurrentBinaryAffineEmitter.matrix security (addWork security extra data) =
      CurrentBinaryAffineEmitter.matrix security data := rfl

theorem addWork_offset (security extra : ℕ) (data : CurrentBinaryAffineEmitter.Data security) :
    CurrentBinaryAffineEmitter.offset security (addWork security extra data) =
      CurrentBinaryAffineEmitter.offset security data := rfl

theorem forLayout_matrix (security order : ℕ) (producer : Producer security order)
    (layout : CurrentLayoutDraw.Cache security) (word : CurrentMaterializedCompletion.Tapes security) :
    CurrentBinaryAffineEmitter.matrix security (forLayout security order producer layout word) =
      (NumericalAffineTransport.realizeResult security layout.layout
        ((CurrentMaterializedCompletion.current security order (producer layout).value word).value.map
          CurrentMaterializedCompletion.Result.sample)).matrix :=
  CurrentBinaryEmitterSemantic.emit_matrix security layout _

theorem forLayout_offset (security order : ℕ) (producer : Producer security order)
    (layout : CurrentLayoutDraw.Cache security) (word : CurrentMaterializedCompletion.Tapes security) :
    CurrentBinaryAffineEmitter.offset security (forLayout security order producer layout word) =
      (NumericalAffineTransport.realizeResult security layout.layout
        ((CurrentMaterializedCompletion.current security order (producer layout).value word).value.map
          CurrentMaterializedCompletion.Result.sample)).offset :=
  CurrentBinaryEmitterSemantic.emit_offset security layout _

theorem forLayout_invertible (security order : ℕ) (producer : Producer security order)
    (layout : CurrentLayoutDraw.Cache security) (word : CurrentMaterializedCompletion.Tapes security) :
    IsUnit ((CurrentBinaryAffineEmitter.matrix security (forLayout security order producer layout word)).map
      (Int.castRingHom (ZMod (Parameters.modulus security)))) := by
  rw [forLayout_matrix]
  exact NumericalAffineTransport.every_result_invertible security layout.layout _

theorem run_invertible (security order : ℕ) (producer : Producer security order)
    (word : PublicBitTapes.Tapes security) :
    IsUnit ((CurrentBinaryAffineEmitter.matrix security (run security order producer word)).map
      (Int.castRingHom (ZMod (Parameters.modulus security)))) := by
  rw [run, addWork_matrix]
  exact forLayout_invertible security order producer _ word.2

def forLayoutData (security order : ℕ) (producer : Producer security order)
    (layout : CurrentLayoutDraw.Cache security) (word : CurrentMaterializedCompletion.Tapes security) :
    CurrentAffineData.Data security where
  matrix := CurrentBinaryAffineEmitter.matrix security (forLayout security order producer layout word)
  offset := CurrentBinaryAffineEmitter.offset security (forLayout security order producer layout word)
  invertible := forLayout_invertible security order producer layout word

theorem forLayoutData_eq (security order : ℕ) (producer : Producer security order)
    (layout : CurrentLayoutDraw.Cache security) (word : CurrentMaterializedCompletion.Tapes security) :
    forLayoutData security order producer layout word =
      NumericalAffineTransport.realizeResult security layout.layout
        ((CurrentMaterializedCompletion.current security order (producer layout).value word).value.map
          CurrentMaterializedCompletion.Result.sample) := by
  cases h : NumericalAffineTransport.realizeResult security layout.layout
    ((CurrentMaterializedCompletion.current security order (producer layout).value word).value.map
      CurrentMaterializedCompletion.Result.sample) with
  | mk matrix offset invertible =>
    have hm := forLayout_matrix security order producer layout word
    have ho := forLayout_offset security order producer layout word
    rw [h] at hm ho
    unfold forLayoutData
    simp only [hm, ho]

end
end CurrentAFT.PublicAffinePipeline
