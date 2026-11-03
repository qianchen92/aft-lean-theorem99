import CurrentAFT.PublicAffinePipeline
import CurrentAFT.CurrentBinaryEmitterPolynomial

namespace CurrentAFT.PublicAffinePipeline
open AFT BinaryArithmetic RationalRejectionProgram
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentBinaryAffineEmitter.emit CurrentMaterializedCompletion.current CurrentLayoutDraw.draw

def workPolynomial (order : ℕ) (producerWork tableHeight : Polynomial ℕ) : Polynomial ℕ :=
  CurrentLayoutDraw.workPolynomial Polynomial.X + producerWork +
    CurrentMaterializedCompletion.workPolynomial order tableHeight +
    CurrentBinaryEmitterPolynomial.workPolynomial+5

theorem polynomial_work (security order : ℕ) (producer : Producer security order)
    (producerWork tableHeight : Polynomial ℕ)
    (hp : ∀ layout, (producer layout).work ≤ producerWork.eval security)
    (ht : ∀ layout block point, RationalNumerics.HeightBound
      (((producer layout).value.get block).get point).decode (tableHeight.eval security))
    (word : PublicBitTapes.Tapes security) :
    (run security order producer word).work ≤ (workPolynomial order producerWork tableHeight).eval security := by
  let layout := (CurrentLayoutDraw.draw security security word.1).value
  have hl := CurrentLayoutDraw.polynomial_work security Polynomial.X
  rw [Polynomial.eval_X] at hl
  have hl := hl word.1
  have hs := CurrentMaterializedCompletion.polynomial_work security order tableHeight (producer layout).value
    (ht layout) word.2
  have he := CurrentBinaryEmitterPolynomial.polynomial_work security layout
    (CurrentMaterializedCompletion.current security order (producer layout).value word.2).value
  have hp := hp layout
  change (CurrentLayoutDraw.draw security security word.1).work+2+
    ((producer layout).work+(CurrentMaterializedCompletion.current security order (producer layout).value word.2).work+
      (CurrentBinaryAffineEmitter.emit security layout
        (CurrentMaterializedCompletion.current security order (producer layout).value word.2).value).work+3) ≤ _
  simp only [workPolynomial, Polynomial.eval_add, Polynomial.eval_ofNat]
  omega


end
end CurrentAFT.PublicAffinePipeline
