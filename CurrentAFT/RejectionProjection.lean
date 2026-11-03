import CurrentAFT.BinaryArrayRejection

/-! Deterministic decoding of the actual binary rejection loop. -/
namespace CurrentAFT.RejectionProjection
open AFT BinaryArithmetic RationalRejectionProgram
set_option maxHeartbeats 400000
variable {State Output Tape : Type*}

theorem map_run (decode : State → Output) (fallback : State) (attempts : ℕ)
    (proposals : Fin attempts → State × Fin 2) :
    decode (RationalRejectionProgram.run fallback attempts proposals) =
      RationalRejectionProgram.run (decode fallback) attempts
        (fun index => (decode (proposals index).1, (proposals index).2)) := by
  induction attempts with
  | zero => rfl
  | succ attempts ih =>
    simp only [RationalRejectionProgram.run]
    split_ifs
    · rfl
    · exact ih (fun index => proposals index.succ)

theorem array_value [Inhabited Tape] (decode : State → Output) (sample : Tape → CountedValue State)
    (score : State → CountedValue RationalBits) (targetScore : Output → ℚ)
    (hscore : ∀ state, (score state).value.decode = targetScore (decode state))
    (envelope : RationalBits) (envelopeValue bits : ℕ) (he : envelope.decode = (envelopeValue : ℚ))
    (fallback : CountedValue State) (attempts : ℕ) (words : Vector (Tape × (Fin bits → Fin 2)) attempts) :
    decode (BinaryArrayRejection.run sample score envelope bits fallback attempts words).value =
      RationalRejectionProgram.positiveDraw (fun input => decode (sample input).value) targetScore
        envelopeValue bits attempts (decode fallback.value) words.get := by
  rw [BinaryArrayRejection.run_value, binaryRejectionDraw_value sample score envelope envelopeValue bits he]
  unfold RationalRejectionProgram.positiveDraw RationalRejectionProgram.draw
  rw [map_run decode]
  congr 1
  funext index
  simp only [RationalRejectionProgram.proposal, hscore]

end CurrentAFT.RejectionProjection
