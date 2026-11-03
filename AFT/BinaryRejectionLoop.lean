import AFT.BinaryAcceptanceCoin
import AFT.CountedRationalRejection

/-! # Capped rejection using the actual binary acceptance implementation

The proposal and numerical score are each evaluated once per attempted
sample. This layer propagates their proved bit costs; it does not assume
constant-time rational arithmetic for the acceptance decision.
-/
namespace AFT.BinaryArithmetic
open RationalNumerics RationalRejectionProgram
variable {State Tape : Type*}

def binaryPositiveRatio (raw envelope : RationalBits) : RationalResult :=
  let positive := raw.maxZero
  let result := positive.data.quotient envelope
  ⟨result.data,positive.work+result.work+2⟩

theorem binaryPositiveRatio_value (raw envelope : RationalBits) :
    (binaryPositiveRatio raw envelope).data.decode=max raw.decode 0/envelope.decode := by
  simp only [binaryPositiveRatio,RationalBits.quotient_value,RationalBits.maxZero_value]

theorem binaryPositiveRatio_height (raw envelope : RationalBits) (scoreBits envelopeBits : ℕ)
    (hs : HeightBound raw.decode scoreBits) (he : HeightBound envelope.decode envelopeBits) :
    HeightBound (binaryPositiveRatio raw envelope).data.decode (scoreBits+envelopeBits) := by
  rw [binaryPositiveRatio_value]
  exact (max_zero_height _ _ hs).div he

theorem binaryPositiveRatio_work (raw envelope : RationalBits) (scoreBits envelopeBits : ℕ)
    (hs : HeightBound raw.decode scoreBits) (he : HeightBound envelope.decode envelopeBits) :
    (binaryPositiveRatio raw envelope).work≤ 2*RationalBits.primitiveWorkBound (scoreBits+envelopeBits)+6 := by
  have hp : HeightBound raw.maxZero.data.decode scoreBits := by
    rw [RationalBits.maxZero_value]
    exact max_zero_height _ _ hs
  have hw := RationalBits.quotient_work raw.maxZero.data envelope (scoreBits+envelopeBits)
    (hp.mono (Nat.le_add_right _ _)) (he.mono (Nat.le_add_left _ _))
  simp only [binaryPositiveRatio,RationalBits.maxZero_work]
  omega

def binaryRejectionDraw (sample : Tape → CountedValue State) (score : State → CountedValue RationalBits)
    (envelope : RationalBits) (bits : ℕ) (fallback : CountedValue State) :
    (attempts : ℕ) → (Fin attempts → Tape×(Fin bits → Fin 2)) → CountedValue State
  | 0,_ => fallback
  | attempts+1,tape =>
      let candidate := sample (tape 0).1
      let raw := score candidate.value
      let ratio := binaryPositiveRatio raw.value envelope
      let accepted := binaryAcceptance ratio.data bits (tape 0).2
      let used := candidate.work+raw.work+ratio.work+accepted.work+3
      if accepted.value=0 then ⟨candidate.value,used⟩ else
        let remaining := binaryRejectionDraw sample score envelope bits fallback attempts (Fin.tail tape)
        ⟨remaining.value,used+remaining.work⟩

theorem binaryRejectionDraw_value (sample : Tape → CountedValue State)
    (score : State → CountedValue RationalBits) (envelope : RationalBits) (envelopeValue bits : ℕ)
    (he : envelope.decode=(envelopeValue : ℚ)) (fallback : CountedValue State)
    (attempts : ℕ) (tape : Fin attempts → Tape×(Fin bits → Fin 2)) :
    (binaryRejectionDraw sample score envelope bits fallback attempts tape).value=
      RationalRejectionProgram.positiveDraw (fun input => (sample input).value)
        (fun point => (score point).value.decode) envelopeValue bits attempts fallback.value tape := by
  induction attempts with
  | zero => rfl
  | succ attempts ih =>
      simp only [binaryRejectionDraw,binaryAcceptance_value,binaryPositiveRatio_value,he,
        RationalRejectionProgram.positiveDraw,RationalRejectionProgram.draw,RationalRejectionProgram.run,
        RationalRejectionProgram.proposal]
      have hc : ∀ coin : Fin 2,coin.val=0 ↔ coin=0 := fun coin => by simp only [Fin.ext_iff,Fin.val_zero]
      simp only [hc]
      split_ifs
      · rfl
      · exact ih (Fin.tail tape)

def binaryRejectionStepWork (proposalWork scoreWork scoreBits envelopeBits bits : ℕ) : ℕ :=
  proposalWork+scoreWork+2*RationalBits.primitiveWorkBound (scoreBits+envelopeBits)+
    binaryAcceptanceWork (scoreBits+envelopeBits) bits+9

theorem binaryRejectionDraw_work (sample : Tape → CountedValue State)
    (score : State → CountedValue RationalBits) (envelope : RationalBits) (bits : ℕ)
    (fallback : CountedValue State) (proposalWork scoreWork scoreBits envelopeBits : ℕ)
    (hsample : ∀ input,(sample input).work≤ proposalWork)
    (hscore : ∀ point,(score point).work≤ scoreWork)
    (hheight : ∀ point,HeightBound (score point).value.decode scoreBits)
    (henvelope : HeightBound envelope.decode envelopeBits)
    (attempts : ℕ) (tape : Fin attempts → Tape×(Fin bits → Fin 2)) :
    (binaryRejectionDraw sample score envelope bits fallback attempts tape).work≤
      fallback.work+attempts*binaryRejectionStepWork proposalWork scoreWork scoreBits envelopeBits bits := by
  induction attempts with
  | zero => simp only [binaryRejectionDraw,Nat.zero_mul,Nat.add_zero,le_refl]
  | succ attempts ih =>
      have wp := hsample (tape 0).1
      have ws := hscore (sample (tape 0).1).value
      have hh := hheight (sample (tape 0).1).value
      have wr := binaryPositiveRatio_work (score (sample (tape 0).1).value).value envelope scoreBits envelopeBits hh henvelope
      have ha := binaryPositiveRatio_height (score (sample (tape 0).1).value).value envelope scoreBits envelopeBits hh henvelope
      have wa := binaryAcceptance_work (binaryPositiveRatio (score (sample (tape 0).1).value).value envelope).data
        (scoreBits+envelopeBits) bits (tape 0).2 ha
      have wt := ih (Fin.tail tape)
      simp only [binaryRejectionStepWork] at wt
      simp only [binaryRejectionDraw,binaryRejectionStepWork]
      split_ifs <;> nlinarith

end AFT.BinaryArithmetic
