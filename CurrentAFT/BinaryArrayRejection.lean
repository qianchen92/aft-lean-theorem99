import AFT.BinaryRejectionLoop
import AFT.BinaryDataArrays

/-! Binary rejection with sequential reads of the stored random tape.
Every failed attempt materializes its remaining tape suffix explicitly. -/
namespace CurrentAFT.BinaryArrayRejection
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
variable {State Tape : Type*} [Inhabited Tape]

def run (sample : Tape → CountedValue State) (score : State → CountedValue RationalBits)
    (envelope : RationalBits) (bits : ℕ) (fallback : CountedValue State) :
    (attempts : ℕ) → Vector (Tape × (Fin bits → Fin 2)) attempts → CountedValue State
  | 0, _ => fallback
  | attempts+1, words =>
    let word := readVector default words 0
    let candidate := sample word.value.1
    let raw := score candidate.value
    let ratio := binaryPositiveRatio raw.value envelope
    let accepted := binaryAcceptance ratio.data bits word.value.2
    let used := word.work+candidate.work+raw.work+ratio.work+accepted.work+4
    if accepted.value = 0 then ⟨candidate.value, used⟩ else
      let tail := storeData attempts (fun index => readVector default words index.succ)
      let remaining := run sample score envelope bits fallback attempts tail.value
      ⟨remaining.value, used+tail.work+remaining.work+2⟩

theorem run_value (sample : Tape → CountedValue State) (score : State → CountedValue RationalBits)
    (envelope : RationalBits) (bits : ℕ) (fallback : CountedValue State)
    (attempts : ℕ) (words : Vector (Tape × (Fin bits → Fin 2)) attempts) :
    (run sample score envelope bits fallback attempts words).value =
      (binaryRejectionDraw sample score envelope bits fallback attempts words.get).value := by
  induction attempts with
  | zero => rfl
  | succ attempts ih =>
    simp only [run, binaryRejectionDraw, readVector_value]
    split_ifs
    · rfl
    · rw [ih]
      have htail : (storeData attempts (fun index => readVector (default : Tape × (Fin bits → Fin 2)) words index.succ)).value.get =
          Fin.tail words.get := by
        funext index
        exact storeData_get _ _ index |>.trans (readVector_value _ _ _)
      rw [htail]

def overhead (limit : ℕ) : ℕ := (limit+1)*(3*limit+5)+15

theorem run_work_limit (sample : Tape → CountedValue State) (score : State → CountedValue RationalBits)
    (envelope : RationalBits) (bits : ℕ) (fallback : CountedValue State)
    (proposalWork scoreWork scoreBits envelopeBits : ℕ)
    (hsample : ∀ input, (sample input).work ≤ proposalWork)
    (hscore : ∀ point, (score point).work ≤ scoreWork)
    (hheight : ∀ point, HeightBound (score point).value.decode scoreBits)
    (henvelope : HeightBound envelope.decode envelopeBits)
    (attempts limit : ℕ) (hlimit : attempts ≤ limit) (words : Vector (Tape × (Fin bits → Fin 2)) attempts) :
    (run sample score envelope bits fallback attempts words).work ≤
      fallback.work+attempts*(binaryRejectionStepWork proposalWork scoreWork scoreBits envelopeBits bits+overhead limit) := by
  induction attempts with
  | zero => simp only [run, zero_mul, add_zero, le_refl]
  | succ attempts ih =>
    let word := readVector default words 0
    let candidate := sample word.value.1
    let raw := score candidate.value
    let ratio := binaryPositiveRatio raw.value envelope
    let accepted := binaryAcceptance ratio.data bits word.value.2
    let tail := storeData attempts (fun index => readVector default words index.succ)
    have hw := readVector_work (default : Tape × (Fin bits → Fin 2)) words 0
    change word.work ≤ _ at hw
    have hp := hsample word.value.1
    change candidate.work ≤ _ at hp
    have hs := hscore candidate.value
    change raw.work ≤ _ at hs
    have hh := hheight candidate.value
    have hr := binaryPositiveRatio_work raw.value envelope scoreBits envelopeBits hh henvelope
    change ratio.work ≤ _ at hr
    have hratio := binaryPositiveRatio_height raw.value envelope scoreBits envelopeBits hh henvelope
    have ha := binaryAcceptance_work ratio.data (scoreBits+envelopeBits) bits word.value.2 hratio
    change accepted.work ≤ _ at ha
    have ht := storeData_work attempts (3*(attempts+1)+3)
      (fun index => readVector (default : Tape × (Fin bits → Fin 2)) words index.succ)
      (fun index => readVector_work _ _ _)
    change tail.work ≤ _ at ht
    have hi := ih (by omega) tail.value
    have hstep : word.work+candidate.work+raw.work+ratio.work+accepted.work+4+tail.work+2 ≤
        binaryRejectionStepWork proposalWork scoreWork scoreBits envelopeBits bits+overhead limit := by
      have ht' : attempts*(3*(attempts+1)+5) ≤ limit*(3*limit+5) :=
        Nat.mul_le_mul (by omega) (by omega)
      unfold binaryRejectionStepWork overhead
      nlinarith
    change (if accepted.value = 0 then
      (⟨candidate.value, word.work+candidate.work+raw.work+ratio.work+accepted.work+4⟩ : CountedValue State)
      else ⟨(run sample score envelope bits fallback attempts tail.value).value,
        word.work+candidate.work+raw.work+ratio.work+accepted.work+4+tail.work+
          (run sample score envelope bits fallback attempts tail.value).work+2⟩).work ≤ _
    split_ifs <;> dsimp only <;> nlinarith

theorem run_work (sample : Tape → CountedValue State) (score : State → CountedValue RationalBits)
    (envelope : RationalBits) (bits : ℕ) (fallback : CountedValue State)
    (proposalWork scoreWork scoreBits envelopeBits : ℕ)
    (hsample : ∀ input, (sample input).work ≤ proposalWork)
    (hscore : ∀ point, (score point).work ≤ scoreWork)
    (hheight : ∀ point, HeightBound (score point).value.decode scoreBits)
    (henvelope : HeightBound envelope.decode envelopeBits)
    (attempts : ℕ) (words : Vector (Tape × (Fin bits → Fin 2)) attempts) :
    (run sample score envelope bits fallback attempts words).work ≤
      fallback.work+attempts*(binaryRejectionStepWork proposalWork scoreWork scoreBits envelopeBits bits+overhead attempts) :=
  run_work_limit sample score envelope bits fallback proposalWork scoreWork scoreBits envelopeBits
    hsample hscore hheight henvelope attempts attempts le_rfl words

end CurrentAFT.BinaryArrayRejection
