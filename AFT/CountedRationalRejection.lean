import AFT.ExecutableGlobalRejection
import AFT.CountedPositiveSampling
import AFT.CountedGaussianArithmetic

/-! # Arithmetic counters for the executable outer rejection loop -/
namespace AFT.RationalRejectionProgram
open RationalNumerics PermutationProgram BetaReference
open scoped BigOperators

 structure CountedValue (State : Type*) where
  value : State
  work : ℕ

 def countedAcceptance (bits : ℕ) (value : ℚ) (word : Fin bits → Fin 2) : CountedNatural :=
  let tickets := powerTwo bits
  let accepted := ⌊(tickets.value : ℚ)*RationalAcceptanceCoin.clipped value⌋₊
  let ticket := bitValue bits word
  let selected := countedBucket [accepted,tickets.value-accepted] ticket.value
  ⟨selected.value,tickets.work+ticket.work+selected.work+7⟩

 theorem countedAcceptance_value (bits : ℕ) (value : ℚ) (word : Fin bits → Fin 2) :
    (countedAcceptance bits value word).value=(RationalAcceptanceCoin.draw bits value word).val := by
  simp only [countedAcceptance,powerTwo_value,bitValue_value,countedBucket_value,
    RationalAcceptanceCoin.draw,RationalAcceptanceCoin.counts,RationalAcceptanceCoin.count,
    FiniteTicketSampler.drawBitTable,FiniteTicketSampler.drawFin,Fin.val_cast]
  simp only [Nat.cast_pow,Nat.cast_ofNat,List.ofFn_succ,List.ofFn_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_fin_one]

 theorem countedAcceptance_work (bits : ℕ) (value : ℚ) (word : Fin bits → Fin 2) :
    (countedAcceptance bits value word).work≤3*bits+13 := by
  have hh := countedBucket_work
    [⌊((2^bits : ℕ) : ℚ)*RationalAcceptanceCoin.clipped value⌋₊,
      2^bits-⌊((2^bits : ℕ) : ℚ)*RationalAcceptanceCoin.clipped value⌋₊] (bitValue bits word).value
  simp only [List.length_cons,List.length_nil] at hh
  simp only [countedAcceptance,powerTwo_value,powerTwo_work,bitValue_work]
  omega

 variable {State Tape : Type*}

/-- The proposal and score are evaluated once per attempt and stored before
checking the acceptance coin. The remaining attempts are evaluated only
following rejection. -/
 def countedDraw (sample : Tape → CountedValue State) (score : State → GaussianArithmetic)
    (envelope bits : ℕ) (fallback : CountedValue State) :
    (attempts : ℕ) → (Fin attempts → Tape×(Fin bits → Fin 2)) → CountedValue State
  | 0,_ => fallback
  | attempts+1,tape =>
      let candidate := sample (tape 0).1
      let raw := score candidate.value
      let accepted := countedAcceptance bits (max raw.value 0/(envelope : ℚ)) (tape 0).2
      let used := candidate.work+raw.work+accepted.work+3
      if accepted.value=0 then ⟨candidate.value,used⟩
      else
        let remaining := countedDraw sample score envelope bits fallback attempts (fun index => tape index.succ)
        ⟨remaining.value,used+remaining.work⟩

 theorem countedDraw_value (sample : Tape → CountedValue State) (score : State → GaussianArithmetic)
    (envelope bits : ℕ) (fallback : CountedValue State) (attempts : ℕ)
    (tape : Fin attempts → Tape×(Fin bits → Fin 2)) :
    (countedDraw sample score envelope bits fallback attempts tape).value=
      positiveDraw (fun input => (sample input).value) (fun point => (score point).value)
        envelope bits attempts fallback.value tape := by
  induction attempts with
  | zero => rfl
  | succ attempts ih =>
    simp only [countedDraw,countedAcceptance_value,positiveDraw,draw,run,proposal]
    have he : ∀ coin : Fin 2,coin.val=0 ↔ coin=0 := fun coin => by simp only [Fin.ext_iff,Fin.val_zero]
    simp only [he]
    split_ifs
    · rfl
    · exact ih (fun index => tape index.succ)

 theorem countedDraw_work (sample : Tape → CountedValue State) (score : State → GaussianArithmetic)
    (envelope bits : ℕ) (fallback : CountedValue State) (proposalWork scoreWork : ℕ)
    (hsample : ∀ tape,(sample tape).work≤proposalWork) (hscore : ∀ point,(score point).work≤scoreWork)
    (attempts : ℕ) (tape : Fin attempts → Tape×(Fin bits → Fin 2)) :
    (countedDraw sample score envelope bits fallback attempts tape).work≤
      fallback.work+attempts*(proposalWork+scoreWork+3*bits+16) := by
  induction attempts with
  | zero => simp only [countedDraw,Nat.zero_mul,Nat.add_zero,le_refl]
  | succ attempts ih =>
    have hp := hsample (tape 0).1
    have hs := hscore (sample (tape 0).1).value
    have hc := countedAcceptance_work bits (max (score (sample (tape 0).1).value).value 0/(envelope : ℚ)) (tape 0).2
    have hr := ih (fun index => tape index.succ)
    simp only [countedDraw]
    split_ifs <;> nlinarith

end AFT.RationalRejectionProgram
