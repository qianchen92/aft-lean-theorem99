import CurrentAFT.WeightCoordinates

/-! # Executable inverse coordinates for complete joint tables -/
namespace CurrentAFT.WeightCoordinates
set_option maxHeartbeats 600000

def tupleDecode (base : ℕ) (hb : 0 < base) : (count : ℕ) → ℕ → (Fin count → Fin base)
  | 0, _ => Fin.elim0
  | count+1, code => Fin.lastCases ⟨code % base, Nat.mod_lt _ hb⟩
      (tupleDecode base hb count (code / base))

theorem tupleDecode_code (base count : ℕ) (hb : 0 < base) (word : Fin count → Fin base) :
    tupleDecode base hb count (tupleCode base count (fun index => (word index).val)) = word := by
  induction count with
  | zero => exact Subsingleton.elim _ _
  | succ count ih =>
    funext index
    refine Fin.lastCases ?_ (fun index => ?_) index
    · apply Fin.ext
      simp only [tupleDecode, Fin.lastCases_last, tupleCode, Nat.mul_add_mod_self_left,
        Nat.mod_eq_of_lt (word (Fin.last count)).isLt]
    · simp only [tupleDecode, Fin.lastCases_castSucc, tupleCode]
      have hd : (base * tupleCode base count (fun index => (word index.castSucc).val) +
          (word (Fin.last count)).val) / base =
          tupleCode base count (fun index => (word index.castSucc).val) := by
        rw [Nat.mul_add_div hb, Nat.div_eq_of_lt (word (Fin.last count)).isLt, Nat.add_zero]
      rw [hd, ih]

theorem tupleCode_decode (base count : ℕ) (hb : 0 < base) (code : ℕ) (hc : code < base^count) :
    tupleCode base count (fun index => (tupleDecode base hb count code index).val) = code := by
  induction count generalizing code with
  | zero => simp only [pow_zero] at hc; simp only [tupleCode]; omega
  | succ count ih =>
    have hdiv : code / base < base^count := by
      apply (Nat.div_lt_iff_lt_mul hb).mpr
      simpa only [pow_succ] using hc
    simp only [tupleCode, tupleDecode, Fin.lastCases_castSucc, Fin.lastCases_last]
    rw [ih (code / base) hdiv]
    exact Nat.div_add_mod code base

theorem tupleCode_injective (base count : ℕ) (hb : 0 < base) : Function.Injective
    (fun word : Fin count → Fin base => tupleCode base count (fun index => (word index).val)) := by
  intro first second he
  have h := congrArg (tupleDecode base hb count) he
  simpa only [tupleDecode_code] using h

theorem jointCode_div (base r s : ℕ) (hb : 0 < base)
    (primary : Fin r → Fin base) (body : Fin s → Fin base) :
    jointCode base r s (fun i => (primary i).val) (fun i => (body i).val) / base^s =
      tupleCode base r (fun i => (primary i).val) := by
  unfold jointCode
  rw [Nat.mul_add_div (pow_pos hb s), Nat.div_eq_of_lt
    (tupleCode_lt base s hb _ (fun i => (body i).isLt)), Nat.add_zero]

theorem jointCode_mod (base r s : ℕ) (hb : 0 < base)
    (primary : Fin r → Fin base) (body : Fin s → Fin base) :
    jointCode base r s (fun i => (primary i).val) (fun i => (body i).val) % base^s =
      tupleCode base s (fun i => (body i).val) := by
  unfold jointCode
  rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt (tupleCode_lt base s hb _ (fun i => (body i).isLt))]

theorem jointCode_injective (base r s : ℕ) (hb : 0 < base) : Function.Injective
    (fun pair : (Fin r → Fin base) × (Fin s → Fin base) =>
      jointCode base r s (fun i => (pair.1 i).val) (fun i => (pair.2 i).val)) := by
  rintro ⟨firstPrimary, firstBody⟩ ⟨secondPrimary, secondBody⟩ he
  have hp := congrArg (fun value => value / base^s) he
  have hb' := congrArg (fun value => value % base^s) he
  simp only [jointCode_div base r s hb] at hp
  simp only [jointCode_mod base r s hb] at hb'
  exact Prod.ext (tupleCode_injective base r hb hp) (tupleCode_injective base s hb hb')

end CurrentAFT.WeightCoordinates
