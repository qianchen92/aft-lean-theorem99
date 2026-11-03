import AFT.BinarySignedComparison
import AFT.BinaryChartArray
import AFT.BinarySeriesPolynomials

/-! Integer translation of a finite rational array, using explicit binary
comparisons and an indexed finite sum. The source callback is executed only
at a matching integer; there is no integer-to-palette oracle. -/
namespace AFT.BinaryArithmetic
open RationalNumerics RationalBits RationalRejectionProgram Polynomial
open scoped BigOperators

 def signedEqual (firstSign secondSign : Bool) (first second : List Bool) : CountedValue Bool :=
  let forward := signedLe firstSign secondSign first second
  let backward := signedLe secondSign firstSign second first
  ⟨forward.value && backward.value,forward.work+backward.work+3⟩

 theorem signedEqual_value (firstSign secondSign : Bool) (first second : List Bool) :
    (signedEqual firstSign secondSign first second).value=true ↔
      signedValue firstSign first=signedValue secondSign second := by
  simp only [signedEqual,Bool.and_eq_true,signedLe_value]
  exact le_antisymm_iff.symm

 theorem signedEqual_work (firstSign secondSign : Bool) (first second : List Bool) :
    (signedEqual firstSign secondSign first second).work≤48*max first.length second.length+39 := by
  have hf:=signedLe_work firstSign secondSign first second
  have hb:=signedLe_work secondSign firstSign second first
  simp only [signedEqual]
  rw [max_comm second.length first.length] at hb
  omega

 def binaryShiftTerm (shiftSign outputSign : Bool) (shift output : List Bool)
    (center : ℕ) (entry : ℕ → RationalResult) : RationalResult :=
  let encoded := canonicalCounter center
  let translated := signedAdd false shiftSign encoded.digits shift
  let matched := signedEqual outputSign translated.negative output translated.digits
  let result := if matched.value then entry center else ⟨RationalBits.zero,1⟩
  ⟨result.data,encoded.work+translated.work+matched.work+result.work+5⟩

 theorem binaryShiftTerm_value (shiftSign outputSign : Bool) (shift output : List Bool)
    (center : ℕ) (entry : ℕ → RationalResult) :
    (binaryShiftTerm shiftSign outputSign shift output center entry).data.decode=
      if signedValue outputSign output=(center : ℤ)+signedValue shiftSign shift
      then (entry center).data.decode else 0 := by
  have he : (signedEqual outputSign (signedAdd false shiftSign (canonicalCounter center).digits shift).negative
      output (signedAdd false shiftSign (canonicalCounter center).digits shift).digits).value=true ↔
      signedValue outputSign output=(center : ℤ)+signedValue shiftSign shift := by
    rw [signedEqual_value,signedAdd_value]
    simp only [signedValue,Bool.false_eq_true,ite_false,canonicalCounter_value]
  simp only [binaryShiftTerm,he]
  split_ifs <;> rfl

 theorem binaryShiftTerm_height (shiftSign outputSign : Bool) (shift output : List Bool)
    (center bits : ℕ) (entry : ℕ → RationalResult) (h : HeightBound (entry center).data.decode bits) :
    HeightBound (binaryShiftTerm shiftSign outputSign shift output center entry).data.decode bits := by
  rw [binaryShiftTerm_value]
  split_ifs
  · exact h
  · exact HeightBound.zero.mono (Nat.zero_le _)

 def binaryShiftTermWork (count shiftBits outputBits entryWork : ℕ) : ℕ :=
   50*(count+1)^2+100*(count+shiftBits+outputBits+2)+entryWork+100

 theorem binaryShiftTerm_work (shiftSign outputSign : Bool) (shift output : List Bool)
    (center count entryWork : ℕ) (entry : ℕ → RationalResult)
    (hc : center≤count) (he : (entry center).work≤entryWork) :
    (binaryShiftTerm shiftSign outputSign shift output center entry).work≤
      binaryShiftTermWork count shift.length output.length entryWork := by
  have hl : (canonicalCounter center).digits.length≤count := by
    rw [canonicalCounter_length]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=center))).trans hc
  have hw := (canonicalCounter_work center).trans (show 50*(center+1)^2≤50*(count+1)^2 by gcongr)
  have hs:=signedAdd_work false shiftSign (canonicalCounter center).digits shift
  have hsl:=signedAdd_length false shiftSign (canonicalCounter center).digits shift
  have hm:=signedEqual_work outputSign (signedAdd false shiftSign (canonicalCounter center).digits shift).negative
      output (signedAdd false shiftSign (canonicalCounter center).digits shift).digits
  simp only [binaryShiftTerm,binaryShiftTermWork]
  split_ifs <;> (try dsimp only) <;> omega

 def binaryShiftSum (count : ℕ) (shiftSign outputSign : Bool) (shift output : List Bool)
    (entry : ℕ → RationalResult) : RationalResult :=
  sumFin count (fun center => binaryShiftTerm shiftSign outputSign shift output center.val entry)

 theorem binaryShiftSum_value (count : ℕ) (shiftSign outputSign : Bool) (shift output : List Bool)
    (entry : ℕ → RationalResult) :
    (binaryShiftSum count shiftSign outputSign shift output entry).data.decode=
      ∑ center∈Finset.range count,if signedValue outputSign output=(center : ℤ)+signedValue shiftSign shift
        then (entry center).data.decode else 0 := by
  simp only [binaryShiftSum,sumFin_value,binaryShiftTerm_value]
  exact Fin.sum_univ_eq_sum_range (fun center : ℕ =>
    if signedValue outputSign output=(center : ℤ)+signedValue shiftSign shift
    then (entry center).data.decode else (0 : ℚ)) count

 theorem binaryShiftSum_height (count bits : ℕ) (shiftSign outputSign : Bool) (shift output : List Bool)
    (entry : ℕ → RationalResult) (h : ∀ center<count,HeightBound (entry center).data.decode bits) :
    HeightBound (binaryShiftSum count shiftSign outputSign shift output entry).data.decode (count*(bits+1)) := by
  apply sumFin_height
  intro center
  exact binaryShiftTerm_height _ _ _ _ _ _ _ (h _ center.isLt)

 def binaryShiftSumWork (count bits shiftBits outputBits entryWork : ℕ) : ℕ :=
   count*(binaryShiftTermWork count shiftBits outputBits entryWork+primitiveWorkBound ((count+1)*(bits+1))+2)+2

 theorem binaryShiftSum_work (count bits entryWork : ℕ) (shiftSign outputSign : Bool) (shift output : List Bool)
    (entry : ℕ → RationalResult) (hh : ∀ center<count,HeightBound (entry center).data.decode bits)
    (hw : ∀ center<count,(entry center).work≤entryWork) :
    (binaryShiftSum count shiftSign outputSign shift output entry).work≤
      binaryShiftSumWork count bits shift.length output.length entryWork := by
  apply sumFin_work
  · intro center
    exact binaryShiftTerm_height _ _ _ _ _ _ _ (hh _ center.isLt)
  · intro center
    exact binaryShiftTerm_work _ _ _ _ _ _ _ _ center.isLt.le (hw _ center.isLt)

 noncomputable def binaryShiftSumPolynomial (count bits shiftBits outputBits entryWork : Polynomial ℕ) : Polynomial ℕ :=
   count*(50*(count+1)^2+100*(count+shiftBits+outputBits+2)+entryWork+100+
     primitiveWorkPolynomial ((count+1)*(bits+1))+2)+2

 @[simp] theorem binaryShiftSumPolynomial_eval (count bits shiftBits outputBits entryWork : Polynomial ℕ) (n : ℕ) :
    (binaryShiftSumPolynomial count bits shiftBits outputBits entryWork).eval n=
      binaryShiftSumWork (count.eval n) (bits.eval n) (shiftBits.eval n) (outputBits.eval n) (entryWork.eval n) := by
  simp [binaryShiftSumPolynomial,binaryShiftSumWork,binaryShiftTermWork]

 theorem binaryShiftSumWork_mono {c c' b b' s s' o o' e e' : ℕ}
    (hc : c≤c') (hb : b≤b') (hs : s≤s') (ho : o≤o') (he : e≤e') :
    binaryShiftSumWork c b s o e≤binaryShiftSumWork c' b' s' o' e' := by
  unfold binaryShiftSumWork binaryShiftTermWork primitiveWorkBound
  gcongr

 def binaryShiftFinSum (count : ℕ) (shiftSign outputSign : Bool) (shift output : List Bool)
    (entry : Fin count → RationalResult) : RationalResult :=
  sumFin count (fun center => binaryShiftTerm shiftSign outputSign shift output center.val (fun _ => entry center))

 theorem binaryShiftFinSum_value (count : ℕ) (shiftSign outputSign : Bool) (shift output : List Bool)
    (entry : Fin count → RationalResult) :
    (binaryShiftFinSum count shiftSign outputSign shift output entry).data.decode=
      ∑ center,if signedValue outputSign output=(center.val : ℤ)+signedValue shiftSign shift
        then (entry center).data.decode else 0 := by
  simp only [binaryShiftFinSum,sumFin_value,binaryShiftTerm_value]

 theorem binaryShiftFinSum_height (count bits : ℕ) (shiftSign outputSign : Bool) (shift output : List Bool)
    (entry : Fin count → RationalResult) (h : ∀ center,HeightBound (entry center).data.decode bits) :
    HeightBound (binaryShiftFinSum count shiftSign outputSign shift output entry).data.decode (count*(bits+1)) := by
  apply sumFin_height
  intro center
  exact binaryShiftTerm_height _ _ _ _ _ _ _ (h center)

 theorem binaryShiftFinSum_work (count bits entryWork : ℕ) (shiftSign outputSign : Bool) (shift output : List Bool)
    (entry : Fin count → RationalResult) (hh : ∀ center,HeightBound (entry center).data.decode bits)
    (hw : ∀ center,(entry center).work≤entryWork) :
    (binaryShiftFinSum count shiftSign outputSign shift output entry).work≤
      binaryShiftSumWork count bits shift.length output.length entryWork := by
  apply sumFin_work
  · intro center
    exact binaryShiftTerm_height _ _ _ _ _ _ _ (hh center)
  · intro center
    exact binaryShiftTerm_work _ _ _ _ _ _ _ _ center.isLt.le (hw center)

 theorem binaryShiftFinSum_cast (first second : ℕ) (heq : first=second)
    (shiftSign outputSign : Bool) (shift output : List Bool) (entry : Fin second → RationalResult) :
    binaryShiftFinSum first shiftSign outputSign shift output (fun index => entry (Fin.cast heq index))=
      binaryShiftFinSum second shiftSign outputSign shift output entry := by
  subst second;rfl

end AFT.BinaryArithmetic
