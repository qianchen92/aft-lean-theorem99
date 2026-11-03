import CurrentAFT.BinaryCurrentPaired
import CurrentAFT.BinaryTupleSum

/-! # All primary slots of a joint kernel evaluated on stored binary data

The recursive score profile is materialized before each paired operation.
Groups and tuple tails are read by sequential array scans.
-/
namespace CurrentAFT.BinaryPairedTensor
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def dropFirst {Value : Type*} {count : ℕ} (fallback : Value) (word : Vector Value (count+1)) : CountedValue (Vector Value count) :=
  let computed := Vector.ofFn (fun index : Fin count => readVector fallback word index.succ)
  ⟨computed.map (fun result => result.value), (∑ index, (computed.get index).work)+2*count+2⟩

theorem dropFirst_get {Value : Type*} {count : ℕ} (fallback : Value) (word : Vector Value (count+1)) (index : Fin count) :
    (dropFirst fallback word).value.get index = word.get index.succ := by simp [dropFirst, readVector_value]

def dropWork (count : ℕ) : ℕ := count*(3*(count+1)+5)+2

theorem dropFirst_work {Value : Type*} {count : ℕ} (fallback : Value) (word : Vector Value (count+1)) :
    (dropFirst fallback word).work ≤ dropWork count := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun (index : Fin count) _ => readVector_work fallback word index.succ)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  simp only [dropFirst, Vector.get_ofFn, dropWork]
  nlinarith

def lift {colors : ℕ} (primary center : Vector RationalBits colors)
    (anchor : Vector (Vector RationalBits colors) colors) (rate : RationalBits)
    (profile : Fin colors → ℚ) (group : Fin colors × Fin colors) : ℚ :=
  profile group.1-rate.decode*(∑ color, (primary.get color).decode*profile color*((anchor.get color).get group.2).decode)/
    (center.get group.2).decode

def value {colors : ℕ} (primary center : Vector RationalBits colors)
    (anchor : Vector (Vector RationalBits colors) colors) (rate : RationalBits) :
    (count : ℕ) → ((Fin count → Fin colors) → ℚ) → (Fin count → Fin colors × Fin colors) → ℚ
  | 0, kernel, _ => kernel Fin.elim0
  | count+1, kernel, groups => lift primary center anchor rate
      (fun color => value primary center anchor rate count (fun rest => kernel (Fin.cons color rest))
        (fun index => groups index.succ)) (groups 0)

def current {colors : ℕ} (primary center : Vector RationalBits colors)
    (anchor : Vector (Vector RationalBits colors) colors) (rate : RationalBits) (fallback : Fin colors × Fin colors) :
    (count : ℕ) → (Vector (Fin colors) count → RationalResult) → Vector (Fin colors × Fin colors) count → RationalResult
  | 0, kernel, _ => kernel (Vector.ofFn Fin.elim0)
  | count+1, kernel, groups =>
      let head := readVector fallback groups 0
      let tail := dropFirst fallback groups
      let profile := buildArray colors (fun color => current primary center anchor rate fallback count
        (fun rest =>
          let word := BinaryTupleSum.prepend color rest
          let result := kernel word.value
          ⟨result.data, word.work+result.work+1⟩) tail.value)
      let result := BinaryPairedScore.current primary center profile.data anchor rate head.value.1 head.value.2
      ⟨result.data, head.work+tail.work+profile.work+result.work+4⟩

theorem current_value {colors : ℕ} (primary center : Vector RationalBits colors)
    (anchor : Vector (Vector RationalBits colors) colors) (rate : RationalBits) (fallback : Fin colors × Fin colors)
    (count : ℕ) (kernel : Vector (Fin colors) count → RationalResult) (groups : Vector (Fin colors × Fin colors) count) :
    (current primary center anchor rate fallback count kernel groups).data.decode =
      value primary center anchor rate count (fun word => (kernel (Vector.ofFn word)).data.decode) groups.get := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [current, BinaryPairedScore.current_value, buildArray_get, readVector_value]
    simp_rw [ih]
    simp only [value, lift]
    have htail : (dropFirst fallback groups).value.get = fun index => groups.get index.succ := by
      funext index; exact dropFirst_get fallback groups index
    rw [htail]
    simp only [BinaryTupleSum.prepend_value, BinaryTupleSum.get_ofFn_fun]

def height (colors referenceHeight : ℕ) : (count leafHeight : ℕ) → ℕ
  | 0, leafHeight => leafHeight
  | count+1, leafHeight => BinaryPairedScore.height colors (referenceHeight+height colors referenceHeight count leafHeight)

def work (colors referenceHeight : ℕ) : (count leafHeight leafWork : ℕ) → ℕ
  | 0, _, leafWork => leafWork
  | count+1, leafHeight, leafWork =>
      (3*(count+1)+3)+dropWork count+
      (colors*(work colors referenceHeight count leafHeight (BinaryTupleSum.prependWork count+leafWork+1)+2)+2)+
      BinaryPairedScore.work colors (referenceHeight+height colors referenceHeight count leafHeight)+4

theorem current_bounds {colors : ℕ} (primary center : Vector RationalBits colors)
    (anchor : Vector (Vector RationalBits colors) colors) (rate : RationalBits) (fallback : Fin colors × Fin colors)
    (referenceHeight count leafHeight leafWork : ℕ) (kernel : Vector (Fin colors) count → RationalResult)
    (groups : Vector (Fin colors × Fin colors) count)
    (hp : ∀ color, HeightBound (primary.get color).decode referenceHeight)
    (hb : ∀ color, HeightBound (center.get color).decode referenceHeight)
    (ha : ∀ input output, HeightBound ((anchor.get input).get output).decode referenceHeight)
    (hr : HeightBound rate.decode referenceHeight)
    (hk : ∀ word, HeightBound (kernel word).data.decode leafHeight)
    (hw : ∀ word, (kernel word).work ≤ leafWork) :
    HeightBound (current primary center anchor rate fallback count kernel groups).data.decode
      (height colors referenceHeight count leafHeight) ∧
    (current primary center anchor rate fallback count kernel groups).work ≤ work colors referenceHeight count leafHeight leafWork := by
  induction count generalizing leafWork with
  | zero => exact ⟨hk _, hw _⟩
  | succ count ih =>
    let head := readVector fallback groups 0
    let tail := dropFirst fallback groups
    let profile := buildArray colors (fun color => current primary center anchor rate fallback count
      (fun rest => let word := BinaryTupleSum.prepend color rest; let result := kernel word.value
        ⟨result.data, word.work+result.work+1⟩) tail.value)
    let H := referenceHeight+height colors referenceHeight count leafHeight
    have hchild (color : Fin colors) := ih (BinaryTupleSum.prependWork count+leafWork+1)
      (fun rest => let word := BinaryTupleSum.prepend color rest; let result := kernel word.value
        ⟨result.data, word.work+result.work+1⟩) tail.value
      (fun rest => hk (BinaryTupleSum.prepend color rest).value)
      (fun rest => Nat.add_le_add_right (Nat.add_le_add (BinaryTupleSum.prepend_work color rest) (hw (BinaryTupleSum.prepend color rest).value)) 1)
    have hprofile (color : Fin colors) : HeightBound (profile.data.get color).decode H := by
      rw [buildArray_get]
      exact (hchild color).1.mono (Nat.le_add_left _ _)
    have hreference : referenceHeight ≤ H := Nat.le_add_right _ _
    have hout := BinaryPairedScore.current_height primary center profile.data anchor rate head.value.1 head.value.2 H
      (fun color => (hp color).mono hreference) (fun color => (hb color).mono hreference) hprofile
      (fun input output => (ha input output).mono hreference) (hr.mono hreference)
    have wout := BinaryPairedScore.current_work primary center profile.data anchor rate head.value.1 head.value.2 H
      (fun color => (hp color).mono hreference) (fun color => (hb color).mono hreference) hprofile
      (fun input output => (ha input output).mono hreference) (hr.mono hreference)
    have wp : profile.work ≤ colors*(work colors referenceHeight count leafHeight (BinaryTupleSum.prependWork count+leafWork+1)+2)+2 :=
      buildArray_work colors _ _ (fun color => (hchild color).2)
    have wh : head.work ≤ 3*(count+1)+3 := readVector_work fallback groups 0
    have wt : tail.work ≤ dropWork count := dropFirst_work fallback groups
    exact ⟨hout, by
      change head.work+tail.work+profile.work+(BinaryPairedScore.current primary center profile.data anchor rate head.value.1 head.value.2).work+4 ≤ _
      rw [work]
      exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add wh wt) wp) wout) 4⟩

noncomputable def heightPolynomial (colors referenceHeight : Polynomial ℕ) : (count : ℕ) → Polynomial ℕ → Polynomial ℕ
  | 0, leafHeight => leafHeight
  | count+1, leafHeight => BinaryCurrentPaired.heightPolynomial colors
      (referenceHeight+heightPolynomial colors referenceHeight count leafHeight)

noncomputable def workPolynomial (colors referenceHeight : Polynomial ℕ) : (count : ℕ) → Polynomial ℕ → Polynomial ℕ → Polynomial ℕ
  | 0, _, leafWork => leafWork
  | count+1, leafHeight, leafWork =>
      Polynomial.C (3*(count+1)+3)+Polynomial.C (dropWork count)+
      (colors*(workPolynomial colors referenceHeight count leafHeight
        (Polynomial.C (BinaryTupleSum.prependWork count)+leafWork+1)+2)+2)+
      BinaryCurrentPaired.evaluationWorkPolynomial colors
        (referenceHeight+heightPolynomial colors referenceHeight count leafHeight)+4

theorem heightPolynomial_eval (colors referenceHeight leafHeight : Polynomial ℕ) (count security : ℕ) :
    (heightPolynomial colors referenceHeight count leafHeight).eval security =
      height (colors.eval security) (referenceHeight.eval security) count (leafHeight.eval security) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [heightPolynomial, height, BinaryCurrentPaired.heightPolynomial, BinaryPairedScore.height,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one, Polynomial.eval_ofNat, ih]

theorem workPolynomial_eval (colors referenceHeight leafHeight leafWork : Polynomial ℕ) (count security : ℕ) :
    (workPolynomial colors referenceHeight count leafHeight leafWork).eval security =
      work (colors.eval security) (referenceHeight.eval security) count (leafHeight.eval security) (leafWork.eval security) := by
  induction count generalizing leafWork with
  | zero => rfl
  | succ count ih =>
    simp only [workPolynomial, work, BinaryCurrentPaired.evaluationWorkPolynomial, BinaryCurrentPaired.heightPolynomial,
      BinaryPairedScore.work, BinaryPairedScore.height, primitiveWorkPolynomial_eval,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one, Polynomial.eval_ofNat, Polynomial.eval_C, heightPolynomial_eval, ih]

end CurrentAFT.BinaryPairedTensor
