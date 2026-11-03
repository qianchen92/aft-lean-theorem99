import AFT.BinaryChartArray
import AFT.BinarySeriesPolynomials
import Mathlib.Data.Fin.Tuple.Basic

/-! # Explicit fixed-length tuple enumeration with binary sums

Tuple construction scans the stored tail.  The callback is charged on each
visit; the weight evaluator supplies a concrete joint-array reader.
-/
namespace CurrentAFT.BinaryTupleSum
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

/-- Materialize the new tuple using charged sequential reads. -/
def prepend {Value : Type*} {count : ℕ} (head : Value) (tail : Vector Value count) : CountedValue (Vector Value (count+1)) :=
  let computed := Vector.ofFn (fun index : Fin (count+1) =>
    Fin.cases (motive := fun _ => CountedValue Value) (⟨head, 1⟩ : CountedValue Value) (fun rest => readVector head tail rest) index)
  ⟨computed.map (fun result => result.value), (∑ index, (computed.get index).work)+2*(count+1)+2⟩

theorem prepend_get {Value : Type*} {count : ℕ} (head : Value) (tail : Vector Value count) (index : Fin (count+1)) :
    ((prepend head tail).value.get index) = Fin.cons (α := fun _ => Value) head tail.get index := by
  refine Fin.cases ?_ (fun rest => ?_) index
  · simp [prepend]
  · simp [prepend, readVector_value]

theorem prepend_value {Value : Type*} {count : ℕ} (head : Value) (tail : Vector Value count) :
    (prepend head tail).value = Vector.ofFn (Fin.cons (α := fun _ => Value) head tail.get) := by
  apply Vector.ext
  intro index hi
  simpa using prepend_get head tail ⟨index, hi⟩

def prependWork (count : ℕ) : ℕ := (count+1)*(3*count+5)+2

theorem prepend_work {Value : Type*} {count : ℕ} (head : Value) (tail : Vector Value count) :
    (prepend head tail).work ≤ prependWork count := by
  have hw (index : Fin (count+1)) :
      (Fin.cases (motive := fun _ => CountedValue Value) (⟨head, 1⟩ : CountedValue Value) (fun rest => readVector head tail rest) index).work ≤ 3*count+3 := by
    refine Fin.cases ?_ (fun rest => ?_) index
    · change 1 ≤ 3*count+3; omega
    · exact readVector_work head tail rest
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun index _ => hw index)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  simp only [prepend, Vector.get_ofFn, prependWork]
  nlinarith

theorem get_ofFn_fun {Value : Type*} {count : ℕ} (word : Fin count → Value) :
    (Vector.ofFn word).get = word := by
  funext index
  exact Vector.get_ofFn word index

def current (pool : ℕ) : (count : ℕ) → (Vector (Fin pool) count → RationalResult) → RationalResult
  | 0, kernel => kernel (Vector.ofFn Fin.elim0)
  | count+1, kernel =>
      sumFin pool (fun head => current pool count (fun tail =>
        let word := prepend head tail
        let result := kernel word.value
        ⟨result.data, word.work+result.work+1⟩))

theorem current_value (pool count : ℕ) (kernel : Vector (Fin pool) count → RationalResult) :
    (current pool count kernel).data.decode =
      ∑ word : Fin count → Fin pool, (kernel (Vector.ofFn word)).data.decode := by
  induction count with
  | zero =>
    simp only [current, Fintype.sum_unique]
    congr 2
  | succ count ih =>
    rw [current, sumFin_value]
    simp_rw [ih]
    simp only [prepend_value, get_ofFn_fun]
    simpa only [Fintype.sum_prod_type, Fin.consEquiv_apply] using
      (Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (count+1) => Fin pool))
        (fun word => (kernel (Vector.ofFn word)).data.decode))

def height (pool : ℕ) : (count leafHeight : ℕ) → ℕ
  | 0, leafHeight => leafHeight
  | count+1, leafHeight => pool*(height pool count leafHeight+1)

def work (pool : ℕ) : (count leafHeight leafWork : ℕ) → ℕ
  | 0, _, leafWork => leafWork
  | count+1, leafHeight, leafWork =>
      pool*(work pool count leafHeight (prependWork count+leafWork+1)+
        primitiveWorkBound ((pool+1)*(height pool count leafHeight+1))+2)+2

theorem current_bounds (pool count : ℕ) (kernel : Vector (Fin pool) count → RationalResult)
    (leafHeight leafWork : ℕ)
    (hh : ∀ word, HeightBound (kernel word).data.decode leafHeight)
    (hw : ∀ word, (kernel word).work ≤ leafWork) :
    HeightBound (current pool count kernel).data.decode (height pool count leafHeight) ∧
      (current pool count kernel).work ≤ work pool count leafHeight leafWork := by
  induction count generalizing leafWork with
  | zero => exact ⟨hh _, hw _⟩
  | succ count ih =>
    have hb (head : Fin pool) := ih (fun tail =>
      let word := prepend head tail
      let result := kernel word.value
      ⟨result.data, word.work+result.work+1⟩)
      (prependWork count+leafWork+1) (fun tail => hh (prepend head tail).value)
      (fun tail => Nat.add_le_add_right (Nat.add_le_add (prepend_work head tail) (hw (prepend head tail).value)) 1)
    exact ⟨sumFin_height pool _ _ (fun head => (hb head).1),
      sumFin_work pool _ _ _ (fun head => (hb head).1) (fun head => (hb head).2)⟩

noncomputable def heightPolynomial (pool : Polynomial ℕ) : (count : ℕ) → Polynomial ℕ → Polynomial ℕ
  | 0, leafHeight => leafHeight
  | count+1, leafHeight => pool*(heightPolynomial pool count leafHeight+1)

noncomputable def workPolynomial (pool : Polynomial ℕ) : (count : ℕ) → Polynomial ℕ → Polynomial ℕ → Polynomial ℕ
  | 0, _, leafWork => leafWork
  | count+1, leafHeight, leafWork =>
      pool*(workPolynomial pool count leafHeight (Polynomial.C (prependWork count)+leafWork+1)+
        primitiveWorkPolynomial ((pool+1)*(heightPolynomial pool count leafHeight+1))+2)+2

theorem heightPolynomial_eval (pool leafHeight : Polynomial ℕ) (count security : ℕ) :
    (heightPolynomial pool count leafHeight).eval security = height (pool.eval security) count (leafHeight.eval security) := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [heightPolynomial, height, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one, ih]

theorem workPolynomial_eval (pool leafHeight leafWork : Polynomial ℕ) (count security : ℕ) :
    (workPolynomial pool count leafHeight leafWork).eval security =
      work (pool.eval security) count (leafHeight.eval security) (leafWork.eval security) := by
  induction count generalizing leafWork with
  | zero => rfl
  | succ count ih =>
    simp only [workPolynomial, work, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_ofNat,
      Polynomial.eval_one, Polynomial.eval_C, primitiveWorkPolynomial_eval, heightPolynomial_eval, ih]

end CurrentAFT.BinaryTupleSum
