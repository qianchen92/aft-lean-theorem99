import CurrentAFT.BinarySeedDensityFormula
import CurrentAFT.BinaryTupleSum
import AFT.RationalCanonicalPairProgram

/-! # Executed finite pair canonicalization, including all marginal sums -/
namespace CurrentAFT.BinaryCanonicalPair
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

inductive Leaf where
  | point | first | second | row | column | total
  deriving DecidableEq

def expression : ScalarProgram Leaf :=
  .add (.add (.add (.atom .point) (.negate (.multiply (.atom .first) (.atom .column))))
    (.negate (.multiply (.atom .row) (.atom .second))))
    (.multiply (.multiply (.atom .total) (.atom .first)) (.atom .second))

theorem expression_literals : expression.LiteralBound 1 := by trivial

def read (values : Leaf → RationalBits) (code : Leaf) : CountedValue RationalBits :=
  let result := RationalBits.copy (values code)
  ⟨result.data,result.work+1⟩

def formula (values : Leaf → RationalBits) : RationalResult :=
  let result := expression.compileBinaryRun (read values)
  ⟨result.value,result.work+1⟩

theorem formula_value (values : Leaf → RationalBits) :
    (formula values).data.decode=(values .point).decode-(values .first).decode*(values .column).decode-
      (values .row).decode*(values .second).decode+(values .total).decode*(values .first).decode*(values .second).decode := by
  simp only [formula,ScalarProgram.compileBinaryRun_value,read,RationalBits.copy_value,
    expression,ScalarProgram.run,sub_eq_add_neg]

def current (count : ℕ) (reference : Fin count → RationalResult) (mass : Fin count → Fin count → RationalResult)
    (first second : Fin count) : RationalResult :=
  let point := mass first second
  let refFirst := reference first
  let refSecond := reference second
  let row := sumFin count (mass first)
  let column := sumFin count (fun index => mass index second)
  let total := sumFin count (fun index => sumFin count (mass index))
  let result := formula (fun
    | .point => point.data | .first => refFirst.data | .second => refSecond.data
    | .row => row.data | .column => column.data | .total => total.data)
  ⟨result.data,point.work+refFirst.work+refSecond.work+row.work+column.work+total.work+result.work+7⟩

theorem current_value (count : ℕ) (reference : Fin count → RationalResult) (mass : Fin count → Fin count → RationalResult)
    (first second : Fin count) :
    (current count reference mass first second).data.decode=
      rationalCanonicalPair (fun index => (reference index).data.decode)
        (fun first second => (mass first second).data.decode) first second := by
  simp only [current,formula_value,sumFin_value,rationalCanonicalPair]

def marginalHeight (count bits : ℕ) := count*(bits+1)
def totalHeight (count bits : ℕ) := count*(marginalHeight count bits+1)
def operandHeight (count refBits massBits : ℕ) := refBits+massBits+marginalHeight count massBits+totalHeight count massBits
def height (count refBits massBits : ℕ) := expression.nodes*(operandHeight count refBits massBits+3)
def sumWork (count bits budget : ℕ) := count*(budget+primitiveWorkBound ((count+1)*(bits+1))+2)+2
def formulaWork (bits : ℕ) := expression.nodes*(smallRationalEncodingWork 1+(4*bits+9)+primitiveWorkBound (expression.nodes*(bits+3))+2)+2
def work (count refBits massBits refWork massWork : ℕ) :=
  massWork+2*refWork+2*sumWork count massBits massWork+
    sumWork count (marginalHeight count massBits) (sumWork count massBits massWork)+
    formulaWork (operandHeight count refBits massBits)+7

theorem formula_bounds (values : Leaf → RationalBits) (bits : ℕ)
    (hh : ∀ leaf, HeightBound (values leaf).decode bits) :
    HeightBound (formula values).data.decode (expression.nodes*(bits+3)) ∧
      (formula values).work ≤ formulaWork bits := by
  have hr (leaf : Leaf) : HeightBound (read values leaf).value.decode bits := by
    rw [read,RationalBits.copy_value]; exact hh leaf
  have hw (leaf : Leaf) : (read values leaf).work ≤ 4*bits+9 := by
    have h := RationalBits.copy_work (values leaf) bits (hh leaf)
    change _+1 ≤ _; omega
  have w := expression.compileBinaryRun_work_of_bounds _ 1 bits (4*bits+9) expression_literals hw hr
  have h := expression.run_height (fun leaf => (read values leaf).value.decode) (fun _ => bits) hr
  have hb := expression.heightBudget_le (fun _ => bits) (bits+2) (fun _ => Nat.le_add_right _ _)
    (ScalarProgram.literalsBounded_mono expression_literals.literalsBounded (Nat.le_add_left _ _))
  constructor
  · change HeightBound (expression.compileBinaryRun (read values)).value.decode _
    rw [ScalarProgram.compileBinaryRun_value]
    exact h.mono (hb.trans_eq (by congr 1))
  · change (expression.compileBinaryRun (read values)).work+1 ≤ _
    unfold formulaWork
    simp only [Nat.mul_one,Nat.add_assoc,Nat.reduceAdd] at w ⊢
    omega

theorem current_bounds (count : ℕ) (reference : Fin count → RationalResult) (mass : Fin count → Fin count → RationalResult)
    (first second : Fin count) (refBits massBits refWork massWork : ℕ)
    (hr : ∀ index, HeightBound (reference index).data.decode refBits)
    (hm : ∀ first second, HeightBound (mass first second).data.decode massBits)
    (wr : ∀ index, (reference index).work ≤ refWork) (wm : ∀ first second, (mass first second).work ≤ massWork) :
    HeightBound (current count reference mass first second).data.decode (height count refBits massBits) ∧
      (current count reference mass first second).work ≤ work count refBits massBits refWork massWork := by
  have hs (index : Fin count) := sumFin_height count massBits (mass index) (hm index)
  have hc := sumFin_height count massBits (fun index => mass index second) (fun index => hm index second)
  have ht := sumFin_height count (marginalHeight count massBits) (fun index => sumFin count (mass index)) hs
  change ∀ index, HeightBound (sumFin count (mass index)).data.decode (marginalHeight count massBits) at hs
  change HeightBound (sumFin count (fun index => mass index second)).data.decode (marginalHeight count massBits) at hc
  change HeightBound (sumFin count (fun index => sumFin count (mass index))).data.decode (totalHeight count massBits) at ht
  let H := operandHeight count refBits massBits
  have hH : H=refBits+massBits+marginalHeight count massBits+totalHeight count massBits := rfl
  have hf := formula_bounds (fun
    | .point => (mass first second).data | .first => (reference first).data | .second => (reference second).data
    | .row => (sumFin count (mass first)).data | .column => (sumFin count (fun index => mass index second)).data
    | .total => (sumFin count (fun index => sumFin count (mass index))).data) H (by
      intro leaf
      cases leaf
      · exact (hm first second).mono (by rw [hH]; omega)
      · exact (hr first).mono (by rw [hH]; omega)
      · exact (hr second).mono (by rw [hH]; omega)
      · exact (hs first).mono (by rw [hH]; omega)
      · exact hc.mono (by rw [hH]; omega)
      · exact ht.mono (by rw [hH]; omega))
  have ws (index : Fin count) := sumFin_work count massBits massWork (mass index) (hm index) (wm index)
  have wc := sumFin_work count massBits massWork (fun index => mass index second) (fun index => hm index second) (fun index => wm index second)
  have wt := sumFin_work count (marginalHeight count massBits) (sumWork count massBits massWork)
    (fun index => sumFin count (mass index)) hs ws
  refine ⟨hf.1,?_⟩
  dsimp only [current]
  have wp := wm first second
  have wf := wr first
  have wb := wr second
  have wrw := ws first
  dsimp only [H] at hf
  unfold work sumWork at *
  omega

noncomputable def operandPolynomial (count refBits massBits : Polynomial ℕ) : Polynomial ℕ :=
  refBits+massBits+count*(massBits+1)+count*(count*(massBits+1)+1)
noncomputable def heightPolynomial (count refBits massBits : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C expression.nodes*(operandPolynomial count refBits massBits+3)
noncomputable def sumWorkPolynomial (count bits budget : Polynomial ℕ) : Polynomial ℕ :=
  count*(budget+primitiveWorkPolynomial ((count+1)*(bits+1))+2)+2
noncomputable def formulaWorkPolynomial (bits : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C expression.nodes*(smallRationalEncodingPolynomial 1+(4*bits+9)+primitiveWorkPolynomial (Polynomial.C expression.nodes*(bits+3))+2)+2
noncomputable def workPolynomial (count refBits massBits refWork massWork : Polynomial ℕ) : Polynomial ℕ :=
  massWork+2*refWork+2*sumWorkPolynomial count massBits massWork+
    sumWorkPolynomial count (count*(massBits+1)) (sumWorkPolynomial count massBits massWork)+
    formulaWorkPolynomial (operandPolynomial count refBits massBits)+7

theorem heightPolynomial_eval (count refBits massBits : Polynomial ℕ) (security : ℕ) :
    (heightPolynomial count refBits massBits).eval security=height (count.eval security) (refBits.eval security) (massBits.eval security) := by
  simp only [heightPolynomial,operandPolynomial,height,operandHeight,marginalHeight,totalHeight,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_ofNat,Polynomial.eval_one]

theorem workPolynomial_eval (count refBits massBits refWork massWork : Polynomial ℕ) (security : ℕ) :
    (workPolynomial count refBits massBits refWork massWork).eval security=
      work (count.eval security) (refBits.eval security) (massBits.eval security) (refWork.eval security) (massWork.eval security) := by
  simp only [workPolynomial,operandPolynomial,sumWorkPolynomial,formulaWorkPolynomial,work,sumWork,
    formulaWork,operandHeight,marginalHeight,totalHeight,smallRationalEncodingPolynomial_eval,primitiveWorkPolynomial_eval,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_ofNat,Polynomial.eval_one]

theorem height_mono {count larger refBits massBits : ℕ} (hc : count ≤ larger) :
    height count refBits massBits ≤ height larger refBits massBits := by
  simp only [height,operandHeight,totalHeight,marginalHeight]
  gcongr

theorem work_mono {count larger refBits massBits refWork massWork : ℕ} (hc : count ≤ larger) :
    work count refBits massBits refWork massWork ≤ work larger refBits massBits refWork massWork := by
  simp only [work,sumWork,formulaWork,operandHeight,totalHeight,marginalHeight,primitiveWorkBound]
  gcongr

end CurrentAFT.BinaryCanonicalPair
