import CurrentAFT.WeightCoordinates
import AFT.BinaryChartArray
import AFT.UnaryPolynomialCounters
import AFT.BinarySeriesPolynomials

/-! # Executed indices and sequential joint-table reads for the weight -/
namespace CurrentAFT.BinaryWeightCoordinates
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] multiplyCounter addCounter powerCounter

private opaque checkedPower (base exponent : ℕ) :
    {result : UnaryCounterResult // result.count = base^exponent ∧ result.work ≤ powerCounterWork base exponent} :=
  ⟨powerCounter base exponent, powerCounter_value base exponent, powerCounter_work base exponent⟩

def leading {count : ℕ} (word : Vector ℕ (count+1)) : CountedValue (Vector ℕ count) :=
  let computed := Vector.ofFn (fun index : Fin count => readVector 0 word index.castSucc)
  ⟨computed.map (fun result => result.value), (∑ index, (computed.get index).work)+2*count+2⟩

theorem leading_get {count : ℕ} (word : Vector ℕ (count+1)) (index : Fin count) :
    (leading word).value.get index = word.get index.castSucc := by simp [leading, readVector_value]

def leadingWork (count : ℕ) : ℕ := count*(3*(count+1)+5)+2

theorem leading_work {count : ℕ} (word : Vector ℕ (count+1)) : (leading word).work ≤ leadingWork count := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun (index : Fin count) _ => readVector_work 0 word index.castSucc)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  simp only [leading, Vector.get_ofFn, leadingWork]
  nlinarith

def encode (base : ℕ) : (count : ℕ) → Vector ℕ count → UnaryCounterResult
  | 0, _ => ⟨0, 1⟩
  | count+1, word =>
      let digits := leading word
      let previous := encode base count digits.value
      let last := readVector 0 word (Fin.last count)
      let scaled := multiplyCounter base previous.count
      let result := addCounter scaled.count last.value
      ⟨result.count, digits.work+previous.work+last.work+scaled.work+result.work+5⟩

theorem encode_value (base count : ℕ) (word : Vector ℕ count) :
    (encode base count word).count = WeightCoordinates.tupleCode base count word.get := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [encode, addCounter_value, multiplyCounter_value, readVector_value, ih, WeightCoordinates.tupleCode]
    congr 2
    apply congrArg (WeightCoordinates.tupleCode base count)
    funext index
    exact leading_get word index

def encodeWork (base capacity : ℕ) : ℕ → ℕ
  | 0 => 1
  | count+1 => leadingWork count+encodeWork base capacity count+(3*(count+1)+3)+
      (base*(2*capacity+3)+1)+(2*(base*capacity)+1)+5

theorem encode_work (base order count : ℕ) (hb : 0 < base) (hcount : count ≤ order)
    (word : Vector ℕ count) (hw : ∀ index, word.get index < base) :
    (encode base count word).work ≤ encodeWork base (base^order) count := by
  induction count with
  | zero => exact le_refl _
  | succ count ih =>
    let digits := leading word
    let previous := encode base count digits.value
    let last := readVector 0 word (Fin.last count)
    let scaled := multiplyCounter base previous.count
    let result := addCounter scaled.count last.value
    have hp (index : Fin count) : digits.value.get index < base := by rw [leading_get]; exact hw index.castSucc
    have wc : previous.work ≤ encodeWork base (base^order) count := ih (by omega) digits.value hp
    have hv : previous.count ≤ base^order := by
      rw [encode_value]
      exact (WeightCoordinates.tupleCode_lt base count hb digits.value.get hp).le.trans
        (Nat.pow_le_pow_right hb (by omega))
    have wd : digits.work ≤ leadingWork count := leading_work word
    have wl : last.work ≤ 3*(count+1)+3 := readVector_work 0 word (Fin.last count)
    have wm : scaled.work ≤ base*(2*base^order+3)+1 :=
      (multiplyCounter_work base previous.count).le.trans
        (Nat.add_le_add_right (Nat.mul_le_mul_left base (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hv) 3)) 1)
    have vs : scaled.count ≤ base*base^order :=
      (multiplyCounter_value base previous.count).le.trans (Nat.mul_le_mul_left base hv)
    have wa : result.work ≤ 2*(base*base^order)+1 :=
      (addCounter_work scaled.count last.value).le.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2 vs) 1)
    change digits.work+previous.work+last.work+scaled.work+result.work+5 ≤ _
    rw [encodeWork]
    omega

def joint (base r s : ℕ) (primary : Vector ℕ r) (body : Vector ℕ s) : UnaryCounterResult :=
  let first := encode base r primary
  let second := encode base s body
  let power := (checkedPower base s).val
  let scaled := multiplyCounter power.count first.count
  let result := addCounter scaled.count second.count
  ⟨result.count, first.work+second.work+power.work+scaled.work+result.work+5⟩

theorem joint_value (base r s : ℕ) (primary : Vector ℕ r) (body : Vector ℕ s) :
    (joint base r s primary body).count = WeightCoordinates.jointCode base r s primary.get body.get := by
  simp only [joint, addCounter_value, multiplyCounter_value, encode_value, (checkedPower base s).property.1,
    WeightCoordinates.jointCode]

def jointWork (base order r s : ℕ) : ℕ :=
  let capacity := base^order
  encodeWork base capacity r+encodeWork base capacity s+powerCounterWork base s+
    (capacity*(2*capacity+3)+1)+(2*(capacity*capacity)+1)+5

theorem joint_work (base order r s : ℕ) (hb : 0 < base) (hdegree : r+s ≤ order)
    (primary : Vector ℕ r) (body : Vector ℕ s)
    (hp : ∀ index, primary.get index < base) (hq : ∀ index, body.get index < base) :
    (joint base r s primary body).work ≤ jointWork base order r s := by
  let first := encode base r primary
  let second := encode base s body
  let power := (checkedPower base s).val
  let scaled := multiplyCounter power.count first.count
  let result := addCounter scaled.count second.count
  let capacity := base^order
  have wf : first.work ≤ encodeWork base capacity r := encode_work base order r hb (by omega) primary hp
  have ws : second.work ≤ encodeWork base capacity s := encode_work base order s hb (by omega) body hq
  have wp : power.work ≤ powerCounterWork base s := (checkedPower base s).property.2
  have vf : first.count ≤ capacity := by
    rw [encode_value]
    exact (WeightCoordinates.tupleCode_lt base r hb primary.get hp).le.trans (Nat.pow_le_pow_right hb (by omega))
  have vp : power.count ≤ capacity := (checkedPower base s).property.1.le.trans (Nat.pow_le_pow_right hb (by omega))
  have wm : scaled.work ≤ capacity*(2*capacity+3)+1 :=
    (multiplyCounter_work power.count first.count).le.trans (Nat.add_le_add_right
      (Nat.mul_le_mul vp (Nat.add_le_add_right (Nat.mul_le_mul_left 2 vf) 3)) 1)
  have vm : scaled.count ≤ capacity*capacity :=
    (multiplyCounter_value power.count first.count).le.trans (Nat.mul_le_mul vp vf)
  have wa : result.work ≤ 2*(capacity*capacity)+1 :=
    (addCounter_work scaled.count second.count).le.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2 vm) 1)
  change first.work+second.work+power.work+scaled.work+result.work+5 ≤ _
  change _ ≤ encodeWork base capacity r+encodeWork base capacity s+powerCounterWork base s+
    (capacity*(2*capacity+3)+1)+(2*(capacity*capacity)+1)+5
  omega

def arity (order r s : ℕ) : UnaryCounterResult :=
  let size := addCounter order 1
  let row := multiplyCounter r size.count
  let result := addCounter row.count s
  ⟨result.count, size.work+row.work+result.work+3⟩

theorem arity_value (order r s : ℕ) : (arity order r s).count = WeightCoordinates.arityCode order r s := by
  simp only [arity, addCounter_value, multiplyCounter_value, WeightCoordinates.arityCode]

def arityWork (order : ℕ) : ℕ :=
  (2*order+1)+(order*(2*(order+1)+3)+1)+(2*(order*(order+1))+1)+3

theorem arity_work (order r s : ℕ) (hr : r ≤ order) : (arity order r s).work ≤ arityWork order := by
  let size := addCounter order 1
  let row := multiplyCounter r size.count
  let result := addCounter row.count s
  have hs : size.count = order+1 := addCounter_value order 1
  have ws : size.work = 2*order+1 := addCounter_work order 1
  have wr : row.work ≤ order*(2*(order+1)+3)+1 := by
    rw [multiplyCounter_work, hs]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hr) 1
  have vr : row.count ≤ order*(order+1) := by
    rw [multiplyCounter_value, hs]
    exact Nat.mul_le_mul_right _ hr
  have wa : result.work ≤ 2*(order*(order+1))+1 :=
    (addCounter_work row.count s).le.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2 vr) 1)
  change size.work+row.work+result.work+3 ≤ _
  unfold arityWork
  omega

abbrev Table (base order : ℕ) := Vector (Vector RationalBits (base^order)) ((order+1)^2)

def read (base order r s : ℕ) (hb : 0 < base) (hdegree : r+s ≤ order)
    (table : Table base order) (primary : Vector (Fin base) r) (body : Vector (Fin base) s) : RationalResult :=
  let first := primary.map Fin.val
  let second := body.map Fin.val
  let wordCode := joint base r s first second
  let blockCode := arity order r s
  let row := readVector (Vector.replicate (base^order) zero) table
    ⟨blockCode.count, by
      rw [arity_value]
      exact WeightCoordinates.arityCode_lt order r s (by omega) (by omega)⟩
  let value := readVector zero row.value
    ⟨wordCode.count, by
      rw [joint_value]
      exact WeightCoordinates.jointCode_lt_capacity base order r s hb hdegree _ _
        (fun index => by
          change (primary.map Fin.val).get index < base
          simpa only [Vector.get_map] using (primary.get index).isLt)
        (fun index => by
          change (body.map Fin.val).get index < base
          simpa only [Vector.get_map] using (body.get index).isLt)⟩
  ⟨value.value, r+s+2+wordCode.work+blockCode.work+row.work+value.work+base^order+4⟩

theorem get_map_fun {First Second : Type*} {count : ℕ} (word : Vector First count) (f : First → Second) :
    (word.map f).get = fun index => f (word.get index) := by
  funext index
  simp only [Vector.get_map]

theorem read_value (base order r s : ℕ) (hb : 0 < base) (hdegree : r+s ≤ order)
    (table : Table base order) (primary : Vector (Fin base) r) (body : Vector (Fin base) s) :
    (read base order r s hb hdegree table primary body).data.decode =
      ((table.get (WeightCoordinates.arityIndex order ⟨r, by omega⟩ ⟨s, by omega⟩)).get
        (WeightCoordinates.wordIndex base order r s hb hdegree primary.get body.get)).decode := by
  simp only [read, readVector_value]
  congr 3
  · apply Fin.ext
    exact arity_value order r s
  · simpa only [WeightCoordinates.wordIndex, get_map_fun, Function.comp_def] using joint_value base r s (primary.map Fin.val) (body.map Fin.val)

def readWork (base order r s : ℕ) : ℕ := r+s+2+jointWork base order r s+arityWork order+
  (3*((order+1)^2)+3)+(3*(base^order)+3)+base^order+4

theorem read_work (base order r s : ℕ) (hb : 0 < base) (hdegree : r+s ≤ order)
    (table : Table base order) (primary : Vector (Fin base) r) (body : Vector (Fin base) s) :
    (read base order r s hb hdegree table primary body).work ≤ readWork base order r s := by
  have hj := joint_work base order r s hb hdegree (primary.map Fin.val) (body.map Fin.val)
    (fun index => by simpa only [Vector.get_map] using (primary.get index).isLt)
    (fun index => by simpa only [Vector.get_map] using (body.get index).isLt)
  have ha := arity_work order r s (by omega)
  unfold read
  dsimp only
  have hr := readVector_work (Vector.replicate (base^order) zero) table
    ⟨(arity order r s).count, by rw [arity_value]; exact WeightCoordinates.arityCode_lt order r s (by omega) (by omega)⟩
  have hv := readVector_work zero
    (readVector (Vector.replicate (base^order) zero) table
      ⟨(arity order r s).count, by rw [arity_value]; exact WeightCoordinates.arityCode_lt order r s (by omega) (by omega)⟩).value
    ⟨(joint base r s (primary.map Fin.val) (body.map Fin.val)).count, by
      rw [joint_value]
      exact WeightCoordinates.jointCode_lt_capacity base order r s hb hdegree _ _
        (fun index => by simpa only [Vector.get_map] using (primary.get index).isLt)
        (fun index => by simpa only [Vector.get_map] using (body.get index).isLt)⟩
  unfold readWork
  omega

theorem read_height (base order r s : ℕ) (hb : 0 < base) (hdegree : r+s ≤ order)
    (table : Table base order) (primary : Vector (Fin base) r) (body : Vector (Fin base) s)
    (bound : ℕ) (ht : ∀ arity word, HeightBound ((table.get arity).get word).decode bound) :
    HeightBound (read base order r s hb hdegree table primary body).data.decode bound := by
  rw [read_value]
  exact ht _ _

noncomputable def encodeWorkPolynomial (base capacity : Polynomial ℕ) : ℕ → Polynomial ℕ
  | 0 => 1
  | count+1 => Polynomial.C (leadingWork count)+encodeWorkPolynomial base capacity count+Polynomial.C (3*(count+1)+3)+
      (base*(2*capacity+3)+1)+(2*(base*capacity)+1)+5

noncomputable def jointWorkPolynomial (base : Polynomial ℕ) (order r s : ℕ) : Polynomial ℕ :=
  let capacity := base^order
  encodeWorkPolynomial base capacity r+encodeWorkPolynomial base capacity s+
    Polynomial.C (s+1)*(6*(base+1)^(s+2)+4)+
    (capacity*(2*capacity+3)+1)+(2*(capacity*capacity)+1)+5

noncomputable def readWorkPolynomial (base : Polynomial ℕ) (order r s : ℕ) : Polynomial ℕ :=
  Polynomial.C (r+s+2)+jointWorkPolynomial base order r s+Polynomial.C (arityWork order)+
    Polynomial.C (3*((order+1)^2)+3)+(3*(base^order)+3)+base^order+4

theorem encodeWorkPolynomial_eval (base capacity : Polynomial ℕ) (count security : ℕ) :
    (encodeWorkPolynomial base capacity count).eval security = encodeWork (base.eval security) (capacity.eval security) count := by
  induction count with
  | zero => simp only [encodeWorkPolynomial, encodeWork, Polynomial.eval_one]
  | succ count ih => simp only [encodeWorkPolynomial, encodeWork, Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, ih]

theorem jointWorkPolynomial_eval (base : Polynomial ℕ) (order r s security : ℕ) :
    (jointWorkPolynomial base order r s).eval security = jointWork (base.eval security) order r s := by
  simp only [jointWorkPolynomial, jointWork, encodeWorkPolynomial_eval, powerCounterWork,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat, Polynomial.eval_one]

theorem readWorkPolynomial_eval (base : Polynomial ℕ) (order r s security : ℕ) :
    (readWorkPolynomial base order r s).eval security = readWork (base.eval security) order r s := by
  simp only [readWorkPolynomial, readWork, jointWorkPolynomial_eval, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat]

end CurrentAFT.BinaryWeightCoordinates
