import AFT.BinaryChartArray
import AFT.BinarySeriesPolynomials

/-! # Counted fixed-length products of computed binary rationals -/
namespace CurrentAFT.BinaryFiniteProduct
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1400000

def current : (count : ℕ) → (Fin count → RationalResult) → RationalResult
  | 0, _ => ⟨one,2⟩
  | count+1, term =>
      let previous := current count (fun index => term index.castSucc)
      let next := term (Fin.last count)
      let result := RationalBits.multiply previous.data next.data
      ⟨result.data, previous.work+next.work+result.work+2⟩

theorem current_value (count : ℕ) (term : Fin count → RationalResult) :
    (current count term).data.decode = ∏ index, (term index).data.decode := by
  induction count with
  | zero => simp only [current, one_value, Fin.prod_univ_zero]
  | succ count ih => simp only [current, RationalBits.multiply_value, ih, Fin.prod_univ_castSucc]

theorem current_height (count bits : ℕ) (term : Fin count → RationalResult)
    (hh : ∀ index, HeightBound (term index).data.decode bits) :
    HeightBound (current count term).data.decode (count*bits) := by
  induction count with
  | zero => simpa only [current, one_value, zero_mul] using HeightBound.one
  | succ count ih =>
      change HeightBound (RationalBits.multiply _ _).data.decode _
      rw [RationalBits.multiply_value]
      exact ((ih _ (fun index => hh index.castSucc)).mul (hh (Fin.last count))).mono (by nlinarith)

def work (count bits termWork : ℕ) := count*(termWork+primitiveWorkBound (count*bits)+2)+2

theorem current_work (count bits termWork : ℕ) (term : Fin count → RationalResult)
    (hh : ∀ index, HeightBound (term index).data.decode bits) (hw : ∀ index, (term index).work ≤ termWork) :
    (current count term).work ≤ work count bits termWork := by
  induction count with
  | zero => simp only [current, work, zero_mul, zero_add, le_refl]
  | succ count ih =>
      have hp := current_height count bits (fun index => term index.castSucc) (fun index => hh index.castSucc)
      have hi := ih (fun index => term index.castSucc) (fun index => hh index.castSucc) (fun index => hw index.castSucc)
      have hm := RationalBits.multiply_work (current count (fun index => term index.castSucc)).data (term (Fin.last count)).data ((count+1)*bits)
        (hp.mono (Nat.mul_le_mul_right _ (by omega))) ((hh (Fin.last count)).mono (by nlinarith))
      have hmono := primitiveWorkBound_mono (Nat.mul_le_mul_right bits (show count ≤ count+1 by omega))
      have ht := hw (Fin.last count)
      change _+_+_+2 ≤ _
      unfold work at hi ⊢
      nlinarith

noncomputable def workPolynomial (count : ℕ) (bits termWork : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C count*(termWork+primitiveWorkPolynomial (Polynomial.C count*bits)+2)+2

theorem workPolynomial_eval (count : ℕ) (bits termWork : Polynomial ℕ) (security : ℕ) :
    (workPolynomial count bits termWork).eval security = work count (bits.eval security) (termWork.eval security) := by
  simp only [workPolynomial, work, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_ofNat,
    primitiveWorkPolynomial_eval]

end CurrentAFT.BinaryFiniteProduct
