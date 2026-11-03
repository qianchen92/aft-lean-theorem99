import CurrentAFT.BinarySparseCycleAverage
import CurrentAFT.BinarySparseCyclePolynomial

/-! The complete distinct-placement sparse cycle average has a polynomial
budget for every fixed order bound, including its computed normalizer. -/
namespace CurrentAFT.BinarySparseCycleAveragePolynomial
open AFT GaussianSource RationalNumerics BinaryArithmetic
open BinarySparseCyclePolynomial
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false


def distinctWorkPolynomial (pool count : Polynomial ℕ) : Polynomial ℕ :=
  count*(count*(12*count+12*pool+22)+3)+1

 theorem distinctWorkPolynomial_eval (pool count : Polynomial ℕ) (security : ℕ) :
    (distinctWorkPolynomial pool count).eval security = BinaryDistinctTuples.work (pool.eval security) (count.eval security) := by
  simp only [distinctWorkPolynomial,BinaryDistinctTuples.work,BinaryDistinctTuples.pairWork,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one]
  ring

 theorem distinctWork_mono {pool larger count : ℕ} (hp : pool ≤ larger) :
    BinaryDistinctTuples.work pool count ≤ BinaryDistinctTuples.work larger count := by
  unfold BinaryDistinctTuples.work BinaryDistinctTuples.pairWork
  gcongr


def numeratorHeight (limit : ℕ) (body leafHeight : Polynomial ℕ) : Polynomial ℕ :=
  ∑ count ∈ Finset.range (limit+1), BinaryTupleSum.heightPolynomial body count leafHeight

def numeratorWork (limit : ℕ) (body leafHeight leafWork : Polynomial ℕ) : Polynomial ℕ :=
  ∑ count ∈ Finset.range (limit+1), BinaryTupleSum.workPolynomial body count leafHeight
    (distinctWorkPolynomial body (Polynomial.C count)+leafWork+2)


def heightPolynomial (limit : ℕ) (body cutoff precision th : Polynomial ℕ) : Polynomial ℕ :=
  numeratorHeight limit body (BinarySparseCyclePolynomial.heightPolynomial limit cutoff precision th)+numeratorHeight limit body 0


def workPolynomial (limit : ℕ) (body cutoff precision th tw : Polynomial ℕ) : Polynomial ℕ :=
  numeratorWork limit body (BinarySparseCyclePolynomial.heightPolynomial limit cutoff precision th)
      (BinarySparseCyclePolynomial.workPolynomial limit body cutoff precision th tw)+
    numeratorWork limit body 0 1+
    2*RationalBits.primitiveWorkPolynomial (heightPolynomial limit body cutoff precision th)+5

 theorem current_polynomial_bounds (security cutoff bits body count limit : ℕ) (hb : 0 < body)
    (bodyBound cutoffBound precision th tw : Polynomial ℕ) (hbits : bits = precision.eval security)
    (hbody : body ≤ bodyBound.eval security) (hcount : count ≤ limit)
    (hcutoff : cutoff ≤ (security+2)^2) (hupper : cutoff ≤ cutoffBound.eval security)
    (test : Vector IntegerBits count → RationalResult)
    (htest : ∀ roots, (∀ slot, (roots.get slot).digits.length ≤ 2*cutoff+2) →
      HeightBound (test roots).data.decode (th.eval security) ∧ (test roots).work ≤ tw.eval security) :
    HeightBound (BinarySparseCycleAverage.current security cutoff bits body count hb test).data.decode
      ((heightPolynomial limit bodyBound cutoffBound precision th).eval security) ∧
    (BinarySparseCycleAverage.current security cutoff bits body count hb test).work ≤
      (workPolynomial limit bodyBound cutoffBound precision th tw).eval security := by
  subst bits
  let H := BinarySparseCyclePolynomial.heightPolynomial limit cutoffBound precision th
  let W := BinarySparseCyclePolynomial.workPolynomial limit bodyBound cutoffBound precision th tw
  let numerator := BinaryDistinctTuples.sum body count hb (fun sites =>
    BinarySparseCycleEvaluation.current security cutoff (precision.eval security) hb sites test)
  let denominator := BinaryDistinctTuples.normalizer body count hb
  have hs (sites : Vector (Fin body) count) := BinarySparseCyclePolynomial.current_polynomial_bounds security cutoff limit hb sites
    bodyBound cutoffBound precision th tw hbody hcount hcutoff hupper test htest
  have hn := BinaryDistinctTuples.sum_bounds body count hb _ (H.eval security) (W.eval security)
    (fun sites => (hs sites).1) (fun sites => (hs sites).2)
  have hd := BinaryDistinctTuples.sum_bounds body count hb (fun _ => (⟨RationalBits.one,1⟩ : RationalResult)) 0 1
    (fun _ => by rw [RationalBits.one_value]; exact HeightBound.one) (fun _ => le_rfl)
  have bound_sum (leafHeight leafWork : Polynomial ℕ) (result : RationalResult)
      (hh : HeightBound result.data.decode (BinaryTupleSum.height body count (leafHeight.eval security)))
      (hw : result.work ≤ BinaryTupleSum.work body count (leafHeight.eval security) (BinaryDistinctTuples.work body count+leafWork.eval security+2)) :
      HeightBound result.data.decode ((numeratorHeight limit bodyBound leafHeight).eval security) ∧
        result.work ≤ (numeratorWork limit bodyBound leafHeight leafWork).eval security := by
    have hheight : BinaryTupleSum.height body count (leafHeight.eval security) ≤
        (BinaryTupleSum.heightPolynomial bodyBound count leafHeight).eval security := by
      rw [BinaryTupleSum.heightPolynomial_eval]
      exact BinaryPackedRootSum.height_mono hbody le_rfl
    have hwork : BinaryTupleSum.work body count (leafHeight.eval security) (BinaryDistinctTuples.work body count+leafWork.eval security+2) ≤
        (BinaryTupleSum.workPolynomial bodyBound count leafHeight (distinctWorkPolynomial bodyBound (Polynomial.C count)+leafWork+2)).eval security := by
      rw [BinaryTupleSum.workPolynomial_eval]
      simp only [Polynomial.eval_add,Polynomial.eval_ofNat,distinctWorkPolynomial_eval,Polynomial.eval_C]
      exact BinaryPackedRootSum.work_mono hbody le_rfl (by
        have h := distinctWork_mono (count := count) hbody
        omega)
    have hh' : (BinaryTupleSum.heightPolynomial bodyBound count leafHeight).eval security ≤
        (numeratorHeight limit bodyBound leafHeight).eval security := by
      simp only [numeratorHeight,Polynomial.eval_finset_sum]
      exact Finset.single_le_sum (a := count) (s := Finset.range (limit+1))
        (f := fun n => (BinaryTupleSum.heightPolynomial bodyBound n leafHeight).eval security)
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
    have hw' : (BinaryTupleSum.workPolynomial bodyBound count leafHeight (distinctWorkPolynomial bodyBound (Polynomial.C count)+leafWork+2)).eval security ≤
        (numeratorWork limit bodyBound leafHeight leafWork).eval security := by
      simp only [numeratorWork,Polynomial.eval_finset_sum]
      exact Finset.single_le_sum (a := count) (s := Finset.range (limit+1))
        (f := fun n => (BinaryTupleSum.workPolynomial bodyBound n leafHeight (distinctWorkPolynomial bodyBound (Polynomial.C n)+leafWork+2)).eval security)
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
    exact ⟨hh.mono (hheight.trans hh'),hw.trans (hwork.trans hw')⟩
  have hnum := bound_sum H W numerator hn.1 hn.2
  have hden := bound_sum 0 1 denominator (by simpa only [Polynomial.eval_zero] using hd.1)
    (by simpa only [Polynomial.eval_one,Polynomial.eval_zero] using hd.2)
  have hq := RationalBits.quotient_work numerator.data denominator.data
    ((heightPolynomial limit bodyBound cutoffBound precision th).eval security)
    (hnum.1.mono (by simp only [heightPolynomial,Polynomial.eval_add];exact Nat.le_add_right _ _))
    (hden.1.mono (by simp only [heightPolynomial,Polynomial.eval_add];exact Nat.le_add_left _ _))
  constructor
  · change HeightBound (RationalBits.quotient numerator.data denominator.data).data.decode _
    rw [RationalBits.quotient_value]
    simpa only [heightPolynomial,Polynomial.eval_add] using hnum.1.div hden.1
  · change numerator.work+denominator.work+(RationalBits.quotient numerator.data denominator.data).work+3 ≤ _
    simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,RationalBits.primitiveWorkPolynomial_eval]
    dsimp only [H,W] at hnum ⊢
    omega

end
end CurrentAFT.BinarySparseCycleAveragePolynomial
