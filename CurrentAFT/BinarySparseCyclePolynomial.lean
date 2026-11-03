import CurrentAFT.BinarySparseCycleBounds

/-! Fixed-order polynomial witnesses for the actual sparse Gaussian evaluator.
Body size, numerical precision and the concrete test program have explicit
polynomial budgets; every touched-word and rank operation is included. -/
namespace CurrentAFT.BinarySparseCyclePolynomial
open AFT GaussianSource RationalNumerics BinaryArithmetic
open BinarySparseCycleBounds BinaryTouchedCycleRanks
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false


def preparePolynomial (body count : Polynomial ℕ) : Polynomial ℕ :=
  count*(3*count+7*body+19)+3+(2*count)*(2*count*(6*body+4)+3)+3

def bufferPolynomial (body count : Polynomial ℕ) : Polynomial ℕ :=
  preparePolynomial body count+(2*count)*(4*count+5)+4

def positionsPolynomial (body count : Polynomial ℕ) : Polynomial ℕ :=
  bufferPolynomial body count+count*(3*count+7*body+2*((2*count)*(6*count+6*body+8)+3)+20)+4

def gaussianHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  500000000*((Polynomial.X+2)^2+precision+2)^6

def termHeightPolynomial (edges gh th : Polynomial ℕ) : Polynomial ℕ := edges*gh+th

def rootEntryPolynomial (edges count cutoff : Polynomial ℕ) : Polynomial ℕ :=
  3*count+6*edges+100*(2*cutoff+2)^2+20*(2*cutoff+1)+30

def rootsPolynomial (edges count cutoff : Polynomial ℕ) : Polynomial ℕ := count*(rootEntryPolynomial edges count cutoff+2)+2

def weightPolynomial (edges cutoff : Polynomial ℕ) : Polynomial ℕ := 3*edges+3*(2*cutoff+1)+8

def termPolynomial (edges count cutoff gh th tw : Polynomial ℕ) : Polynomial ℕ :=
  rootsPolynomial edges count cutoff+tw+
    edges*(weightPolynomial edges cutoff+RationalBits.primitiveWorkPolynomial (edges*gh)+2)+2+
    RationalBits.primitiveWorkPolynomial (termHeightPolynomial edges gh th)+4

 theorem preparePolynomial_eval (body count : Polynomial ℕ) (security : ℕ) :
    (preparePolynomial body count).eval security = prepareWork (body.eval security) (count.eval security) := by
  simp only [preparePolynomial,prepareWork,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]

 theorem positionsPolynomial_eval (body count : Polynomial ℕ) (security : ℕ) :
    (positionsPolynomial body count).eval security = positionsWork (body.eval security) (count.eval security) := by
  simp only [positionsPolynomial,bufferPolynomial,positionsWork,bufferWork,preparePolynomial_eval,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]

 theorem gaussianHeightPolynomial_eval (precision : Polynomial ℕ) (security : ℕ) :
    (gaussianHeightPolynomial precision).eval security = BinaryGaussianAverage.gaussianHeight security (precision.eval security) := by
  simp only [gaussianHeightPolynomial,BinaryGaussianAverage.gaussianHeight,CurrentGaussianBits.budget,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_ofNat]

 theorem termHeightPolynomial_eval (edges gh th : Polynomial ℕ) (security : ℕ) :
    (termHeightPolynomial edges gh th).eval security = BinarySparseCycleTermResources.termHeight
      (edges.eval security) (gh.eval security) (th.eval security) := by
  simp only [termHeightPolynomial,BinarySparseCycleTermResources.termHeight,Polynomial.eval_add,Polynomial.eval_mul]

 theorem termPolynomial_eval (edges count cutoff gh th tw : Polynomial ℕ) (security : ℕ) :
    (termPolynomial edges count cutoff gh th tw).eval security = BinarySparseCycleTermResources.termWork
      (edges.eval security) (count.eval security) (cutoff.eval security) (gh.eval security) (th.eval security) (tw.eval security) := by
  simp only [termPolynomial,rootsPolynomial,rootEntryPolynomial,weightPolynomial,termHeightPolynomial_eval,
    BinarySparseCycleTermResources.termWork,BinarySparseCycleTermResources.rootsWork,
    BinarySparseCycleTermResources.rootEntryWork,BinarySparseCycleTermResources.weightEntryWork,BinaryFiniteProduct.work,
    RationalBits.primitiveWorkPolynomial_eval,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat,Polynomial.eval_one]
  omega


def heightPolynomial (limit : ℕ) (cutoff precision testHeight : Polynomial ℕ) : Polynomial ℕ :=
  ∑ edges ∈ Finset.range (2*limit+1), BinaryTupleSum.heightPolynomial (2*cutoff+1) edges
    (termHeightPolynomial (Polynomial.C (2*limit)) (gaussianHeightPolynomial precision) testHeight)


def workPolynomial (limit : ℕ) (body cutoff precision testHeight testWork : Polynomial ℕ) : Polynomial ℕ :=
  preparePolynomial body (Polynomial.C limit)+Polynomial.C (2*limit)+positionsPolynomial body (Polynomial.C limit)+
    CurrentGaussianBits.workPolynomial precision+
    (∑ edges ∈ Finset.range (2*limit+1), BinaryTupleSum.workPolynomial (2*cutoff+1) edges
      (termHeightPolynomial (Polynomial.C (2*limit)) (gaussianHeightPolynomial precision) testHeight)
      (termPolynomial (Polynomial.C (2*limit)) (Polynomial.C limit) cutoff (gaussianHeightPolynomial precision) testHeight testWork))+5

 theorem heightPolynomial_eval (limit : ℕ) (cutoff precision th : Polynomial ℕ) (security : ℕ) :
    (heightPolynomial limit cutoff precision th).eval security =
      heightLimit security (precision.eval security) limit (cutoff.eval security) (th.eval security) := by
  simp only [heightPolynomial,heightLimit,Polynomial.eval_finset_sum,BinaryTupleSum.heightPolynomial_eval,
    termHeightPolynomial_eval,gaussianHeightPolynomial_eval,Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_ofNat,Polynomial.eval_one]

 theorem workPolynomial_eval (limit : ℕ) (body cutoff precision th tw : Polynomial ℕ) (security : ℕ) :
    (workPolynomial limit body cutoff precision th tw).eval security =
      workLimit security (precision.eval security) (body.eval security) limit (cutoff.eval security) (th.eval security) (tw.eval security) := by
  simp only [workPolynomial,workLimit,Polynomial.eval_finset_sum,BinaryTupleSum.workPolynomial_eval,
    preparePolynomial_eval,positionsPolynomial_eval,termHeightPolynomial_eval,termPolynomial_eval,
    gaussianHeightPolynomial_eval,CurrentGaussianBits.workPolynomial_eval,Polynomial.eval_C,Polynomial.eval_add,
    Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one]

 theorem current_polynomial_bounds {body count : ℕ} (security cutoff limit : ℕ) (hb : 0 < body)
    (sites : Vector (Fin body) count) (bodyBound cutoffBound precision th tw : Polynomial ℕ)
    (hbody : body ≤ bodyBound.eval security) (hcount : count ≤ limit)
    (hcutoff : cutoff ≤ (security+2)^2) (hupper : cutoff ≤ cutoffBound.eval security)
    (test : Vector IntegerBits count → RationalResult)
    (htest : ∀ roots, (∀ slot, (roots.get slot).digits.length ≤ 2*cutoff+2) →
      HeightBound (test roots).data.decode (th.eval security) ∧ (test roots).work ≤ tw.eval security) :
    HeightBound (BinarySparseCycleEvaluation.current security cutoff (precision.eval security) hb sites test).data.decode
      ((heightPolynomial limit cutoffBound precision th).eval security) ∧
    (BinarySparseCycleEvaluation.current security cutoff (precision.eval security) hb sites test).work ≤
      (workPolynomial limit bodyBound cutoffBound precision th tw).eval security := by
  have h := current_bounds security cutoff (precision.eval security) limit (cutoffBound.eval security) (th.eval security) (tw.eval security)
    hb sites hcount hcutoff hupper test htest
  rw [heightPolynomial_eval,workPolynomial_eval]
  exact ⟨h.1,h.2.trans (workLimit_mono_body hbody)⟩

end
end CurrentAFT.BinarySparseCyclePolynomial
