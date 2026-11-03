import CurrentAFT.BinaryRootReferenceResources

/-! Closed fixed-order resources for centered joint cycle masses. The reference
atoms are computed and cached; no atom reciprocal or joint factorization occurs. -/
namespace CurrentAFT.BinaryRootSignedMassResources
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
open CurrentProposalResources BinaryRootSignedMass
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus


def referenceCacheWorkPolynomial (limit : ℕ) (precision : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C limit*(Polynomial.C (3*limit)+BinaryRootReferenceResources.workPolynomial precision+7)+2

 theorem references_bounds {count : ℕ} (security limit : ℕ) (precision : Polynomial ℕ)
    (output : Vector ℕ count) (hcount : count ≤ limit)
    (hout : ∀ slot, output.get slot ≤ primeSizePolynomial.eval security) :
    (∀ slot, HeightBound ((references security (precision.eval security) output).value.get slot).decode
      ((BinaryRootReferenceResources.heightPolynomial precision).eval security)) ∧
    (references security (precision.eval security) output).work ≤
      (referenceCacheWorkPolynomial limit precision).eval security := by
  have hh (slot : Fin count) := BinaryRootReferenceResources.referenceEntry_polynomial_bounds security precision (output.get slot) (hout slot)
  constructor
  · intro slot
    simpa only [references,storeData_get,readVector_value] using (hh slot).1
  · have hw := storeData_work count (3*count+(BinaryRootReferenceResources.workPolynomial precision).eval security+5)
      (fun slot =>
        let expected := readVector 0 output slot
        let mass := referenceEntry security (precision.eval security) expected.value
        (⟨mass.data,expected.work+mass.work+2⟩ : CountedValue RationalBits)) (by
          intro slot
          have hr := readVector_work 0 output slot
          have hm := (hh slot).2
          simp only [readVector_value]
          change _+_+2 ≤ _
          omega)
    apply hw.trans
    simp only [referenceCacheWorkPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_ofNat]
    exact Nat.add_le_add_right (Nat.mul_le_mul hcount (by omega)) 2


def factorPolynomial (count : ℕ) (precision : Polynomial ℕ) : Polynomial ℕ :=
  let R := BinaryRootReferenceResources.rootBitsPolynomial
  let Q := primeSizePolynomial
  Polynomial.C (9*count)+(60*(R+Q+1)^2+50*(Q+1)^2+48*(R+Q+Q)+50)+
    2*RationalBits.primitiveWorkPolynomial (BinaryRootReferenceResources.heightPolynomial precision+1)+20

 theorem factorPolynomial_eval (count security : ℕ) (precision : Polynomial ℕ) :
    (factorPolynomial count precision).eval security =
      BinaryCycleTestResources.factorWork count (2*(security+2)^2+2)
        (primeSizePolynomial.eval security) (primeSizePolynomial.eval security)
        ((BinaryRootReferenceResources.heightPolynomial precision).eval security) := by
  simp only [factorPolynomial,BinaryRootReferenceResources.rootBitsPolynomial,BinaryRootReferenceResources.cutoffPolynomial,
    BinaryCycleTestResources.factorWork,BinaryCycleTestResources.matchWork,RationalBits.primitiveWorkPolynomial_eval,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_C,Polynomial.eval_X,
    Polynomial.eval_ofNat,Polynomial.eval_one]


def testHeightPolynomial (limit : ℕ) (precision : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C limit*(BinaryRootReferenceResources.heightPolynomial precision+1)

def testWorkPolynomial (limit : ℕ) (precision : Polynomial ℕ) : Polynomial ℕ :=
  ∑ count ∈ Finset.range (limit+1), BinaryFiniteProduct.workPolynomial count
    (BinaryRootReferenceResources.heightPolynomial precision+1) (factorPolynomial count precision)

 theorem signed_test_bounds {count : ℕ} (security limit : ℕ) (precision : Polynomial ℕ)
    (output : Vector ℕ count) (hcount : count ≤ limit)
    (hout : ∀ slot, output.get slot ≤ primeSizePolynomial.eval security)
    (roots : Vector IntegerBits count)
    (hr : ∀ slot, (roots.get slot).digits.length ≤
      2*(CurrentEdgeDrawProgram.cutoffProgram security).quotient+2) :
    HeightBound (BinaryCycleTest.signed
      (canonicalCounter (PublicParameterProgram.modulus security).count).digits output
      (references security (precision.eval security) output).value roots).data.decode
      ((testHeightPolynomial limit precision).eval security) ∧
    (BinaryCycleTest.signed (canonicalCounter (PublicParameterProgram.modulus security).count).digits output
      (references security (precision.eval security) output).value roots).work ≤
      (testWorkPolynomial limit precision).eval security := by
  have hcut := BinaryRootReferenceResources.cutoff_bound security
  have hs := BinaryCycleTestResources.signed_bounds
    (canonicalCounter (PublicParameterProgram.modulus security).count).digits output
    (references security (precision.eval security) output).value roots (2*(security+2)^2+2)
    (primeSizePolynomial.eval security) (primeSizePolynomial.eval security)
    ((BinaryRootReferenceResources.heightPolynomial precision).eval security)
    (fun slot => (hr slot).trans (by omega)) (BinaryRootReferenceResources.code_length security) hout
    (references_bounds security limit precision output hcount hout).1
  constructor
  · apply hs.1.mono
    simp only [testHeightPolynomial,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_one]
    exact Nat.mul_le_mul_right _ hcount
  · have hsingle :
        (BinaryFiniteProduct.workPolynomial count (BinaryRootReferenceResources.heightPolynomial precision+1)
          (factorPolynomial count precision)).eval security ≤ (testWorkPolynomial limit precision).eval security := by
      simp only [testWorkPolynomial,Polynomial.eval_finset_sum]
      exact Finset.single_le_sum (a := count) (s := Finset.range (limit+1))
        (f := fun n => (BinaryFiniteProduct.workPolynomial n (BinaryRootReferenceResources.heightPolynomial precision+1)
          (factorPolynomial n precision)).eval security) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
    apply hs.2.trans
    rw [BinaryFiniteProduct.workPolynomial_eval,factorPolynomial_eval] at hsingle
    simpa only [Polynomial.eval_add,Polynomial.eval_one] using hsingle


def heightPolynomial (limit : ℕ) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinarySparseCycleAveragePolynomial.heightPolynomial limit BinaryRootReferenceResources.bodyPolynomial
    BinaryRootReferenceResources.cutoffPolynomial precision (testHeightPolynomial limit precision)

def workPolynomial (limit : ℕ) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRootReferenceResources.bodyWorkPolynomial+CurrentProposalSamplerPolynomial.edgeCutoffWorkPolynomial+
    PublicParameterProgram.workPolynomial+50*(primeSizePolynomial+1)^2+
    referenceCacheWorkPolynomial limit precision+
    BinarySparseCycleAveragePolynomial.workPolynomial limit BinaryRootReferenceResources.bodyPolynomial
      BinaryRootReferenceResources.cutoffPolynomial precision (testHeightPolynomial limit precision) (testWorkPolynomial limit precision)+6

 theorem weightedEntry_polynomial_bounds {count : ℕ} (security limit : ℕ) (precision : Polynomial ℕ)
    (output : Vector ℕ count) (hcount : count ≤ limit)
    (hout : ∀ slot, output.get slot ≤ primeSizePolynomial.eval security) :
    HeightBound (weightedEntry security (precision.eval security) output).data.decode
      ((heightPolynomial limit precision).eval security) ∧
    (weightedEntry security (precision.eval security) output).work ≤ (workPolynomial limit precision).eval security := by
  let body := bodyProgram security
  let cutoff := CurrentEdgeDrawProgram.cutoffProgram security
  let q := PublicParameterProgram.modulus security
  let code := canonicalCounter q.count
  let masses := references security (precision.eval security) output
  let test := BinaryCycleTest.signed code.digits output masses.value
  have ha := BinarySparseCycleAveragePolynomial.current_polynomial_bounds security cutoff.quotient (precision.eval security)
    body.count count limit (bodyProgram_positive security) BinaryRootReferenceResources.bodyPolynomial
    BinaryRootReferenceResources.cutoffPolynomial precision (testHeightPolynomial limit precision) (testWorkPolynomial limit precision)
    rfl (BinaryRootReferenceResources.body_bound security) hcount (BinaryRootReferenceResources.cutoff_bound security)
    (by simpa only [BinaryRootReferenceResources.cutoffPolynomial,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_ofNat] using BinaryRootReferenceResources.cutoff_bound security)
    test (signed_test_bounds security limit precision output hcount hout)
  constructor
  · exact ha.1
  · have hb := BinaryRootReferenceResources.body_polynomial_work security
    have hc := CurrentEdgeDrawProgram.cutoff_work security
    have hq := PublicParameterProgram.modulus_work security
    have he := BinaryRootReferenceResources.code_work security
    have hm := (references_bounds security limit precision output hcount hout).2
    change body.work+cutoff.work+q.work+code.work+masses.work+(BinarySparseCycleAverage.current _ _ _ _ _ _ _).work+6 ≤ _
    simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat,
      Polynomial.eval_one,CurrentProposalSamplerPolynomial.edgeCutoffWorkPolynomial_eval,PublicParameterProgram.workPolynomial_eval] at he ⊢
    dsimp only [body,cutoff,q,code,masses,test] at ha ⊢
    omega

end
end CurrentAFT.BinaryRootSignedMassResources
