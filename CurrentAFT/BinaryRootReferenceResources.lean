import CurrentAFT.BinaryRootSignedMass
import CurrentAFT.BinaryCycleTestResources
import CurrentAFT.BinarySparseCycleAveragePolynomial
import CurrentAFT.CurrentProposalSamplerPolynomial

/-! Closed current-parameter polynomial resources for the actual binary root
reference atom. The body sites and touched Gaussian words are both executed. -/
namespace CurrentAFT.BinaryRootReferenceResources
open AFT GaussianSource RationalNumerics BinaryArithmetic RationalRejectionProgram
open CurrentProposalResources BinaryRootSignedMass
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus


def bodyPolynomial : Polynomial ℕ := primeSizePolynomial*(Polynomial.X+2)^96

def cutoffPolynomial : Polynomial ℕ := (Polynomial.X+2)^2

def rootBitsPolynomial : Polynomial ℕ := 2*cutoffPolynomial+2


def bodyWorkPolynomial : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+2*Polynomial.X+1+97*(6*(Polynomial.X+3)^98+4)+
    primeSizePolynomial*(2*(Polynomial.X+2)^96+3)+5

 theorem colors_bound (security : ℕ) : (PublicParameterProgram.modulus security).count ≤ primeSizePolynomial.eval security := by
  rw [PublicParameterProgram.modulus_value]
  simpa only [primeSizePolynomial,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,
    Polynomial.eval_ofNat,Parameters.base] using (Parameters.modulus_bounds security).2

 theorem body_bound (security : ℕ) : (bodyProgram security).count ≤ bodyPolynomial.eval security := by
  rw [bodyProgram_value]
  simp only [CurrentCycleEntryProgram.bodyCount,bodyPolynomial,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_ofNat]
  exact Nat.mul_le_mul_right _ (colors_bound security)

 theorem cutoff_bound (security : ℕ) : (CurrentEdgeDrawProgram.cutoffProgram security).quotient ≤ (security+2)^2 := by
  rw [CurrentEdgeDrawProgram.cutoff_value]
  exact (Nat.div_le_self _ 2).trans (by
    simpa only [DiffuseProfiles.edgeCutoff,Parameters.sourceCutoff,Parameters.base] using Nat.sub_le ((security+2)^2) 1)

 theorem body_polynomial_work (security : ℕ) : (bodyProgram security).work ≤ bodyWorkPolynomial.eval security := by
  have hq := PublicParameterProgram.modulus_work security
  rw [← PublicParameterProgram.workPolynomial_eval] at hq
  have hb := addCounter_work security 2
  have hp : (powerCounter (addCounter security 2).count 96).work ≤ powerCounterWork (security+2) 96 := by
    simpa only [addCounter_value] using powerCounter_work (addCounter security 2).count 96
  have hm : (multiplyCounter (PublicParameterProgram.modulus security).count
      (powerCounter (addCounter security 2).count 96).count).work ≤
      primeSizePolynomial.eval security*(2*(security+2)^96+3)+1 := by
    have he := multiplyCounter_work (PublicParameterProgram.modulus security).count
      (powerCounter (addCounter security 2).count 96).count
    apply he.le.trans
    simp only [powerCounter_value,addCounter_value]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (colors_bound security)) 1
  change (PublicParameterProgram.modulus security).work+(addCounter security 2).work+
    (powerCounter (addCounter security 2).count 96).work+(multiplyCounter _ _).work+4 ≤ _
  simp only [bodyWorkPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,
    Polynomial.eval_ofNat,Polynomial.eval_one]
  unfold powerCounterWork at hp
  norm_num only at hp
  rw [show security+2+1=security+3 by omega] at hp
  omega

 theorem code_length (security : ℕ) : (canonicalCounter (PublicParameterProgram.modulus security).count).digits.length ≤ primeSizePolynomial.eval security := by
  rw [canonicalCounter_length]
  exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n := _))).trans (colors_bound security)

 theorem code_work (security : ℕ) : (canonicalCounter (PublicParameterProgram.modulus security).count).work ≤
    (50*(primeSizePolynomial+1)^2).eval security := by
  apply (canonicalCounter_work _).trans
  simp only [Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_ofNat,Polynomial.eval_one]
  gcongr
  exact colors_bound security


def pointWorkPolynomial (count : ℕ) : Polynomial ℕ :=
  let R := rootBitsPolynomial
  let Q := primeSizePolynomial
  Polynomial.C count*(Polynomial.C (6*count)+
    (60*(R+Q+1)^2+50*(Q+1)^2+48*(R+Q+Q)+50)+11)+3

 theorem pointWorkPolynomial_eval (count security : ℕ) : (pointWorkPolynomial count).eval security =
    BinaryCycleTestResources.pointWork count (2*(security+2)^2+2)
      (primeSizePolynomial.eval security) (primeSizePolynomial.eval security) := by
  simp only [pointWorkPolynomial,rootBitsPolynomial,cutoffPolynomial,BinaryCycleTestResources.pointWork,
    BinaryCycleTestResources.matchWork,Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one]


def heightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinarySparseCycleAveragePolynomial.heightPolynomial 1 bodyPolynomial cutoffPolynomial precision 0


def workPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  bodyWorkPolynomial+CurrentProposalSamplerPolynomial.edgeCutoffWorkPolynomial+PublicParameterProgram.workPolynomial+
    50*(primeSizePolynomial+1)^2+
    BinarySparseCycleAveragePolynomial.workPolynomial 1 bodyPolynomial cutoffPolynomial precision 0 (pointWorkPolynomial 1)+11

 theorem referenceEntry_polynomial_bounds (security : ℕ) (precision : Polynomial ℕ) (output : ℕ)
    (hout : output ≤ primeSizePolynomial.eval security) :
    HeightBound (referenceEntry security (precision.eval security) output).data.decode ((heightPolynomial precision).eval security) ∧
      (referenceEntry security (precision.eval security) output).work ≤ (workPolynomial precision).eval security := by
  let body := bodyProgram security
  let cutoff := CurrentEdgeDrawProgram.cutoffProgram security
  let q := PublicParameterProgram.modulus security
  let code := canonicalCounter q.count
  let expected := storeData 1 (fun _ => (⟨output,1⟩ : CountedValue ℕ))
  let test := BinaryCycleTest.point code.digits expected.value
  have htest : ∀ roots, (∀ slot, (roots.get slot).digits.length ≤ 2*cutoff.quotient+2) →
      HeightBound (test roots).data.decode ((0:Polynomial ℕ).eval security) ∧
        (test roots).work ≤ (pointWorkPolynomial 1).eval security := by
    intro roots hr
    have hcut := cutoff_bound security
    change cutoff.quotient ≤ (security+2)^2 at hcut
    have hp := BinaryCycleTestResources.point_bounds code.digits expected.value roots (2*(security+2)^2+2)
      (primeSizePolynomial.eval security) (primeSizePolynomial.eval security)
      (fun slot => (hr slot).trans (by omega)) (code_length security) (fun slot => by rw [storeData_get];exact hout)
    simpa only [pointWorkPolynomial_eval,Polynomial.eval_zero] using hp
  have ha := BinarySparseCycleAveragePolynomial.current_polynomial_bounds security cutoff.quotient (precision.eval security)
    body.count 1 1 (bodyProgram_positive security) bodyPolynomial cutoffPolynomial precision 0 (pointWorkPolynomial 1)
    rfl (body_bound security) le_rfl (cutoff_bound security) (by simpa only [cutoffPolynomial,Polynomial.eval_pow,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_ofNat] using cutoff_bound security) test htest
  constructor
  · exact ha.1
  · have hb := body_polynomial_work security
    have hc := CurrentEdgeDrawProgram.cutoff_work security
    have hq := PublicParameterProgram.modulus_work security
    have he := code_work security
    have hexpected := storeData_work 1 1 (fun _ => (⟨output,1⟩ : CountedValue ℕ)) (fun _ => le_rfl)
    change body.work+cutoff.work+q.work+code.work+expected.work+(BinarySparseCycleAverage.current _ _ _ _ _ _ _).work+6 ≤ _
    simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat,
      Polynomial.eval_one,CurrentProposalSamplerPolynomial.edgeCutoffWorkPolynomial_eval,PublicParameterProgram.workPolynomial_eval] at he ⊢
    change body.work ≤ _ at hb
    change cutoff.work ≤ _ at hc
    change q.work ≤ _ at hq
    change code.work ≤ _ at he
    change expected.work ≤ _ at hexpected
    norm_num only at hexpected
    dsimp only [body,cutoff,q,code,expected,test] at hb hc hq he hexpected ha ⊢
    omega

end
end CurrentAFT.BinaryRootReferenceResources
