import CurrentAFT.BinaryPublicRejection
import AFT.BinarySamplingPolynomials

/-! Polynomial work of the complete proposal, actual joint score, charge,
binary acceptance and all random-tape array reads in the capped loop. -/
namespace CurrentAFT.BinaryPublicRejection
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram CurrentCoreProposal
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryCoreWeightData.current BinaryCoreCharge.current CurrentPreparedCoreProposal.draw

def sampleWorkPolynomial (tablePrecision drawPrecision : Polynomial ℕ) : Polynomial ℕ :=
  CurrentPreparedCoreProposal.workPolynomial tablePrecision drawPrecision+1
def scoreWorkPolynomial (order : ℕ) (weightPrecision tableBound : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCoreWeightData.workPolynomial order weightPrecision tableBound+BinaryCoreCharge.workPolynomial+3

theorem sample_work (security : ℕ) (tablePrecision drawPrecision : Polynomial ℕ)
    (word : Tapes security (drawPrecision.eval security)) :
    (sample security (tablePrecision.eval security) (drawPrecision.eval security) word).work ≤
      (sampleWorkPolynomial tablePrecision drawPrecision).eval security := by
  exact (Nat.add_le_add_right (CurrentPreparedCoreProposal.polynomial_work security tablePrecision drawPrecision word) 1).trans_eq
    (by simp only [sampleWorkPolynomial, Polynomial.eval_add, Polynomial.eval_one])

theorem score_bounds (security order : ℕ) (weightPrecision tableBound : Polynomial ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order)
    (ht : ∀ block word, HeightBound ((table.get block).get word).decode (tableBound.eval security))
    (input : Option (MaterializedCore security)) :
    HeightBound (score security (weightPrecision.eval security) order table input).value.decode
        ((BinaryCoreWeightData.heightPolynomial order weightPrecision tableBound).eval security) ∧
      (score security (weightPrecision.eval security) order table input).work ≤
        (scoreWorkPolynomial order weightPrecision tableBound).eval security := by
  cases input with
  | none =>
    constructor
    · exact HeightBound.zero.mono (Nat.zero_le _)
    · change 1 ≤ _
      simp only [scoreWorkPolynomial, Polynomial.eval_add, Polynomial.eval_ofNat]
      omega
  | some core =>
    have hv := BinaryCoreWeightData.polynomial_bounds security order weightPrecision tableBound table core ht
    have hc := BinaryCoreCharge.polynomial_work security core
    constructor
    · change HeightBound (if (BinaryCoreCharge.current security core).value = true then
        (BinaryCoreWeightData.current security (weightPrecision.eval security) order table core).value else RationalBits.zero).decode _
      split_ifs
      · exact hv.1
      · exact HeightBound.zero.mono (Nat.zero_le _)
    · change (BinaryCoreWeightData.current security (weightPrecision.eval security) order table core).work+
        (BinaryCoreCharge.current security core).work+3 ≤ _
      simp only [scoreWorkPolynomial, Polynomial.eval_add, Polynomial.eval_ofNat]
      omega

def acceptanceWorkPolynomial (height bits : Polynomial ℕ) : Polynomial ℕ :=
  dyadicFloorWorkPolynomial height bits+50*(height+bits+1)+20

theorem acceptanceWorkPolynomial_eval (height bits : Polynomial ℕ) (security : ℕ) :
    (acceptanceWorkPolynomial height bits).eval security = binaryAcceptanceWork (height.eval security) (bits.eval security) := by
  simp only [acceptanceWorkPolynomial, binaryAcceptanceWork, dyadicFloorWorkPolynomial_eval,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one]

def stepWorkPolynomial (order : ℕ) (tablePrecision drawPrecision weightPrecision coinPrecision tableBound : Polynomial ℕ) : Polynomial ℕ :=
  let height := BinaryCoreWeightData.heightPolynomial order weightPrecision tableBound
  sampleWorkPolynomial tablePrecision drawPrecision+scoreWorkPolynomial order weightPrecision tableBound+
    2*RationalBits.primitiveWorkPolynomial (height+2)+acceptanceWorkPolynomial (height+2) coinPrecision+9

def workPolynomial (order : ℕ) (tablePrecision drawPrecision weightPrecision coinPrecision tableBound cap : Polynomial ℕ) : Polynomial ℕ :=
  542+cap*(stepWorkPolynomial order tablePrecision drawPrecision weightPrecision coinPrecision tableBound+
    (cap+1)*(3*cap+5)+15)

theorem polynomial_work (security order attempts : ℕ)
    (tablePrecision drawPrecision weightPrecision coinPrecision tableBound cap : Polynomial ℕ)
    (hcap : attempts ≤ cap.eval security)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order)
    (ht : ∀ block word, HeightBound ((table.get block).get word).decode (tableBound.eval security))
    (words : Vector (Tapes security (drawPrecision.eval security) × (Fin (coinPrecision.eval security) → Fin 2)) attempts) :
    (current security (tablePrecision.eval security) (drawPrecision.eval security) (weightPrecision.eval security)
      (coinPrecision.eval security) order attempts table words).work ≤
      (workPolynomial order tablePrecision drawPrecision weightPrecision coinPrecision tableBound cap).eval security := by
  let H := (BinaryCoreWeightData.heightPolynomial order weightPrecision tableBound).eval security
  let P := (sampleWorkPolynomial tablePrecision drawPrecision).eval security
  let W := (scoreWorkPolynomial order weightPrecision tableBound).eval security
  have he : HeightBound (RationalBits.ofCounter 2).data.decode 2 := by
    rw [RationalBits.ofCounter_value]
    exact HeightBound.nat_coarse 2
  have h := BinaryArrayRejection.run_work_limit
    (sample security (tablePrecision.eval security) (drawPrecision.eval security))
    (score security (weightPrecision.eval security) order table) (RationalBits.ofCounter 2).data
    (coinPrecision.eval security) ⟨none, 1⟩ P W H 2
    (sample_work security tablePrecision drawPrecision)
    (fun point => (score_bounds security order weightPrecision tableBound table ht point).2)
    (fun point => (score_bounds security order weightPrecision tableBound table ht point).1)
    he attempts (cap.eval security) hcap words
  have hw : (RationalBits.ofCounter 2).work ≤ 540 := (RationalBits.ofCounter_work 2).trans_eq (by norm_num)
  have hstep : (stepWorkPolynomial order tablePrecision drawPrecision weightPrecision coinPrecision tableBound).eval security =
      binaryRejectionStepWork P W H 2 (coinPrecision.eval security) := by
    simp only [stepWorkPolynomial, binaryRejectionStepWork, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_ofNat, acceptanceWorkPolynomial_eval, RationalBits.primitiveWorkPolynomial_eval, H, P, W]
  have hcount := Nat.mul_le_mul_right
    (binaryRejectionStepWork P W H 2 (coinPrecision.eval security)+BinaryArrayRejection.overhead (cap.eval security)) hcap
  change (RationalBits.ofCounter 2).work+
    (BinaryArrayRejection.run (sample security (tablePrecision.eval security) (drawPrecision.eval security))
      (score security (weightPrecision.eval security) order table) (RationalBits.ofCounter 2).data
      (coinPrecision.eval security) ⟨none, 1⟩ attempts words).work+1 ≤ _
  simp only [workPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, hstep]
  unfold BinaryArrayRejection.overhead at h hcount
  dsimp only at h
  simp only [Nat.add_assoc] at h hcount ⊢
  omega

def drawWorkPolynomial (order : ℕ) (tablePrecision drawPrecision weightPrecision coinPrecision tableBound cap : Polynomial ℕ) : Polynomial ℕ :=
  workPolynomial order tablePrecision drawPrecision weightPrecision coinPrecision tableBound cap+3*cap+4

theorem draw_polynomial_work (security order attempts : ℕ)
    (tablePrecision drawPrecision weightPrecision coinPrecision tableBound cap : Polynomial ℕ)
    (hcap : attempts ≤ cap.eval security)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order)
    (ht : ∀ block word, HeightBound ((table.get block).get word).decode (tableBound.eval security))
    (words : Fin attempts → Tapes security (drawPrecision.eval security) × (Fin (coinPrecision.eval security) → Fin 2)) :
    (draw security (tablePrecision.eval security) (drawPrecision.eval security) (weightPrecision.eval security)
      (coinPrecision.eval security) order attempts table words).work ≤
      (drawWorkPolynomial order tablePrecision drawPrecision weightPrecision coinPrecision tableBound cap).eval security := by
  have h := polynomial_work security order attempts tablePrecision drawPrecision weightPrecision coinPrecision tableBound cap hcap table ht
    (storeData attempts (fun index => ⟨words index, 1⟩)).value
  have hs := storeData_work attempts 1 (fun index => (⟨words index, 1⟩ : CountedValue _)) (fun _ => le_rfl)
  change (storeData attempts (fun index => (⟨words index, 1⟩ : CountedValue _))).work+
    (current security (tablePrecision.eval security) (drawPrecision.eval security) (weightPrecision.eval security)
      (coinPrecision.eval security) order attempts table (storeData attempts (fun index => ⟨words index, 1⟩)).value).work+2 ≤ _
  simp only [drawWorkPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
  omega

end
end CurrentAFT.BinaryPublicRejection
