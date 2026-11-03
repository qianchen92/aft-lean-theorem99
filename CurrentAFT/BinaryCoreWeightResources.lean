import CurrentAFT.BinaryCoreWeightData
import CurrentAFT.CurrentProposalResources

/-! Full public-buffer reads and true current weight evaluation resources. -/
namespace CurrentAFT.BinaryCoreWeightData
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram CurrentCoreProposal CurrentProposalDimensions
  CurrentProposalResources BinaryWeightLocal
noncomputable section
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current BinaryWeightProgram.current

theorem ordinary_bound (security : ℕ) : (CurrentProposalDimensions.current security).ordinary ≤ countPolynomial.eval security := by
  have hc := (count_bounds security).1
  have hl := (current_values security).2.1
  have ho := (current_values security).2.2.2.2.1
  have ht := (current_values security).2.2.2.2.2
  omega

def entryWorkPolynomial : Polynomial ℕ := metadataWorkPolynomial+5*countPolynomial+8
def gatherWorkPolynomial : Polynomial ℕ := metadataWorkPolynomial+countPolynomial*(entryWorkPolynomial+2)+4

theorem primaryEntry_work (security : ℕ) (data : MaterializedCore security)
    (index : Fin (CurrentProposalDimensions.current security).legs) :
    (primaryEntry security data index).work ≤ entryWorkPolynomial.eval security := by
  have hr := readVector_work (defaultControl security) data.controls (primaryAddress security index)
  have hc := (count_bounds security).1
  change (readVector (defaultControl security) data.controls (primaryAddress security index)).work+2 ≤ _
  simp only [entryWorkPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
  omega

theorem ordinaryEntry_work (security : ℕ) (data : MaterializedCore security)
    (index : Fin (CurrentProposalDimensions.current security).ordinary) :
    (ordinaryEntry security data index).work ≤ entryWorkPolynomial.eval security := by
  have ha := addCounter_work (CurrentProposalDimensions.current security).legs index.val
  have hr := readVector_work (defaultControl security) data.controls (ordinaryAddress security index).value
  have hc := (count_bounds security).1
  have hl := (count_bounds security).2.1
  have hm := metadata_work security
  change (CurrentProposalDimensions.current security).work+
    (addCounter (CurrentProposalDimensions.current security).legs index.val).work+2+
    (readVector (defaultControl security) data.controls (ordinaryAddress security index).value).work+2 ≤ _
  simp only [entryWorkPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
  omega

theorem groups_work (security : ℕ) (data : MaterializedCore security) :
    (groups security data).work ≤ gatherWorkPolynomial.eval security := by
  have hw := storeData_work (CurrentProposalDimensions.current security).legs (entryWorkPolynomial.eval security)
    (primaryEntry security data) (primaryEntry_work security data)
  have hm := metadata_work security
  have hc := (count_bounds security).2.1
  have ht := Nat.mul_le_mul_right (entryWorkPolynomial.eval security+2) hc
  change (CurrentProposalDimensions.current security).work+(storeData _ (primaryEntry security data)).work+2 ≤ _
  simp only [gatherWorkPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
  omega

theorem centers_work (security : ℕ) (data : MaterializedCore security) :
    (centers security data).work ≤ gatherWorkPolynomial.eval security := by
  have hw := storeData_work (CurrentProposalDimensions.current security).ordinary (entryWorkPolynomial.eval security)
    (ordinaryEntry security data) (ordinaryEntry_work security data)
  have hm := metadata_work security
  have hc := ordinary_bound security
  have ht := Nat.mul_le_mul_right (entryWorkPolynomial.eval security+2) hc
  change (CurrentProposalDimensions.current security).work+(storeData _ (ordinaryEntry security data)).work+2 ≤ _
  simp only [gatherWorkPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
  omega

def heightPolynomial (order : ℕ) (precision tableBound : Polynomial ℕ) : Polynomial ℕ :=
  BinaryWeightResources.outputHeightPolynomial BinaryPrimaryTable.countPolynomial countPolynomial countPolynomial
    precision tableBound order

def workPolynomial (order : ℕ) (precision tableBound : Polynomial ℕ) : Polynomial ℕ :=
  metadataWorkPolynomial+2*gatherWorkPolynomial+
    BinaryWeightResources.currentWorkPolynomial BinaryPrimaryTable.countPolynomial countPolynomial countPolynomial
      precision tableBound order+4

theorem polynomial_bounds (security order : ℕ) (precision tableBound : Polynomial ℕ)
    (table : BinaryWeightCoordinates.Table (colors security) order) (data : MaterializedCore security)
    (ht : ∀ block word, HeightBound ((table.get block).get word).decode (tableBound.eval security)) :
    HeightBound (current security (precision.eval security) order table data).value.decode
        ((heightPolynomial order precision tableBound).eval security) ∧
      (current security (precision.eval security) order table data).work ≤
        (workPolynomial order precision tableBound).eval security := by
  have hv := BinaryWeightResources.current_polynomial_bounds security order
    (CurrentProposalDimensions.current security).legs (CurrentProposalDimensions.current security).ordinary
    (primaryPool_pos security) (bodyPool_pos security) BinaryPrimaryTable.countPolynomial countPolynomial countPolynomial
    precision tableBound (BinaryPrimaryTable.count_bound security) (count_bounds security).2.1 (ordinary_bound security)
    table (groups security data).value (centers security data).value ht
  have hm := metadata_work security
  have hg := groups_work security data
  have hb := centers_work security data
  constructor
  · exact hv.1
  · change (CurrentProposalDimensions.current security).work+(groups security data).work+(centers security data).work+
      (BinaryWeightProgram.current security (precision.eval security) order
        (CurrentProposalDimensions.current security).legs (CurrentProposalDimensions.current security).ordinary
        (primaryPool_pos security) (bodyPool_pos security) table (groups security data).value (centers security data).value).work+4 ≤ _
    simp only [workPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
    omega

end
end CurrentAFT.BinaryCoreWeightData
