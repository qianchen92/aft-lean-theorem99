import CurrentAFT.BinaryPublicRejectionLaw
import CurrentAFT.BinaryProposalPrecision
import CurrentAFT.NumericalProposalRates

/-! A single finite-bit rejection driver computes its own retry cap and
reference-table precision. Its input calibration table is materialized data. -/
namespace CurrentAFT.CappedPublicRejection
open AFT BinaryArithmetic RationalNumerics RationalRejectionProgram CurrentCoreProposal
open ActualPublicCharge
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryPublicRejection.draw BinaryRejectionCap.current BinaryProposalPrecision.current

abbrev Tapes (security : ℕ) := Fin (BinaryRejectionCap.current security).count →
  CurrentCoreProposal.Tapes security security × (Fin security → Fin 2)

def current (security order : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order)
    (word : Tapes security) : CountedValue (Option (MaterializedCore security)) :=
  let cap := BinaryRejectionCap.current security
  let precision := BinaryProposalPrecision.current security security
  let result := BinaryPublicRejection.draw security precision.count security security security order cap.count table word
  ⟨result.value, cap.work+precision.work+result.work+3⟩

theorem current_value (security order : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order) (word : Tapes security) :
    (current security order table word).value =
      (BinaryPublicRejection.draw security (CurrentProposalPrecision.tableBits security security)
        security security security order (BinaryRejectionCap.current security).count table word).value := by
  simp only [current, BinaryProposalPrecision.current_value]

noncomputable section
open scoped Classical
open Polynomial

def tablePrecision : Polynomial ℕ := X+CurrentProposalPrecision.paddingPolynomial

theorem tablePrecision_eval (security : ℕ) :
    tablePrecision.eval security = CurrentProposalPrecision.tableBits security security := by
  simp only [tablePrecision, eval_add, eval_X, CurrentProposalPrecision.paddingPolynomial_eval]

def workPolynomial (order : ℕ) (tableBound : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRejectionCap.workPolynomial+BinaryProposalPrecision.workPolynomial X+
    BinaryPublicRejection.drawWorkPolynomial order tablePrecision X X X tableBound BinaryRejectionCap.countPolynomial+3

theorem polynomial_work (security order : ℕ) (tableBound : Polynomial ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order)
    (ht : ∀ block word, HeightBound ((table.get block).get word).decode (tableBound.eval security))
    (word : Tapes security) :
    (current security order table word).work ≤ (workPolynomial order tableBound).eval security := by
  have hc := BinaryRejectionCap.current_work security
  have hp := BinaryProposalPrecision.polynomial_work security X
  have hd := BinaryPublicRejection.draw_polynomial_work security order (BinaryRejectionCap.current security).count
    tablePrecision X X X tableBound BinaryRejectionCap.countPolynomial (BinaryRejectionCap.count_bound security) table ht
  simp only [eval_X, tablePrecision_eval] at hp hd
  rw [eval_X] at hd
  have hd := hd word
  change (BinaryRejectionCap.current security).work+(BinaryProposalPrecision.current security security).work+
    (BinaryPublicRejection.draw security (BinaryProposalPrecision.current security security).count
      security security security order (BinaryRejectionCap.current security).count table word).work+3 ≤ _
  rw [BinaryProposalPrecision.current_value]
  simp only [workPolynomial, eval_add, eval_ofNat]
  omega

def law (security order : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order) :
    FiniteDist (Option (MaterializedCore security)) :=
  (FiniteDist.uniform (Tapes security)).map (fun word => (current security order table word).value)

theorem law_eq (security order : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order) :
    law security order table = BinaryPublicRejection.law security (CurrentProposalPrecision.tableBits security security)
      security security security order (BinaryRejectionCap.current security).count table := by
  simp only [law, current_value, BinaryPublicRejection.law]

def error (security : ℕ) (weightError : ℝ) : ℝ :=
  ((BinaryRejectionCap.current security).count : ℝ)*
    (CurrentCoreProposalRates.error security (CurrentProposalPrecision.tableBits security security) security/2+
      (1/(2 : ℝ)^security+weightError/2))+Real.exp (-(security : ℝ))

theorem error_nonneg (security : ℕ) (weightError : ℝ) (he : 0 ≤ weightError) : 0 ≤ error security weightError := by
  have hp := NumericalProposalRates.proposal_nonneg security security
  unfold error
  positivity

theorem error_negligible {weightError : ℕ → ℝ} (h : Negligible weightError) :
    Negligible (fun security => error security (weightError security)) := by
  have hp := NumericalWeightRates.negligible_const_mul NumericalProposalRates.proposal_negligible (1/2)
  have hw := NumericalWeightRates.negligible_const_mul h (1/2)
  have hr := NumericalProposalRates.retries_negligible (hp.add (NumericalProposalRates.dyadic_negligible.add hw))
  have ht : Negligible (fun security => Real.exp (-(security : ℝ))) := by
    simpa only [BinaryRejectionCap.timeout_value] using BinaryRejectionCap.timeout_negligible
  convert hr.add ht using 1
  funext security
  unfold error
  ring

theorem core_error (security order : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order)
    (weight : Core security → ℝ) (weightError : ℝ) (he : 0 ≤ weightError)
    (hweight : ∀ core, |(BinaryPublicRejection.coreWeight security security order table core : ℝ)-weight core| ≤ weightError)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security))
    (hmass : 1/(4*(Parameters.modulus security : ℝ)) ≤ publicCoreMass (proposal security) weight (publicCharge security)) :
    FiniteDist.TVBound ((law security order table).map (BinaryPublicRejection.decodeResult security))
      ((positivePublicCoreLaw (proposal security) weight (publicCharge security) hpositive).map some)
      (error security weightError) := by
  rw [law_eq]
  have h := BinaryPublicRejection.core_error security security security security order
    (BinaryRejectionCap.current security).count table weight weightError he hweight hmass
  simpa only [error, BinaryRejectionCap.timeout_value] using h

end
end CurrentAFT.CappedPublicRejection
