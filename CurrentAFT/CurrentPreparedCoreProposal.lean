import CurrentAFT.CurrentCorePolynomialWork
import CurrentAFT.CurrentMaterializedCore
import CurrentAFT.CurrentProposalPrecision

/-! A complete public proposal program: it generates the shared rational
reference cache, prepares its safe restriction, then emits the materialized
core buffers. Its runtime is bounded by an explicit polynomial for any fixed
polynomial choices of table and fair-bit precision. -/
namespace CurrentAFT.CurrentPreparedCoreProposal
open AFT AFT.BinaryArithmetic AFT.RationalNumerics AFT.RationalRejectionProgram
open CurrentReferenceDraw CurrentCoreProposal CurrentProposalResources
open scoped BigOperators Polynomial
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
attribute [local irreducible] CurrentCoreProposal.draw BinaryReferenceTables.current
  CurrentReferenceDraw.counts PublicParameterProgram.modulus


def draw (security tableBits bits : ℕ) (word : Tapes security bits) : CountedValue (MaterializedCore security) :=
  let reference := BinaryReferenceTables.current security tableBits
  let cache := prepare security tableBits reference rfl
  let result := CurrentCoreProposal.draw security tableBits bits cache.value word
  ⟨result.value, reference.work + cache.work + result.work + 3⟩

noncomputable section
open scoped Classical

noncomputable def preparePolynomial : Polynomial ℕ :=
  CurrentReferenceCacheWork.countsWorkPolynomial + countPolynomial * (5 * countPolynomial + 8) + 5

 theorem prepare_polynomial_work (security bits : ℕ) (input : BinaryReferenceTables.Result security)
    (hinput : input = BinaryReferenceTables.current security bits) :
    (prepare security bits input hinput).work ≤ preparePolynomial.eval security := by
  have h := CurrentReferenceCacheWork.prepare_work security bits input hinput
  rcases CurrentReferenceCacheWork.native_bounds security with ⟨hq, hs, hm⟩
  have hd : centerDataWork security ≤ countPolynomial.eval security * (5 * countPolynomial.eval security + 8) + 2 := by
    unfold centerDataWork
    gcongr
    omega
  simp only [preparePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
  omega

noncomputable def workPolynomial (tablePrecision drawPrecision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryReferenceTables.currentWorkPolynomial tablePrecision + preparePolynomial +
    CurrentCorePolynomialWork.workPolynomial (BinaryReferenceTables.heightPolynomial tablePrecision) drawPrecision + 3

 theorem polynomial_work (security : ℕ) (tablePrecision drawPrecision : Polynomial ℕ)
    (word : Tapes security (drawPrecision.eval security)) :
    (draw security (tablePrecision.eval security) (drawPrecision.eval security) word).work ≤
      (workPolynomial tablePrecision drawPrecision).eval security := by
  let input := BinaryReferenceTables.current security (tablePrecision.eval security)
  let cache := prepare security (tablePrecision.eval security) input rfl
  let result := CurrentCoreProposal.draw security (tablePrecision.eval security) (drawPrecision.eval security) cache.value word
  have hc := BinaryReferenceTables.current_bounds security tablePrecision
  have hh := CurrentReferenceCacheWork.prepare_heights security tablePrecision
  have hp := prepare_polynomial_work security (tablePrecision.eval security) input rfl
  have hd := CurrentCorePolynomialWork.draw_polynomial_work security (tablePrecision.eval security)
    (BinaryReferenceTables.heightPolynomial tablePrecision) drawPrecision cache.value hh.1 hh.2.1 hh.2.2 word
  have hi := hc.2.2.2.2
  change input.work ≤ _ at hi
  change cache.work ≤ _ at hp
  change result.work ≤ _ at hd
  change input.work + cache.work + result.work + 3 ≤ _
  simp only [workPolynomial, Polynomial.eval_add, Polynomial.eval_ofNat]
  omega

noncomputable def cache (security tableBits : ℕ) : Cache security tableBits :=
  (prepare security tableBits (BinaryReferenceTables.current security tableBits) rfl).value

noncomputable def law (security tableBits bits : ℕ) : FiniteDist (MaterializedCore security) :=
  (CurrentCoreProposalLaw.tapeLaw security bits).map (fun word => (draw security tableBits bits word).value)

 theorem law_core (security tableBits bits : ℕ) :
    (law security tableBits bits).map MaterializedCore.core =
      CurrentCoreProposalLaw.law security tableBits bits (cache security tableBits) := by
  rw [law, FiniteDist.map_map]
  rfl

 theorem proposal_l1 (security bits : ℕ) :
    (∑ core, |((law security (CurrentProposalPrecision.tableBits security bits) bits).map MaterializedCore.core).weight core -
      (ActualPublicCharge.proposal security).weight core|) ≤
      CurrentCoreProposalRates.error security (CurrentProposalPrecision.tableBits security bits) bits := by
  rw [law_core]
  exact CurrentProposalPrecision.proposal_l1 security bits (cache security _)

end
end CurrentAFT.CurrentPreparedCoreProposal
