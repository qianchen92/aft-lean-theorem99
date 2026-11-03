import CurrentAFT.BinaryProposalMetadata
import CurrentAFT.RationalBackgroundPopulationProgram

/-! # Executed current counts for all three actual background populations -/
namespace CurrentAFT.BinaryBackgroundPopulationCounts
open AFT RationalNumerics BinaryArithmetic
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryProposalMetadata.counts differenceCounter

structure Counts where
  free : ℕ
  queue : ℕ
  leg : ℕ
  work : ℕ

def current (security : ℕ) : Counts :=
  let sizes := BinaryProposalMetadata.counts security
  let noLegs := differenceCounter sizes.population sizes.legs
  let free := differenceCounter noLegs.count sizes.colors
  ⟨free.count,sizes.colors,sizes.legs,sizes.work+noLegs.work+free.work+3⟩

theorem current_value (security : ℕ) :
    (current security).free=RationalBackgroundPopulationProgram.freeCount security ∧
    (current security).queue=(PublicParameterProgram.modulus security).count ∧
    (current security).leg=(security+2)^128 := by
  rcases BinaryProposalMetadata.counts_value security with ⟨hq,hl,hp⟩
  simp only [current,differenceCounter_value,hq,hl,hp,RationalBackgroundPopulationProgram.freeCount,PublicParameterProgram.modulus_value,and_self]

theorem current_sizes (security : ℕ) :
    (current security).free ≤ BinaryProposalMetadata.sizeBound security ∧
    (current security).queue ≤ BinaryProposalMetadata.sizeBound security ∧
    (current security).leg ≤ BinaryProposalMetadata.sizeBound security := by
  rcases BinaryProposalMetadata.counts_bounds security with ⟨hq,hl,hp⟩
  constructor
  · change (differenceCounter (differenceCounter _ _).count _).count ≤ _
    rw [differenceCounter_value,differenceCounter_value]
    omega
  · exact ⟨hq,hl⟩

noncomputable def workPolynomial : Polynomial ℕ := BinaryProposalMetadata.countsWorkPolynomial+4*BinaryProposalMetadata.sizePolynomial+5

theorem current_work (security : ℕ) : (current security).work ≤ workPolynomial.eval security := by
  let sizes := BinaryProposalMetadata.counts security
  let noLegs := differenceCounter sizes.population sizes.legs
  let free := differenceCounter noLegs.count sizes.colors
  have hs := BinaryProposalMetadata.counts_bounds security
  have hn : noLegs.count ≤ BinaryProposalMetadata.sizeBound security := by
    rw [differenceCounter_value]
    exact (Nat.sub_le _ _).trans (BinaryProposalMetadata.counts_bounds security).2.2
  have ws := BinaryProposalMetadata.counts_work security
  have wn := differenceCounter_work sizes.population sizes.legs
  have wf := differenceCounter_work noLegs.count sizes.colors
  change sizes.work+noLegs.work+free.work+3 ≤ _
  change sizes.work ≤ _ at ws
  change noLegs.work ≤ _ at wn
  change free.work ≤ _ at wf
  change sizes.colors ≤ _ ∧ sizes.legs ≤ _ ∧ sizes.population ≤ _ at hs
  simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
    BinaryProposalMetadata.countsWorkPolynomial_eval,BinaryProposalMetadata.sizePolynomial_eval]
  omega

end CurrentAFT.BinaryBackgroundPopulationCounts
