import CurrentAFT.BinaryProposalMetadata
import CurrentAFT.UniformTaggedOutput

/-! # Actual counts for full-response choices and root ordinals -/
namespace CurrentAFT.BinaryFullResponseCounts
open AFT RationalNumerics BinaryArithmetic
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryProposalMetadata.counts differenceCounter doubleCounter

structure Counts where
  leg : ℕ
  ordinary : ℕ
  queue : ℕ
  body : ℕ
  work : ℕ

def current (security : ℕ) : Counts :=
  let sizes := BinaryProposalMetadata.counts security
  let noQueue := differenceCounter sizes.population sizes.colors
  let doubled := doubleCounter sizes.legs
  let ordinary := differenceCounter noQueue.count doubled.count
  ⟨sizes.legs,ordinary.count,sizes.colors,sizes.population,
    sizes.work+noQueue.work+doubled.work+ordinary.work+4⟩

theorem current_value (security : ℕ) :
    (current security).leg=Parameters.legCount security ∧
    (current security).ordinary=BackgroundRates.ordinaryPool security ∧
    (current security).queue=Parameters.modulus security ∧
    (current security).body=Parameters.bodySize security := by
  rcases BinaryProposalMetadata.counts_value security with ⟨hq,hl,hp⟩
  simp only [current,differenceCounter_value,doubleCounter_value,hq,hl,hp,BackgroundRates.ordinaryPool,
    Parameters.legCount_eq,Parameters.bodySize_eq,Parameters.base,and_self]

theorem current_sizes (security : ℕ) :
    (current security).leg ≤ BinaryProposalMetadata.sizeBound security ∧
    (current security).ordinary ≤ BinaryProposalMetadata.sizeBound security ∧
    (current security).queue ≤ BinaryProposalMetadata.sizeBound security ∧
    (current security).body ≤ BinaryProposalMetadata.sizeBound security := by
  have h := BinaryProposalMetadata.counts_bounds security
  refine ⟨h.2.1,?_,h.1,h.2.2⟩
  change (differenceCounter (differenceCounter _ _).count _).count ≤ _
  rw [differenceCounter_value,differenceCounter_value]
  omega

theorem body_decomposition (security : ℕ) :
    (current security).leg+((current security).leg+(current security).ordinary)+(current security).queue=(current security).body := by
  rcases current_value security with ⟨hl,ho,hq,hb⟩
  rw [hl,ho,hq,hb]
  have hroom := ProposalPrimary.population_room security
  unfold BackgroundRates.ordinaryPool
  omega

theorem positive (security : ℕ) :
    0<(current security).leg ∧ 0<(current security).ordinary ∧ 0<(current security).queue ∧ 0<(current security).body := by
  rcases current_value security with ⟨hl,ho,hq,hb⟩
  rw [hl,ho,hq,hb]
  have hp : 0<Parameters.legCount security := by rw [Parameters.legCount_eq]; exact pow_pos (Parameters.base_pos security) _
  have ho := BackgroundRates.ordinaryPool_pos security
  have hq := (Parameters.modulus_spec security).2.pos
  have hroom := ProposalPrimary.population_room security
  exact ⟨hp,ho,hq,by omega⟩

noncomputable def workPolynomial : Polynomial ℕ := BinaryProposalMetadata.countsWorkPolynomial+7*BinaryProposalMetadata.sizePolynomial+7

theorem current_work (security : ℕ) : (current security).work ≤ workPolynomial.eval security := by
  let sizes := BinaryProposalMetadata.counts security
  let noQueue := differenceCounter sizes.population sizes.colors
  let doubled := doubleCounter sizes.legs
  let ordinary := differenceCounter noQueue.count doubled.count
  have hs := BinaryProposalMetadata.counts_bounds security
  change sizes.colors ≤ _ ∧ sizes.legs ≤ _ ∧ sizes.population ≤ _ at hs
  have hn : noQueue.count ≤ BinaryProposalMetadata.sizeBound security := by rw [differenceCounter_value]; omega
  have ws := BinaryProposalMetadata.counts_work security
  have wn := differenceCounter_work sizes.population sizes.colors
  have wd := doubleCounter_work sizes.legs
  have wo := differenceCounter_work noQueue.count doubled.count
  change sizes.work ≤ _ at ws
  change noQueue.work ≤ _ at wn
  change doubled.work=_ at wd
  change ordinary.work ≤ _ at wo
  change sizes.work+noQueue.work+doubled.work+ordinary.work+4 ≤ _
  simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
    BinaryProposalMetadata.countsWorkPolynomial_eval,BinaryProposalMetadata.sizePolynomial_eval]
  omega

end CurrentAFT.BinaryFullResponseCounts
