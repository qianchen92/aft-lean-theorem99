import CurrentAFT.BinaryProposalMetadata
import CurrentAFT.PublicOutputExperiment
import AFT.UnaryPolynomialCounters

/-! Executed current dimensions of every finite public proposal buffer. -/
namespace CurrentAFT.CurrentProposalDimensions
open AFT AFT.BinaryArithmetic
set_option maxHeartbeats 500000

structure Result where
  colors : ℕ
  legs : ℕ
  body : ℕ
  dimension : ℕ
  ordinary : ℕ
  controls : ℕ
  work : ℕ

def current (security : ℕ) : Result :=
  let sizes := BinaryProposalMetadata.counts security
  let doubled := doubleCounter sizes.legs
  let dimension := addCounter sizes.population doubled.count
  let nonqueue := subtractCounter sizes.population sizes.colors
  let ordinary := subtractCounter nonqueue.count doubled.count
  let controls := addCounter sizes.legs ordinary.count
  ⟨sizes.colors, sizes.legs, sizes.population, dimension.count, ordinary.count, controls.count,
    sizes.work + doubled.work + dimension.work + nonqueue.work + ordinary.work + controls.work + 6⟩

theorem current_values (security : ℕ) :
    (current security).colors = Parameters.modulus security ∧
    (current security).legs = Parameters.legCount security ∧
    (current security).body = Parameters.bodySize security ∧
    (current security).dimension = Parameters.dimension security ∧
    (current security).ordinary = BackgroundRates.ordinaryPool security ∧
    (current security).controls = Parameters.legCount security + BackgroundRates.ordinaryPool security := by
  rcases BinaryProposalMetadata.counts_value security with ⟨hq, hl, hb⟩
  have hlegs : (BinaryProposalMetadata.counts security).legs = Parameters.legCount security := by
    rw [hl, Parameters.legCount, Parameters.scale, Parameters.base, ← pow_mul]
  have hbody : (BinaryProposalMetadata.counts security).population = Parameters.bodySize security := by
    rw [hb, Parameters.bodySize, Parameters.scale, Parameters.base, ← pow_mul]
  simp only [current, addCounter_value, subtractCounter_value, doubleCounter_value, hq, hlegs, hbody,
    Parameters.dimension, BackgroundRates.ordinaryPool, and_self]

def controlsEquiv (security : ℕ) : Fin (current security).controls ≃ PublicOutputExperiment.PublicIndex security :=
  (finCongr (current_values security).2.2.2.2.2).trans finSumFinEquiv.symm

def legEquiv (security : ℕ) : Fin (current security).legs ≃ Fin (Parameters.legCount security) :=
  finCongr (current_values security).2.1

def queueEquiv (security : ℕ) : Fin (current security).colors ≃ Fin (Parameters.modulus security) :=
  finCongr (current_values security).1

def bodyEquiv (security : ℕ) : Fin (current security).body ≃ ActualCycleMeanMGF.BodyIndex security :=
  finCongr (current_values security).2.2.1

def endpointEquiv (security : ℕ) : Fin (current security).dimension ≃ Fin (Parameters.dimension security) :=
  finCongr (current_values security).2.2.2.1

end CurrentAFT.CurrentProposalDimensions
