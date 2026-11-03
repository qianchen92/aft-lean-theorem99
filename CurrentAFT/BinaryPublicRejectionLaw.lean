import CurrentAFT.BinaryPublicRejectionResources
import CurrentAFT.NumericalPublicCompletion

/-! Probability semantics of the actual binary public rejection program. -/
namespace CurrentAFT.BinaryPublicRejection
open AFT CurrentCoreProposal ActualPublicCharge CurrentPublicCompletion
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension
  CurrentPreparedCoreProposal.draw BinaryPublicRejection.draw RationalWeightProgram.current

theorem proposal_tape_uniform (security bits : ℕ) :
    CurrentCoreProposalLaw.tapeLaw security bits = FiniteDist.uniform (Tapes security bits) := by
  simp only [CurrentCoreProposalLaw.tapeLaw, CurrentCoreProposalLaw.controlTapeLaw,
    CurrentCoreProposalLaw.legTapeLaw, CurrentPublicSeedDraw.tapeLaw,
    ← FiniteDist.uniform_product, FiniteDist.independent_uniform]

def law (security tableBits drawBits weightBits coinBits order attempts : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order) :
    FiniteDist (Option (MaterializedCore security)) :=
  (FiniteDist.uniform (Fin attempts → Tapes security drawBits × (Fin coinBits → Fin 2))).map
    (fun words => (draw security tableBits drawBits weightBits coinBits order attempts table words).value)

def cachedLaw (security tableBits drawBits weightBits coinBits order attempts : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order) :
    FiniteDist (Option (CachedCore security)) :=
  (law security tableBits drawBits weightBits coinBits order attempts table).map (Option.map MaterializedCore.cached)

def coin (security weightBits coinBits order : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order) : Option (Core security) → ℝ :=
  ClippedRejectionCoin.optionCoin coinBits (fun core => decide (publicCharge security core))
    (coreWeight security weightBits order table)

theorem coin_bounds (security weightBits coinBits order : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order) :
    ∀ input, 0 ≤ coin security weightBits coinBits order table input ∧ coin security weightBits coinBits order table input ≤ 1 :=
  ClippedRejectionCoin.option_bounds _ _ _

theorem coin_formula (security weightBits coinBits order : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order) (input : Option (Core security)) :
    RationalAcceptanceCoin.probability coinBits (max (coreScore security weightBits order table input) 0/2) =
      coin security weightBits coinBits order table input := by
  cases input with
  | none => norm_num [coreScore, coin, ClippedRejectionCoin.optionCoin, RationalAcceptanceCoin.probability,
      RationalAcceptanceCoin.count, RationalAcceptanceCoin.clipped]
  | some core =>
    simp only [coreScore, coin, ClippedRejectionCoin.optionCoin, ClippedRejectionCoin.probability,
      ClippedRejectionCoin.raw, decide_eq_true_eq]

theorem core_law (security tableBits drawBits weightBits coinBits order attempts : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order) :
    (law security tableBits drawBits weightBits coinBits order attempts table).map (decodeResult security) =
      (((CurrentPreparedCoreProposal.law security tableBits drawBits).map MaterializedCore.core).map some).cappedRejection
        (coin security weightBits coinBits order table) (coin_bounds security weightBits coinBits order table)
        (CanonicalMoments.pointLaw none) attempts := by
  rw [law, FiniteDist.map_map]
  simp only [draw_value]
  rw [RationalRejectionProgram.positiveDraw, RationalRejectionProgram.draw_law]
  have hp : (FiniteDist.uniform (Tapes security drawBits)).map
      (fun word => some (CurrentPreparedCoreProposal.draw security tableBits drawBits word).value.core) =
      ((CurrentPreparedCoreProposal.law security tableBits drawBits).map MaterializedCore.core).map some := by
    simp only [CurrentPreparedCoreProposal.law, proposal_tape_uniform, FiniteDist.map_map]
  simp only [hp, coin_formula, Nat.cast_ofNat]

theorem cachedLaw_core (security tableBits drawBits weightBits coinBits order attempts : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order) :
    (cachedLaw security tableBits drawBits weightBits coinBits order attempts table).map (Option.map (coreEquiv security)) =
      (law security tableBits drawBits weightBits coinBits order attempts table).map (decodeResult security) := by
  rw [cachedLaw, FiniteDist.map_map]
  congr 1
  funext input
  cases input <;> rfl

theorem core_error (security drawBits weightBits coinBits order attempts : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order)
    (weight : Core security → ℝ) (weightError : ℝ) (he : 0 ≤ weightError)
    (hweight : ∀ core, |(coreWeight security weightBits order table core : ℝ)-weight core| ≤ weightError)
    (hmass : 1/(4*(Parameters.modulus security : ℝ)) ≤ publicCoreMass (proposal security) weight (publicCharge security)) :
    FiniteDist.TVBound
      ((law security (CurrentProposalPrecision.tableBits security drawBits) drawBits weightBits coinBits order attempts table).map
        (decodeResult security))
      ((positivePublicCoreLaw (proposal security) weight (publicCharge security)
        (lt_of_lt_of_le (by
          have hq : (0 : ℝ) < Parameters.modulus security := Nat.cast_pos.mpr (Parameters.modulus_spec security).2.pos
          positivity) hmass)).map some)
      ((attempts : ℝ)*(CurrentCoreProposalRates.error security (CurrentProposalPrecision.tableBits security drawBits) drawBits/2+
        (1/(2 : ℝ)^coinBits+weightError/2)) + Real.exp (-(attempts : ℝ)/(8*(Parameters.modulus security : ℝ)))) := by
  rw [core_law]
  have hp : FiniteDist.TVBound
      ((CurrentPreparedCoreProposal.law security (CurrentProposalPrecision.tableBits security drawBits) drawBits).map MaterializedCore.core)
      (proposal security) (CurrentCoreProposalRates.error security (CurrentProposalPrecision.tableBits security drawBits) drawBits/2) := by
    rw [FiniteDist.tvBound_iff_totalVariation_le, FiniteDist.totalVariation_eq_half_l1]
    exact div_le_div_of_nonneg_right (CurrentPreparedCoreProposal.proposal_l1 security drawBits) (by norm_num)
  exact OptionRejection.approximate_error (proposal security) _ weight (publicCharge security)
    (coin security weightBits coinBits order table) (coin_bounds security weightBits coinBits order table)
    (Parameters.modulus security) _ _ (Nat.cast_pos.mpr (Parameters.modulus_spec security).2.pos) hmass hp
    (ClippedRejectionCoin.option_error coinBits (fun core => decide (publicCharge security core))
      (coreWeight security weightBits order table) weight (publicCharge security) weightError he
      (fun _ => by simp only [decide_eq_true_eq]) hweight) attempts

theorem cached_error (security drawBits weightBits coinBits order attempts : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order)
    (weight : Core security → ℝ) (weightError : ℝ) (he : 0 ≤ weightError)
    (hweight : ∀ core, |(coreWeight security weightBits order table core : ℝ)-weight core| ≤ weightError)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security))
    (hmass : 1/(4*(Parameters.modulus security : ℝ)) ≤ publicCoreMass (proposal security) weight (publicCharge security)) :
    FiniteDist.TVBound
      (cachedLaw security (CurrentProposalPrecision.tableBits security drawBits) drawBits weightBits coinBits order attempts table)
      (NumericalPublicCompletion.targetCore security weight hpositive)
      ((attempts : ℝ)*(CurrentCoreProposalRates.error security (CurrentProposalPrecision.tableBits security drawBits) drawBits/2+
        (1/(2 : ℝ)^coinBits+weightError/2)) + Real.exp (-(attempts : ℝ)/(8*(Parameters.modulus security : ℝ)))) := by
  apply NumericalPublicCompletion.lift_core_error
  rw [cachedLaw_core]
  exact core_error security drawBits weightBits coinBits order attempts table weight weightError he hweight hmass

end
end CurrentAFT.BinaryPublicRejection
