import CurrentAFT.CurrentMaterializedCompletion

/-! Exact probability semantics and Gaussian error of the executed public
core-and-completion program, uniformly for every fixed public placement. -/
namespace CurrentAFT.CurrentMaterializedCompletion
open AFT ActualPublicCharge CurrentCoreProposal CurrentPublicCompletion
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CappedPublicRejection.current CurrentMaterializedCompletion.current

theorem completion_tape_uniform (security bits edgeBits : ℕ) :
    CurrentPublicCompletion.tapeLaw security bits edgeBits = FiniteDist.uniform (CurrentPublicCompletion.Tapes security bits edgeBits) := by
  simp only [CurrentPublicCompletion.tapeLaw, CurrentChartsDraw.tapeLaw, CurrentFlagJointDraw.tapeLaw,
    ← FiniteDist.uniform_product, FiniteDist.independent_uniform]

theorem product_program {First Second Output : Type*} [Fintype First] [Fintype Second] [Fintype Output]
    (first : FiniteDist First) (second : FiniteDist Second) (program : First → Second → Output) :
    (first.prod second).map (fun pair => program pair.1 pair.2) =
      first.mix (fun input => second.map (program input)) := by
  ext output
  simp only [FiniteDist.map_weight, FiniteDist.prod_weight, FiniteDist.mix_weight, Fintype.sum_prod_type,
    Finset.mul_sum, mul_ite, mul_zero]

def publicLaw (security order : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order) :
    FiniteDist (Option (CurrentPublicAffineSample.Sample security)) :=
  (FiniteDist.uniform (CurrentMaterializedCompletion.Tapes security)).map
    (fun word => Option.map Result.sample (current security order table word).value)

theorem publicLaw_eq (security order : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order) :
    publicLaw security order table =
      ((CappedPublicRejection.law security order table).map (Option.map MaterializedCore.cached)).mix
        (CurrentPublicCompletion.kernel security security security security) := by
  rw [publicLaw, FiniteDist.uniform_product]
  unfold CurrentMaterializedCompletion.current
  change ((FiniteDist.uniform (CappedPublicRejection.Tapes security)).prod
    (FiniteDist.uniform (CurrentPublicCompletion.Tapes security security security))).map
      (fun pair => Option.map Result.sample (complete security
        (CappedPublicRejection.current security order table pair.1).value security security security pair.2).value) = _
  simp only [complete_value]
  rw [product_program (FiniteDist.uniform (CappedPublicRejection.Tapes security))
    (FiniteDist.uniform (CurrentPublicCompletion.Tapes security security security))
    (fun first second => (CurrentPublicCompletion.complete security
      (Option.map MaterializedCore.cached (CappedPublicRejection.current security order table first).value)
      security security security second).value)]
  simp only [CappedPublicRejection.law, FiniteDist.mix_map, CurrentPublicCompletion.kernel, completion_tape_uniform]

def totalError (security : ℕ) (weightError : ℝ) : ℝ :=
  CappedPublicRejection.error security weightError+CurrentPublicCompletion.errorBound security security security security/2

theorem totalError_nonneg (security : ℕ) (weightError : ℝ) (he : 0 ≤ weightError) : 0 ≤ totalError security weightError := by
  have hc := CappedPublicRejection.error_nonneg security weightError he
  unfold totalError CurrentPublicCompletion.errorBound
  positivity

theorem totalError_negligible {weightError : ℕ → ℝ} (he : Negligible weightError) :
    Negligible (fun security => totalError security (weightError security)) := by
  have hc := CappedPublicRejection.error_negligible he
  have hp := NumericalWeightRates.negligible_const_mul NumericalProposalRates.completion_negligible (1/2)
  convert hc.add hp using 1
  funext security
  unfold totalError
  ring

theorem public_error (security order : ℕ) (hsecurity : 1 ≤ security)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order)
    (weight : Core security → ℝ) (weightError : ℝ) (he : 0 ≤ weightError)
    (hweight : ∀ core, |(BinaryPublicRejection.coreWeight security security order table core : ℝ)-weight core| ≤ weightError)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security))
    (hmass : 1/(4*(Parameters.modulus security : ℝ)) ≤ publicCoreMass (proposal security) weight (publicCharge security)) :
    FiniteDist.TVBound (publicLaw security order table)
      ((CurrentPublicAffineSample.law security weight hpositive).map some) (totalError security weightError) := by
  have hc := CappedPublicRejection.core_error security order table weight weightError he hweight hpositive hmass
  have hforget : ((CappedPublicRejection.law security order table).map (Option.map MaterializedCore.cached)).map
      (Option.map (CurrentPublicCompletion.coreEquiv security)) =
      (CappedPublicRejection.law security order table).map (BinaryPublicRejection.decodeResult security) := by
    rw [FiniteDist.map_map]
    congr 1
    funext input
    cases input <;> rfl
  have hl := NumericalPublicCompletion.lift_core_error security weight hpositive
    ((CappedPublicRejection.law security order table).map (Option.map MaterializedCore.cached))
    (CappedPublicRejection.error security weightError) (by rw [hforget]; exact hc)
  rw [publicLaw_eq]
  exact NumericalPublicCompletion.implementation_error security security security security hsecurity weight hpositive
    _ _ hl

theorem gaussian_error (security order : ℕ) (hsecurity : 1 ≤ security)
    (layout : ConditionalHistogramMean.RoleIndex security ≃ ActualCycleMeanMGF.BodyIndex security)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order)
    (weight : Core security → ℝ) (weightError analytic : ℝ) (he : 0 ≤ weightError)
    (hweight : ∀ core, |(BinaryPublicRejection.coreWeight security security order table core : ℝ)-weight core| ≤ weightError)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security))
    (hmass : 1/(4*(Parameters.modulus security : ℝ)) ≤ publicCoreMass (proposal security) weight (publicCharge security))
    (hanalytic : (CurrentAffineTransport.gaussianLaw security layout weight hpositive).totalVariation
      (CurrentZeroFiber.uniformFiber security) ≤ analytic) :
    (NumericalAffineTransport.gaussianOutput security layout (publicLaw security order table)).totalVariation
      (CurrentZeroFiber.uniformFiber security) ≤ analytic+totalError security weightError :=
  NumericalAffineTransport.transport_error security layout weight hpositive (publicLaw security order table)
    (totalError security weightError) analytic (public_error security order hsecurity table weight weightError he hweight hpositive hmass) hanalytic

end
end CurrentAFT.CurrentMaterializedCompletion
