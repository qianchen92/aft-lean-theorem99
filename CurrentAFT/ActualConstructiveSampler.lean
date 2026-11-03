import CurrentAFT.ActualConstructiveProgram
import CurrentAFT.BinaryFullResponseMatrixEntry
import CurrentAFT.RationalFullWeightAccuracy

/-! The complete current fixed-order Gaussian affine transport theorem.
Every numerical and runtime obligation is supplied by the actual binary producer. -/
namespace CurrentAFT.ActualConstructiveSampler
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
open ActualCalibrationRates BinaryFullResponseData
open Filter
open scoped Classical Topology
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
noncomputable section
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentProposalDimensions.current PublicParameterProgram.modulus

theorem weight_error_eventually (order : ℕ) (horder : 2≤order) (data : Data order) (hdata : Correct data) :
    ∀ᶠ security : ℕ in atTop,
      ∀ hsecurity : ActualCompleteStability.threshold order horder≤security,
      ∀ (layout : CurrentLayoutDraw.Cache security) (core : ActualPublicCharge.Core security),
        |(BinaryPublicRejection.coreWeight security security order (producer security order data layout).value core:ℝ)-
          ActualCalibratedPublic.weight security order horder hsecurity layout.layout core|≤
            RationalFullResponseProgram.weightError security order := by
  filter_upwards [RationalFullResponseProgram.materialized_weight_error_eventually order horder] with security hs hsecurity layout core
  exact hs hsecurity layout.layout (BinaryFullResponseMatrixEntry.current security security order data)
    (BinaryFullResponseMatrixEntry.current_value security security order data hdata) core

theorem accuracy_eventually (accuracyOrder : ℕ) (data : Data (Parameters.calibrationOrder accuracyOrder)) (hdata : Correct data) :
    ∃ cutoff : ℕ, ∀ security≥cutoff,
      (law security (Parameters.calibrationOrder accuracyOrder) data).totalVariation (CurrentZeroFiber.uniformFiber security)≤
        (security:ℝ)^(-(accuracyOrder:ℝ)) :=
  PublicAffinePipeline.accuracy_eventually accuracyOrder (fun security => producer security (Parameters.calibrationOrder accuracyOrder) data)
    (fun security => RationalFullResponseProgram.weightError security (Parameters.calibrationOrder accuracyOrder))
    (fun security => RationalFullResponseProgram.weightError_nonneg security _)
    (RationalFullResponseProgram.weightError_negligible _)
    (weight_error_eventually _ (calibrationOrder_at_least_two accuracyOrder) data hdata)

def numericalError (security order : ℕ) : ℝ :=
  CurrentMaterializedCompletion.totalError security (RationalFullResponseProgram.weightError security order)

theorem numericalError_negligible (order : ℕ) : Negligible (fun security => numericalError security order) :=
  CurrentMaterializedCompletion.totalError_negligible (RationalFullResponseProgram.weightError_negligible order)

theorem quantitative_eventually (accuracyOrder : ℕ) (data : Data (Parameters.calibrationOrder accuracyOrder)) (hdata : Correct data) :
    ∀ᶠ security : ℕ in atTop,
      (law security (Parameters.calibrationOrder accuracyOrder) data).totalVariation (CurrentZeroFiber.uniformFiber security) ≤
      (2*fourierConstant (Parameters.calibrationOrder accuracyOrder))*(Parameters.modulus security:ℝ)*
        (Parameters.base security:ℝ)^(-((Parameters.calibrationOrder accuracyOrder+1:ℕ):ℝ)/4)+
      ActualGaussianRemainder.remainder security (Parameters.calibrationOrder accuracyOrder)
        (calibrationOrder_at_least_two accuracyOrder)+numericalError security (Parameters.calibrationOrder accuracyOrder) :=
  PublicAffinePipeline.quantitative_eventually accuracyOrder (fun security => producer security (Parameters.calibrationOrder accuracyOrder) data)
    (fun security => RationalFullResponseProgram.weightError security (Parameters.calibrationOrder accuracyOrder))
    (fun security => RationalFullResponseProgram.weightError_nonneg security _)
    (weight_error_eventually _ (calibrationOrder_at_least_two accuracyOrder) data hdata)

theorem numerical_budget_eventually (accuracyOrder : ℕ) :
    ∀ᶠ security : ℕ in atTop, numericalError security (Parameters.calibrationOrder accuracyOrder) ≤
      (1/4:ℝ)/(Parameters.base security:ℝ)^(accuracyOrder+2) := by
  filter_upwards [PublicAffinePipeline.negligible_quarter_base
    (numericalError_negligible (Parameters.calibrationOrder accuracyOrder)) (accuracyOrder+2)] with security hs
  exact (le_abs_self _).trans hs

/-- Complete fixed-order existence statement for the literal current binary
sampler, with no response, stability, approximation, or runtime premise. -/
theorem constructive_gaussian_aft (accuracyOrder : ℕ) :
    ∃ data : Data (Parameters.calibrationOrder accuracyOrder), Correct data ∧
      ∃ bitBudget workBudget : Polynomial ℕ,
        (∀ security, (PublicBitTapes.current security).bits≤bitBudget.eval security) ∧
        (∀ security (word : Fin (PublicBitTapes.current security).bits → Fin 2),
          (run security (Parameters.calibrationOrder accuracyOrder) data word).work≤workBudget.eval security ∧
          IsUnit ((CurrentBinaryAffineEmitter.matrix security (run security (Parameters.calibrationOrder accuracyOrder) data word)).map
            (Int.castRingHom (ZMod (Parameters.modulus security))))) ∧
        (∃ cutoff : ℕ, ∀ security≥cutoff,
          (law security (Parameters.calibrationOrder accuracyOrder) data).totalVariation (CurrentZeroFiber.uniformFiber security)≤
            (security:ℝ)^(-(accuracyOrder:ℝ))) := by
  obtain ⟨data,hdata⟩ := BinaryFullResponseData.exists_data (Parameters.calibrationOrder accuracyOrder)
  obtain ⟨bitBudget,hbits⟩ := PublicBitResources.polynomial_bits
  refine ⟨data,hdata,bitBudget,workPolynomial _ data,hbits,?_,accuracy_eventually accuracyOrder data hdata⟩
  intro security word
  exact ⟨run_work security _ data word,run_invertible security _ data word⟩



end
end CurrentAFT.ActualConstructiveSampler
