import CurrentAFT.ActualConstructiveSampler

/-!
# Theorem 9.9: constructive fixed-order Gaussian affine transport

Start here. `theorem_9_9` bundles the paper's existence, legality, accuracy,
quantitative error, and exact public-input guarantees for ONE sampler.
`evaluator_correct_and_polynomial` below supplies the deterministic evaluator
required by the AFT definition, for arbitrary encoded affine data and inputs.

* `accuracyOrder` is fixed BEFORE the security parameter and the random tape.
* `CurrentAFT.Parameters.calibrationOrder accuracyOrder = 4 * accuracyOrder + 267`.
* `data` is finite static program metadata, not a table supplied as advice
  depending on security. `Correct data` is proved by existence, not assumed.
* `run` executes matrix production, calibration, rejection, completion, and
  flat fair-bit decoding. Its integer matrix/offset are given by `affine`;
  the two equality clauses below connect these to the executed binary output.
* `law_eq` identifies the law with independent fair tape / Gaussian draws.
* `uniformFiber` is the uniform distribution on the actual fixed rounding
  matrix's zero fiber (see CurrentAFT/CurrentZeroFiber.lean).

COMPLEXITY MODEL: polynomial counted Boolean/list/counter operations, with
binary operand sizes and array/tape operations charged. A simulation theorem
into a standard probabilistic Turing machine is NOT formalized here.

Paper source label: thm:df-constructive-aft (Theorem 9.9 in the source snapshot).
The Fourier constant in the paper is instantiated as 2 * fourierConstant D.
-/
namespace Theorem99

open AFT CurrentAFT
open CurrentAFT.ActualConstructiveSampler CurrentAFT.BinaryFullResponseData
open CurrentAFT.ActualCalibrationRates
open Filter
open scoped Classical Topology

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentAFT.Parameters.base CurrentAFT.Parameters.bodySize
  CurrentAFT.Parameters.legCount CurrentAFT.Parameters.dimension
  CurrentProposalDimensions.current PublicParameterProgram.modulus
  BinaryPublicBitDecode.current PublicAffinePipeline.run
  CurrentBinaryAffineEmitter.matrix CurrentBinaryAffineEmitter.offset

local instance modulusNeZero (security : ℕ) : NeZero (CurrentAFT.Parameters.modulus security) :=
  ⟨(CurrentAFT.Parameters.modulus_spec security).2.ne_zero⟩

/-- A fixed positive accuracy order has a source-independent sampler with
polynomial tape length and worst-case counted binary work, legal integer
outputs on EVERY tape (including fallback), both paper accuracy guarantees,
and exact public-matrix uniformity/independence. All clauses use the SAME data.
-/
theorem theorem_9_9 (accuracyOrder : ℕ) (_positive : 1 ≤ accuracyOrder) :
    ∃ data : Data (CurrentAFT.Parameters.calibrationOrder accuracyOrder), Correct data ∧
      ∃ bitBudget workBudget : Polynomial ℕ,
        -- One polynomial tape budget, for every security parameter.
        (∀ security, (PublicBitTapes.current security).bits ≤ bitBudget.eval security) ∧
        -- Integer outputs and invertibility hold on every tape, even fallback.
        (∀ security (word : Fin (PublicBitTapes.current security).bits → Fin 2),
          (run security (CurrentAFT.Parameters.calibrationOrder accuracyOrder) data word).work ≤ workBudget.eval security ∧
          (affine security (CurrentAFT.Parameters.calibrationOrder accuracyOrder) data word).matrix =
            CurrentBinaryAffineEmitter.matrix security (run security (CurrentAFT.Parameters.calibrationOrder accuracyOrder) data word) ∧
          (affine security (CurrentAFT.Parameters.calibrationOrder accuracyOrder) data word).offset =
            CurrentBinaryAffineEmitter.offset security (run security (CurrentAFT.Parameters.calibrationOrder accuracyOrder) data word) ∧
          IsUnit ((CurrentBinaryAffineEmitter.matrix security
            (run security (CurrentAFT.Parameters.calibrationOrder accuracyOrder) data word)).map
              (Int.castRingHom (ZMod (CurrentAFT.Parameters.modulus security))))) ∧
        -- The actual experiment: draw the public tape independently of the Gaussian source.
        (∀ security, law security (CurrentAFT.Parameters.calibrationOrder accuracyOrder) data =
          (FiniteDist.uniform (Fin (PublicBitTapes.current security).bits → Fin 2)).mix
            (fun word => PublicAffinePipeline.gaussianChannel security
              (run security (CurrentAFT.Parameters.calibrationOrder accuracyOrder) data word))) ∧
        -- Definition of arbitrary fixed inverse-polynomial Gaussian AFT accuracy.
        (∃ cutoff : ℕ, ∀ security ≥ cutoff,
          (law security (CurrentAFT.Parameters.calibrationOrder accuracyOrder) data).totalVariation
            (CurrentZeroFiber.uniformFiber security) ≤ (security : ℝ)^(-(accuracyOrder : ℝ))) ∧
        -- The explicit Fourier + Gaussian remainder + numerical budget of Theorem 9.9.
        (∀ᶠ security : ℕ in atTop,
          (law security (CurrentAFT.Parameters.calibrationOrder accuracyOrder) data).totalVariation
            (CurrentZeroFiber.uniformFiber security) ≤
          (2 * fourierConstant (CurrentAFT.Parameters.calibrationOrder accuracyOrder)) * (CurrentAFT.Parameters.modulus security : ℝ) *
            (CurrentAFT.Parameters.base security : ℝ)^(-((CurrentAFT.Parameters.calibrationOrder accuracyOrder + 1 : ℕ) : ℝ) / 4) +
          ActualGaussianRemainder.remainder security (CurrentAFT.Parameters.calibrationOrder accuracyOrder)
            (calibrationOrder_at_least_two accuracyOrder) +
          numericalError security (CurrentAFT.Parameters.calibrationOrder accuracyOrder)) ∧
        Negligible (fun security => ActualGaussianRemainder.remainder security
          (CurrentAFT.Parameters.calibrationOrder accuracyOrder) (calibrationOrder_at_least_two accuracyOrder)) ∧
        Negligible (fun security => numericalError security (CurrentAFT.Parameters.calibrationOrder accuracyOrder)) ∧
        -- Exact uniform public matrix, independent of the transformed source.
        (∀ (security columns : ℕ),
          letI : (count : ℕ) → DecidableEq (Fin count) := fun _ => Classical.decEq _
          ∀ (source : FiniteDist (ModularCoordinates (CurrentAFT.Parameters.dimension security) (CurrentAFT.Parameters.modulus security))),
          ((FiniteDist.uniform (Fin (PublicBitTapes.current security).bits → Fin 2)).prod source).mix (fun draw =>
            (FiniteDist.uniform (Fin columns → ModularCoordinates (CurrentAFT.Parameters.dimension security) (CurrentAFT.Parameters.modulus security))).map
              (fun matrix => (((affine security (CurrentAFT.Parameters.calibrationOrder accuracyOrder) data draw.1).reduced).columnsEquiv (Fin columns) matrix,
                ((affine security (CurrentAFT.Parameters.calibrationOrder accuracyOrder) data draw.1).reduced).eval draw.2))) =
          (FiniteDist.uniform (Fin columns → ModularCoordinates (CurrentAFT.Parameters.dimension security) (CurrentAFT.Parameters.modulus security))).prod
            (transportedLaw (FiniteDist.uniform (Fin (PublicBitTapes.current security).bits → Fin 2))
              (fun word => (affine security (CurrentAFT.Parameters.calibrationOrder accuracyOrder) data word).reduced) source)) := by
  obtain ⟨data, hdata, bitBudget, workBudget, hbits, hwork, haccuracy⟩ :=
    constructive_gaussian_aft accuracyOrder
  refine ⟨data, hdata, bitBudget, workBudget, hbits, ?_, ?_, haccuracy,
    quantitative_eventually accuracyOrder data hdata,
    ActualGaussianRemainder.remainder_negligible _ (calibrationOrder_at_least_two accuracyOrder),
    numericalError_negligible _, ?_⟩
  · intro security word
    exact ⟨(hwork security word).1, affine_matrix security _ data word,
      affine_offset security _ data word, (hwork security word).2⟩
  · intro security
    exact law_eq security _ data
  · intro security columns source
    exact CurrentAFT.ActualConstructiveSampler.public_matrix_error_independent security _ columns data source

/-- The deterministic AFT evaluator is correct on arbitrary encoded integer
matrix/offset/input arrays and polynomial in security plus their actual bit
lengths. There is no assumption that these data were generated by the sampler.
-/
theorem evaluator_correct_and_polynomial (security : ℕ)
    (data : CurrentBinaryAffineEmitter.Data security)
    (input : Vector BinaryArithmetic.IntegerBits (CurrentBinaryAffinePrimitives.Size security)) :
    ActualAffineEvaluator.decodeOutput security (ActualAffineEvaluator.current security data input).value =
      (fun index => (((CurrentBinaryAffineEmitter.matrix security data).mulVec
        (ActualAffineEvaluator.decodeInput security input) index +
          CurrentBinaryAffineEmitter.offset security data index : ℤ) : ZMod (CurrentAFT.Parameters.modulus security))) ∧
    (ActualAffineEvaluator.current security data input).work ≤
      ActualAffineEvaluator.workPolynomial.eval (security + ActualAffineEvaluator.bitSize data input) :=
  ⟨ActualAffineEvaluator.current_value security data input,
    ActualAffineEvaluator.polynomial_work security data input⟩

end Theorem99
