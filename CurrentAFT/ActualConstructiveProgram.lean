import CurrentAFT.BinaryFullResponseMatrixEntryProgram
import CurrentAFT.PublicAffinePipelineResources
import CurrentAFT.PublicAffinePipelineQuantitative
import CurrentAFT.PublicAffinePipelineUniform
import CurrentAFT.BinaryPublicBitDecode
import CurrentAFT.ActualAffineEvaluator

/-! The current construction's complete finite-bit sampler. Static arithmetic
programs are fixed once for the requested order. All security-dependent tables,
calibration iterates, rejection trials, public completions, and integer affine
outputs are executed by the concrete programs in this import chain. -/
namespace CurrentAFT.ActualConstructiveSampler
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
open ActualCalibrationRates BinaryFullResponseData
open Filter
open scoped Classical Topology
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false

def producer (security order : ℕ) (data : Data order) : PublicAffinePipeline.Producer security order := fun _ =>
  BinaryRectangleMaterialization.run security order security (BinaryFullResponseMatrixEntry.current security security order data)

def run (security order : ℕ) (data : Data order) (word : Fin (PublicBitTapes.current security).bits → Fin 2) :
    CurrentBinaryAffineEmitter.Data security :=
  let decoded := BinaryPublicBitDecode.current security word
  PublicAffinePipeline.addWork security decoded.work
    (PublicAffinePipeline.run security order (producer security order data) decoded.value)

noncomputable section
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentProposalDimensions.current PublicParameterProgram.modulus
  BinaryPublicBitDecode.current PublicAffinePipeline.run
  CurrentBinaryAffineEmitter.matrix CurrentBinaryAffineEmitter.offset

def law (security order : ℕ) (data : Data order) : FiniteDist (CurrentZeroFiber.Word security) :=
  PublicAffinePipeline.fairGaussian security order (producer security order data)

theorem law_eq (security order : ℕ) (data : Data order) :
    law security order data =
      (FiniteDist.uniform (Fin (PublicBitTapes.current security).bits → Fin 2)).mix
        (fun word => PublicAffinePipeline.gaussianChannel security (run security order data word)) := by
  simp only [law,PublicAffinePipeline.fairGaussian,run,PublicAffinePipeline.addWork_channel,
    BinaryPublicBitDecode.current_value,PublicAffinePipeline.fairBitRun]

theorem run_eq (security order : ℕ) (data : Data order) (word : Fin (PublicBitTapes.current security).bits → Fin 2) :
    run security order data word=
      PublicAffinePipeline.addWork security (BinaryPublicBitDecode.current security word).work
        (PublicAffinePipeline.fairBitRun security order (producer security order data) word) := by
  exact congrArg (fun decoded => PublicAffinePipeline.addWork security (BinaryPublicBitDecode.current security word).work
    (PublicAffinePipeline.run security order (producer security order data) decoded))
      (BinaryPublicBitDecode.current_value security word)

theorem run_matrix (security order : ℕ) (data : Data order) (word : Fin (PublicBitTapes.current security).bits → Fin 2) :
    CurrentBinaryAffineEmitter.matrix security (run security order data word)=
      CurrentBinaryAffineEmitter.matrix security
        (PublicAffinePipeline.fairBitRun security order (producer security order data) word) := by
  exact (congrArg (CurrentBinaryAffineEmitter.matrix security) (run_eq security order data word)).trans
    (PublicAffinePipeline.addWork_matrix security _ _)

theorem run_offset (security order : ℕ) (data : Data order) (word : Fin (PublicBitTapes.current security).bits → Fin 2) :
    CurrentBinaryAffineEmitter.offset security (run security order data word)=
      CurrentBinaryAffineEmitter.offset security
        (PublicAffinePipeline.fairBitRun security order (producer security order data) word) := by
  exact (congrArg (CurrentBinaryAffineEmitter.offset security) (run_eq security order data word)).trans
    (PublicAffinePipeline.addWork_offset security _ _)

def producerHeight (order : ℕ) (data : Data order) : Polynomial ℕ :=
  BinaryCalibrationIteration.heightPolynomial (BinaryRectangleResources.sizePolynomial order)
    (BinaryFullResponseMatrixEntry.heightPolynomial order data Polynomial.X) Polynomial.X

def producerWork (order : ℕ) (data : Data order) : Polynomial ℕ :=
  BinaryRectangleResources.runPolynomial order
    (BinaryFullResponseMatrixEntry.heightPolynomial order data Polynomial.X)
    (BinaryFullResponseMatrixEntry.workPolynomial order data Polynomial.X) Polynomial.X

def workPolynomial (order : ℕ) (data : Data order) : Polynomial ℕ :=
  BinaryPublicBitDecode.workPolynomial+
    PublicAffinePipeline.workPolynomial order (producerWork order data) (producerHeight order data)

theorem producer_bounds (security order : ℕ) (data : Data order) (layout : CurrentLayoutDraw.Cache security) :
    (producer security order data layout).work≤(producerWork order data).eval security ∧
      ∀ row column, HeightBound (((producer security order data layout).value.get row).get column).decode
        ((producerHeight order data).eval security) := by
  have h := BinaryRectangleResources.run_polynomial_bounds security order security
    (BinaryFullResponseMatrixEntry.heightPolynomial order data Polynomial.X)
    (BinaryFullResponseMatrixEntry.workPolynomial order data Polynomial.X) Polynomial.X
    (BinaryFullResponseMatrixEntry.current security security order data)
    (fun output input => by simpa only [Polynomial.eval_X] using (BinaryFullResponseMatrixEntry.current_bounds security order data Polynomial.X output input).1)
    (fun output input => by simpa only [Polynomial.eval_X] using (BinaryFullResponseMatrixEntry.current_bounds security order data Polynomial.X output input).2)
    (by simp only [Polynomial.eval_X,le_refl])
  exact h

theorem run_work (security order : ℕ) (data : Data order) (word : Fin (PublicBitTapes.current security).bits → Fin 2) :
    (run security order data word).work≤(workPolynomial order data).eval security := by
  have h := PublicAffinePipeline.polynomial_work security order (producer security order data) (producerWork order data) (producerHeight order data)
    (fun layout => (producer_bounds security order data layout).1)
    (fun layout => (producer_bounds security order data layout).2) (BinaryPublicBitDecode.current security word).value
  simpa only [run,PublicAffinePipeline.addWork,workPolynomial,Polynomial.eval_add] using
    Nat.add_le_add (BinaryPublicBitDecode.current_work security word) h

theorem run_invertible (security order : ℕ) (data : Data order) (word : Fin (PublicBitTapes.current security).bits → Fin 2) :
    IsUnit ((CurrentBinaryAffineEmitter.matrix security (run security order data word)).map
      (Int.castRingHom (ZMod (Parameters.modulus security)))) := by
  rw [run_matrix]
  exact PublicAffinePipeline.run_invertible security order (producer security order data) ((PublicBitTapes.current security).equiv word)

local instance uniformFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

local instance modulusNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩

def affine (security order : ℕ) (data : Data order) (word : Fin (PublicBitTapes.current security).bits → Fin 2) :
    CurrentAffineData.Data security :=
  PublicAffinePipeline.fairData security order (producer security order data) word

theorem affine_matrix (security order : ℕ) (data : Data order) (word : Fin (PublicBitTapes.current security).bits → Fin 2) :
    (affine security order data word).matrix=CurrentBinaryAffineEmitter.matrix security (run security order data word) := by
  rw [run_matrix]
  rfl

theorem affine_offset (security order : ℕ) (data : Data order) (word : Fin (PublicBitTapes.current security).bits → Fin 2) :
    (affine security order data word).offset=CurrentBinaryAffineEmitter.offset security (run security order data word) := by
  rw [run_offset]
  rfl

/-- Exact uniformity and independence of the transformed public matrix, for
an independently drawn input table and the complete literal sampler tape. -/
theorem public_matrix_error_independent (security order columns : ℕ) (data : Data order)
    (source : FiniteDist (ModularCoordinates (Parameters.dimension security) (Parameters.modulus security))) :
    ((FiniteDist.uniform (Fin (PublicBitTapes.current security).bits → Fin 2)).prod source).mix (fun draw =>
      (FiniteDist.uniform (Fin columns → ModularCoordinates (Parameters.dimension security) (Parameters.modulus security))).map
        (fun matrix => (((affine security order data draw.1).reduced).columnsEquiv (Fin columns) matrix,
          ((affine security order data draw.1).reduced).eval draw.2))) =
      (FiniteDist.uniform (Fin columns → ModularCoordinates (Parameters.dimension security) (Parameters.modulus security))).prod
        (transportedLaw (FiniteDist.uniform (Fin (PublicBitTapes.current security).bits → Fin 2))
          (fun word => (affine security order data word).reduced) source) :=
  PublicAffinePipeline.public_matrix_error_independent security order columns (producer security order data) source

theorem ideal_response_preserved (security order columns : ℕ) (data : Data order) :
    (FiniteDist.uniform (Fin (PublicBitTapes.current security).bits → Fin 2)).mix (fun word =>
      ((FiniteDist.uniform (Fin columns → ModularCoordinates (Parameters.dimension security) (Parameters.modulus security))).prod
        (FiniteDist.uniform (ModularCoordinates (Parameters.dimension security) (Parameters.modulus security)))).map
          ((((affine security order data word).reduced).columnsEquiv (Fin columns)).prodCongr
            ((affine security order data word).reduced).equiv)) =
      (FiniteDist.uniform (Fin columns → ModularCoordinates (Parameters.dimension security) (Parameters.modulus security))).prod
        (FiniteDist.uniform (ModularCoordinates (Parameters.dimension security) (Parameters.modulus security))) :=
  PublicAffinePipeline.ideal_response_preserved security order columns (producer security order data)

end
end CurrentAFT.ActualConstructiveSampler
