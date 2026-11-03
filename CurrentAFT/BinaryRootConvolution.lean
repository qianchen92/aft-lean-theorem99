import CurrentAFT.BinaryRootConvolutionKernel
import CurrentAFT.RationalBackgroundProfiles

/-! # The current Gaussian root convolution executed on an explicit profile array -/
namespace CurrentAFT.BinaryRootConvolution
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits FiniteConvolutionProgram
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryDiffuseCurrent.metadata BinaryActivationProgram.cutoff
  BinaryRootConvolutionKernel.current

def evaluate (security count edgeCutoff scalarCutoff bits : ℕ) (table : Vector RationalBits count)
    (output : List Bool) : RationalResult :=
  let modulus := canonicalCounter count
  let result := BinarySeedAverage.evaluate security edgeCutoff scalarCutoff bits
    (BinaryRootConvolutionKernel.current edgeCutoff scalarCutoff modulus.digits output table)
  ⟨result.data, modulus.work+result.work+2⟩

theorem evaluate_value (security count edgeCutoff scalarCutoff bits : ℕ) (table : Vector RationalBits count)
    (output : List Bool) (hq : 0<count) :
    (evaluate security count edgeCutoff scalarCutoff bits table output).data.decode =
      ∑ seed : (Window edgeCutoff × Window edgeCutoff) × Window scalarCutoff,
        RationalProposalProgram.gaussianWeight security edgeCutoff bits seed.1.1*
        RationalProposalProgram.gaussianWeight security edgeCutoff bits seed.1.2*
        RationalProposalProgram.gaussianWeight security scalarCutoff bits seed.2*
        BinaryRootConvolutionKernel.profile table
          (((value output:ℤ)-(seed.1.1.val-seed.1.2.val))%(count:ℤ)).toNat := by
  unfold evaluate
  rw [BinarySeedAverage.evaluate_window_value]
  simp only [RationalProposalProgram.gaussianWeight_eq]
  apply Finset.sum_congr rfl
  intro seed _
  rw [BinaryRootConvolutionKernel.current_value _ _ _ _ _ _ _ _ hq (canonicalCounter_value count)]
  have hl : (((windowIndexEquiv edgeCutoff).symm seed.1.1).val:ℤ)-edgeCutoff=seed.1.1.val :=
    congrArg Subtype.val ((windowIndexEquiv edgeCutoff).apply_symm_apply seed.1.1)
  have hr : (((windowIndexEquiv edgeCutoff).symm seed.1.2).val:ℤ)-edgeCutoff=seed.1.2.val :=
    congrArg Subtype.val ((windowIndexEquiv edgeCutoff).apply_symm_apply seed.1.2)
  have hroot : (((windowIndexEquiv edgeCutoff).symm seed.1.1).val:ℤ)-
      ((windowIndexEquiv edgeCutoff).symm seed.1.2).val=seed.1.1.val-seed.1.2.val := by omega
  rw [hroot]

def current (security bits : ℕ) (table : Vector RationalBits (BinaryFirstInverseProgram.colors security))
    (output : List Bool) : RationalResult :=
  let parameters := BinaryDiffuseCurrent.metadata security
  let window := BinaryActivationProgram.cutoff security
  let modulus := PublicParameterProgram.modulus security
  let result := evaluate security modulus.count parameters.cutoff window.count bits table output
  ⟨result.data, parameters.work+window.work+modulus.work+result.work+4⟩

theorem current_value (security bits : ℕ) (table : Vector RationalBits (BinaryFirstInverseProgram.colors security))
    (output : List Bool) :
    (current security bits table output).data.decode = RationalBackgroundProfiles.convolution security bits
      (BinaryRootConvolutionKernel.profile table) (value output) := by
  have hq : 0<(PublicParameterProgram.modulus security).count := by
    rw [PublicParameterProgram.modulus_value]
    exact (Parameters.modulus_spec security).2.pos
  rcases BinaryDiffuseCurrent.metadata_value security with ⟨_, _, hc⟩
  unfold current
  rw [evaluate_value _ _ _ _ _ _ _ hq, hc, BinaryActivationProgram.cutoff_value]
  have he : ((security+2)^2-1)/2=DiffuseProfiles.edgeCutoff security := by
    simp only [DiffuseProfiles.edgeCutoff, Parameters.sourceCutoff, Parameters.base]
  have hs : (security+2)^2-1=Parameters.sourceCutoff security-1 := by
    simp only [Parameters.sourceCutoff, Parameters.base]
  rw [he, hs]
  unfold RationalBackgroundProfiles.convolution RationalProposalProgram.seedEvaluate RationalProposalProgram.seedWeight
    RationalBackgroundProfiles.inverseShift
  rfl

end CurrentAFT.BinaryRootConvolution
