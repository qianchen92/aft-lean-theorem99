import CurrentAFT.BinaryProfileKernel
import CurrentAFT.BinarySeedAverage

/-! # The full current sign-dependent diffuse profile produced on binary data -/
namespace CurrentAFT.BinaryProfileProgram
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits FiniteConvolutionProgram
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryDiffuseCurrent.metadata BinaryActivationProgram.cutoff

def evaluate (security colors width edgeCutoff scalarCutoff bits : ℕ) (positive : Bool) (output : List Bool) : RationalResult :=
  BinarySeedAverage.evaluate security edgeCutoff scalarCutoff bits
    (BinaryProfileKernel.current colors width edgeCutoff scalarCutoff positive output)

theorem evaluate_value (security colors width edgeCutoff scalarCutoff bits : ℕ) (positive : Bool) (output : List Bool) :
    (evaluate security colors width edgeCutoff scalarCutoff bits positive output).data.decode =
      ∑ seed : (Window edgeCutoff × Window edgeCutoff) × Window scalarCutoff,
        RationalProposalProgram.gaussianWeight security edgeCutoff bits seed.1.1 *
        RationalProposalProgram.gaussianWeight security edgeCutoff bits seed.1.2 *
        RationalProposalProgram.gaussianWeight security scalarCutoff bits seed.2 *
        RationalFirstResponseProgram.profileKernel colors width positive (seed.1.1.val-seed.1.2.val) seed.2.val (value output) := by
  rw [evaluate, BinarySeedAverage.evaluate_window_value]
  simp only [RationalProposalProgram.gaussianWeight_eq]
  apply Finset.sum_congr rfl
  intro seed _
  rw [BinaryProfileKernel.current_value]
  have hl : (((windowIndexEquiv edgeCutoff).symm seed.1.1).val:ℤ)-edgeCutoff = seed.1.1.val :=
    congrArg Subtype.val ((windowIndexEquiv edgeCutoff).apply_symm_apply seed.1.1)
  have hr : (((windowIndexEquiv edgeCutoff).symm seed.1.2).val:ℤ)-edgeCutoff = seed.1.2.val :=
    congrArg Subtype.val ((windowIndexEquiv edgeCutoff).apply_symm_apply seed.1.2)
  have hs : (((windowIndexEquiv scalarCutoff).symm seed.2).val:ℤ)-scalarCutoff = seed.2.val :=
    congrArg Subtype.val ((windowIndexEquiv scalarCutoff).apply_symm_apply seed.2)
  have hblur : (((windowIndexEquiv edgeCutoff).symm seed.1.1).val:ℤ)-
      ((windowIndexEquiv edgeCutoff).symm seed.1.2).val = seed.1.1.val-seed.1.2.val := by omega
  rw [hblur, hs]

theorem evaluate_bounds (security colors width edgeCutoff scalarCutoff bits : ℕ) (positive : Bool) (output : List Bool)
    (bound : ℕ) (hq : colors ≤ bound) (hw : width ≤ bound) (he : edgeCutoff ≤ bound)
    (hs : scalarCutoff ≤ bound) (ho : output.length ≤ bound)
    (hec : edgeCutoff ≤ (security+2)^2) (hsc : scalarCutoff ≤ (security+2)^2) :
    HeightBound (evaluate security colors width edgeCutoff scalarCutoff bits positive output).data.decode
      (BinarySeedAverage.outputHeight security edgeCutoff scalarCutoff bits (BinaryProfileKernel.currentHeight bound)) ∧
      (evaluate security colors width edgeCutoff scalarCutoff bits positive output).work ≤
        BinarySeedAverage.workBound security edgeCutoff scalarCutoff bits (BinaryProfileKernel.currentHeight bound)
          (BinaryProfileKernel.currentWork bound) := by
  have hk (left right : Fin (2*edgeCutoff+1)) (scalar : Fin (2*scalarCutoff+1)) :=
    BinaryProfileKernel.current_bounds colors width edgeCutoff scalarCutoff positive output left right scalar bound hq hw he hs ho
  exact BinarySeedAverage.evaluate_bounds security edgeCutoff scalarCutoff bits _ _ _ hec hsc
    (fun left right scalar => (hk left right scalar).1) (fun left right scalar => (hk left right scalar).2)

def current (security bits : ℕ) (positive : Bool) (output : List Bool) : RationalResult :=
  let parameters := BinaryDiffuseCurrent.metadata security
  let window := BinaryActivationProgram.cutoff security
  let result := evaluate security parameters.colors parameters.width parameters.cutoff window.count bits positive output
  ⟨result.data, parameters.work + window.work + result.work + 3⟩

theorem current_value (security bits : ℕ) (positive : Bool) (output : List Bool) :
    (current security bits positive output).data.decode =
      RationalFirstResponseProgram.profile security bits positive (value output) := by
  rcases BinaryDiffuseCurrent.metadata_value security with ⟨hq, hw, hc⟩
  unfold current
  rw [evaluate_value, hq, hw, hc, BinaryActivationProgram.cutoff_value]
  unfold RationalFirstResponseProgram.profile RationalProposalProgram.seedEvaluate RationalProposalProgram.seedWeight
  rw [PublicParameterProgram.modulus_value]
  have he : ((security+2)^2-1)/2 = DiffuseProfiles.edgeCutoff security := by
    simp only [DiffuseProfiles.edgeCutoff, Parameters.sourceCutoff, Parameters.base]
  have hs : (security+2)^2-1 = Parameters.sourceCutoff security-1 := by
    simp only [Parameters.sourceCutoff, Parameters.base]
  rw [he, hs]

noncomputable section
open scoped Classical

theorem current_error (security bits : ℕ) (positive : Bool) (output : FirstHistogram.Palette security)
    (outputCode : List Bool) (ho : value outputCode = output.val) :
    |((current security bits positive outputCode).data.decode:ℝ)-DiffuseProfiles.actualProfile security positive output| ≤ 3/(2:ℝ)^bits := by
  rw [current_value, ho]
  exact RationalFirstResponseProgram.profile_error security bits positive output

noncomputable def currentWorkPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDiffuseCurrent.metadataWorkPolynomial + BinaryActivationProgram.cutoffWorkPolynomial +
    BinarySeedAverage.workPolynomial ((Polynomial.X+2)^2) ((Polynomial.X+2)^2) precision
      (BinaryProfileKernel.heightPolynomial (BinaryDiffuseCurrent.parameterPolynomial inputBits))
      (BinaryProfileKernel.workPolynomial (BinaryDiffuseCurrent.parameterPolynomial inputBits)) + 3

noncomputable def currentHeightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  let count := 2*(Polynomial.X+2)^2+1
  let gaussian := 500000000*((Polynomial.X+2)^2+precision+2)^6
  count*(gaussian+count*(count*(2*gaussian+BinaryProfileKernel.heightPolynomial
    (BinaryDiffuseCurrent.parameterPolynomial inputBits)+1)+1)+1)

theorem current_height (security : ℕ) (positive : Bool) (output : List Bool)
    (precision inputBits : Polynomial ℕ) (ho : output.length ≤ inputBits.eval security) :
    HeightBound (current security (precision.eval security) positive output).data.decode
      ((currentHeightPolynomial precision inputBits).eval security) := by
  let bound := BinaryDiffuseCurrent.parameterBound security (inputBits.eval security)
  rcases BinaryDiffuseCurrent.metadata_value security with ⟨hq, hw, hc⟩
  have hqBound : Parameters.modulus security ≤ 131072*(security+2)^64 := by
    simpa only [Parameters.base] using (Parameters.modulus_bounds security).2
  have hcolors : (BinaryDiffuseCurrent.metadata security).colors ≤ bound := by
    rw [hq]; unfold bound BinaryDiffuseCurrent.parameterBound; omega
  have hwidth : (BinaryDiffuseCurrent.metadata security).width ≤ bound := by
    rw [hw]; unfold bound BinaryDiffuseCurrent.parameterBound; omega
  have hec : (BinaryDiffuseCurrent.metadata security).cutoff ≤ (security+2)^2 := by rw [hc]; omega
  have hsc : (BinaryActivationProgram.cutoff security).count ≤ (security+2)^2 := by
    rw [BinaryActivationProgram.cutoff_value]; omega
  have he : (BinaryDiffuseCurrent.metadata security).cutoff ≤ bound := by unfold bound BinaryDiffuseCurrent.parameterBound; omega
  have hs : (BinaryActivationProgram.cutoff security).count ≤ bound := by unfold bound BinaryDiffuseCurrent.parameterBound; omega
  have hout : output.length ≤ bound := by unfold bound BinaryDiffuseCurrent.parameterBound; omega
  have hh := (evaluate_bounds security (BinaryDiffuseCurrent.metadata security).colors
    (BinaryDiffuseCurrent.metadata security).width (BinaryDiffuseCurrent.metadata security).cutoff
    (BinaryActivationProgram.cutoff security).count (precision.eval security) positive output bound
      hcolors hwidth he hs hout hec hsc).1
  apply hh.mono
  simp only [currentHeightPolynomial, BinaryProfileKernel.heightPolynomial_eval,
    BinaryDiffuseCurrent.parameterPolynomial_eval, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]
  change BinarySeedAverage.outputHeight security (BinaryDiffuseCurrent.metadata security).cutoff
    (BinaryActivationProgram.cutoff security).count (precision.eval security) (BinaryProfileKernel.currentHeight bound) ≤
      BinarySeedAverage.outputHeight security ((security+2)^2) ((security+2)^2)
        (precision.eval security) (BinaryProfileKernel.currentHeight bound)
  unfold BinarySeedAverage.outputHeight BinaryWindowAverage.sumHeight BinarySeedAverage.innerHeight
    BinaryGaussianAverage.sumHeight BinaryGaussianAverage.termHeight
  gcongr

theorem current_polynomial_work (security : ℕ) (positive : Bool) (output : List Bool)
    (precision inputBits : Polynomial ℕ) (ho : output.length ≤ inputBits.eval security) :
    (current security (precision.eval security) positive output).work ≤
      (currentWorkPolynomial precision inputBits).eval security := by
  let bound := BinaryDiffuseCurrent.parameterBound security (inputBits.eval security)
  rcases BinaryDiffuseCurrent.metadata_value security with ⟨hq, hw, hc⟩
  have hqBound : Parameters.modulus security ≤ 131072*(security+2)^64 := by
    simpa only [Parameters.base] using (Parameters.modulus_bounds security).2
  have hcolors : (BinaryDiffuseCurrent.metadata security).colors ≤ bound := by
    rw [hq]; unfold bound BinaryDiffuseCurrent.parameterBound; omega
  have hwidth : (BinaryDiffuseCurrent.metadata security).width ≤ bound := by
    rw [hw]; unfold bound BinaryDiffuseCurrent.parameterBound; omega
  have hec : (BinaryDiffuseCurrent.metadata security).cutoff ≤ (security+2)^2 := by rw [hc]; omega
  have hsc : (BinaryActivationProgram.cutoff security).count ≤ (security+2)^2 := by
    rw [BinaryActivationProgram.cutoff_value]; omega
  have he : (BinaryDiffuseCurrent.metadata security).cutoff ≤ bound := by unfold bound BinaryDiffuseCurrent.parameterBound; omega
  have hs : (BinaryActivationProgram.cutoff security).count ≤ bound := by unfold bound BinaryDiffuseCurrent.parameterBound; omega
  have hout : output.length ≤ bound := by unfold bound BinaryDiffuseCurrent.parameterBound; omega
  have we := (evaluate_bounds security (BinaryDiffuseCurrent.metadata security).colors
    (BinaryDiffuseCurrent.metadata security).width (BinaryDiffuseCurrent.metadata security).cutoff
    (BinaryActivationProgram.cutoff security).count (precision.eval security) positive output bound
      hcolors hwidth he hs hout hec hsc).2
  have hfinal := BinarySeedAverage.workBound_mono
    (security := security) (bits := precision.eval security) hec hsc
    (le_refl (BinaryProfileKernel.currentHeight bound)) (le_refl (BinaryProfileKernel.currentWork bound))
  have htotal := Nat.add_le_add_right
    (Nat.add_le_add (Nat.add_le_add (BinaryDiffuseCurrent.metadata_work security) (BinaryActivationProgram.cutoff_work security))
      (we.trans hfinal)) 3
  change (current security (precision.eval security) positive output).work ≤ _ at htotal
  convert htotal using 1
  simp only [currentWorkPolynomial, BinaryDiffuseCurrent.metadataWorkPolynomial_eval,
    BinaryActivationProgram.cutoffWorkPolynomial_eval, BinarySeedAverage.workPolynomial_eval,
    BinaryProfileKernel.heightPolynomial_eval, BinaryProfileKernel.workPolynomial_eval,
    BinaryDiffuseCurrent.parameterPolynomial_eval, Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_ofNat]
  rfl

end
end CurrentAFT.BinaryProfileProgram
