import CurrentAFT.BinaryRootConvolutionResources
import AFT.BinaryIntegerData

/-! The original local seed average applied to an executed root-valued leaf.
The root is the difference of the two true sampled edge indices. -/
namespace CurrentAFT.BinarySeedRootAverage
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits FiniteConvolutionProgram
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryDiffuseCurrent.metadata BinaryActivationProgram.cutoff

def term (edgeCutoff scalarCutoff : ℕ) (kernel : IntegerBits → RationalResult)
    (left right : Fin (2*edgeCutoff+1)) (scalar : Fin (2*scalarCutoff+1)) : RationalResult :=
  let root := BinaryBodyProgram.shift edgeCutoff scalarCutoff false left right scalar
  let result := kernel ⟨root.negative,root.digits⟩
  ⟨result.data,root.work+result.work+2⟩

def evaluate (security edgeCutoff scalarCutoff bits : ℕ) (kernel : IntegerBits → RationalResult) : RationalResult :=
  BinarySeedAverage.evaluate security edgeCutoff scalarCutoff bits (term edgeCutoff scalarCutoff kernel)

def current (security bits : ℕ) (kernel : IntegerBits → RationalResult) : RationalResult :=
  let parameters := BinaryDiffuseCurrent.metadata security
  let window := BinaryActivationProgram.cutoff security
  let result := evaluate security parameters.cutoff window.count bits kernel
  ⟨result.data,parameters.work+window.work+result.work+3⟩

theorem evaluate_value (security edgeCutoff scalarCutoff bits : ℕ) (kernel : IntegerBits → RationalResult)
    (ideal : ℤ → ℚ) (hvalue : ∀ root, (kernel root).data.decode=ideal root.decode) :
    (evaluate security edgeCutoff scalarCutoff bits kernel).data.decode=
      ∑ seed : (Window edgeCutoff × Window edgeCutoff) × Window scalarCutoff,
        RationalProposalProgram.gaussianWeight security edgeCutoff bits seed.1.1*
        RationalProposalProgram.gaussianWeight security edgeCutoff bits seed.1.2*
        RationalProposalProgram.gaussianWeight security scalarCutoff bits seed.2*ideal (seed.1.1.val-seed.1.2.val) := by
  rw [evaluate, BinarySeedAverage.evaluate_window_value]
  simp only [RationalProposalProgram.gaussianWeight_eq]
  apply Finset.sum_congr rfl
  intro seed _
  simp only [term, hvalue, IntegerBits.decode, BinaryBodyProgram.shift_value,
    Bool.false_eq_true, if_false, add_zero]
  have hl : (((windowIndexEquiv edgeCutoff).symm seed.1.1).val:ℤ)-edgeCutoff=seed.1.1.val :=
    congrArg Subtype.val ((windowIndexEquiv edgeCutoff).apply_symm_apply seed.1.1)
  have hr : (((windowIndexEquiv edgeCutoff).symm seed.1.2).val:ℤ)-edgeCutoff=seed.1.2.val :=
    congrArg Subtype.val ((windowIndexEquiv edgeCutoff).apply_symm_apply seed.1.2)
  congr 2
  omega

theorem current_value (security bits : ℕ) (kernel : IntegerBits → RationalResult)
    (ideal : ℤ → ℚ) (hvalue : ∀ root, (kernel root).data.decode=ideal root.decode) :
    (current security bits kernel).data.decode=
      RationalProposalProgram.seedEvaluate security bits (fun seed => ideal (DiffuseProfiles.actualBlur security seed)) := by
  unfold current
  rw [evaluate_value security _ _ bits kernel ideal hvalue, (BinaryDiffuseCurrent.metadata_value security).2.2,
    BinaryActivationProgram.cutoff_value]
  have he : ((security+2)^2-1)/2=DiffuseProfiles.edgeCutoff security := by
    simp only [DiffuseProfiles.edgeCutoff, Parameters.sourceCutoff, Parameters.base]
  have hs : (security+2)^2-1=Parameters.sourceCutoff security-1 := by
    simp only [Parameters.sourceCutoff, Parameters.base]
  rw [he, hs]
  rfl

noncomputable section
noncomputable def rootBitsPolynomial : Polynomial ℕ := 4*(Polynomial.X+2)^2+2
noncomputable def termWorkPolynomial (leafWork : Polynomial ℕ) : Polynomial ℕ :=
  BinaryBodyProgram.shiftWorkPolynomial ((Polynomial.X+2)^2)+leafWork+2
noncomputable def heightPolynomial (precision leafBits : Polynomial ℕ) : Polynomial ℕ :=
  let count := 2*(Polynomial.X+2)^2+1
  let gaussian := 500000000*((Polynomial.X+2)^2+precision+2)^6
  count*(gaussian+count*(count*(2*gaussian+leafBits+1)+1)+1)
noncomputable def workPolynomial (precision leafBits leafWork : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDiffuseCurrent.metadataWorkPolynomial+BinaryActivationProgram.cutoffWorkPolynomial+
    BinarySeedAverage.workPolynomial ((Polynomial.X+2)^2) ((Polynomial.X+2)^2) precision leafBits (termWorkPolynomial leafWork)+3

theorem current_bounds (security : ℕ) (precision leafBits leafWork : Polynomial ℕ) (kernel : IntegerBits → RationalResult)
    (hkernel : ∀ root, root.digits.length ≤ rootBitsPolynomial.eval security →
      HeightBound (kernel root).data.decode (leafBits.eval security) ∧ (kernel root).work ≤ leafWork.eval security) :
    HeightBound (current security (precision.eval security) kernel).data.decode ((heightPolynomial precision leafBits).eval security) ∧
      (current security (precision.eval security) kernel).work ≤ (workPolynomial precision leafBits leafWork).eval security := by
  let parameters := BinaryDiffuseCurrent.metadata security
  let window := BinaryActivationProgram.cutoff security
  have he : parameters.cutoff≤(security+2)^2 := by rw [(BinaryDiffuseCurrent.metadata_value security).2.2]; omega
  have hs : window.count≤(security+2)^2 := by rw [BinaryActivationProgram.cutoff_value]; omega
  have ht (left right : Fin (2*parameters.cutoff+1)) (scalar : Fin (2*window.count+1)) :
      HeightBound (term parameters.cutoff window.count kernel left right scalar).data.decode (leafBits.eval security) ∧
        (term parameters.cutoff window.count kernel left right scalar).work ≤ (termWorkPolynomial leafWork).eval security := by
    let root := BinaryBodyProgram.shift parameters.cutoff window.count false left right scalar
    have hr := BinaryBodyProgram.shift_bounds parameters.cutoff window.count false left right scalar ((security+2)^2) he hs
    have hk := hkernel ⟨root.negative,root.digits⟩ (by
      simp only [rootBitsPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat]
      exact hr.1)
    constructor
    · exact hk.1
    · change root.work+(kernel ⟨root.negative,root.digits⟩).work+2 ≤ _
      simp only [termWorkPolynomial, Polynomial.eval_add, Polynomial.eval_ofNat, BinaryBodyProgram.shiftWorkPolynomial,
        BinaryAnchorProgram.coordinateWorkPolynomial,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one] at ⊢
      have wr : root.work ≤ BinaryBodyProgram.shiftWork ((security+2)^2) := hr.2
      unfold BinaryBodyProgram.shiftWork BinaryAnchorProgram.coordinateWork at wr
      omega
  have h := BinarySeedAverage.evaluate_bounds security parameters.cutoff window.count (precision.eval security)
    (term parameters.cutoff window.count kernel) (leafBits.eval security) ((termWorkPolynomial leafWork).eval security) he hs
    (fun left right scalar => (ht left right scalar).1) (fun left right scalar => (ht left right scalar).2)
  constructor
  · apply h.1.mono
    simp only [heightPolynomial, BinarySeedAverage.outputHeight, BinarySeedAverage.innerHeight,
      BinaryWindowAverage.sumHeight, BinaryGaussianAverage.sumHeight, BinaryGaussianAverage.termHeight,
      BinaryGaussianAverage.gaussianHeight, CurrentGaussianBits.budget, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]
    gcongr
  · have hm := BinaryDiffuseCurrent.metadata_work security
    have hw := BinaryActivationProgram.cutoff_work security
    have wh := h.2.trans (BinarySeedAverage.workBound_mono he hs (le_refl _) (le_refl _))
    change parameters.work≤_ at hm
    change window.work≤_ at hw
    change parameters.work+window.work+(evaluate security parameters.cutoff window.count (precision.eval security) kernel).work+3 ≤ _
    simp only [workPolynomial, Polynomial.eval_add, Polynomial.eval_ofNat, BinaryDiffuseCurrent.metadataWorkPolynomial_eval,
      BinaryActivationProgram.cutoffWorkPolynomial_eval, BinarySeedAverage.workPolynomial_eval,
      Polynomial.eval_pow, Polynomial.eval_X]
    exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hm hw) wh) 3

end
end CurrentAFT.BinarySeedRootAverage
