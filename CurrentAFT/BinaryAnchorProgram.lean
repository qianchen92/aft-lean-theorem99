import CurrentAFT.BinaryWindowAverage
import CurrentAFT.BinaryMarkedCurrent
import CurrentAFT.BinaryActivationProgram
import CurrentAFT.RationalProposalProgram

/-! # The actual smoothed anchor table produced by binary arithmetic -/
namespace CurrentAFT.BinaryAnchorProgram
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits FiniteConvolutionProgram
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalCounter signedAdd BinaryDiffuseCurrent.metadata BinaryActivationProgram.cutoff

def coordinate (cutoff index : ℕ) : SignedResult :=
  let first := canonicalCounter index
  let second := canonicalCounter cutoff
  let result := signedAdd false true first.digits second.digits
  ⟨result.negative, result.digits, first.work + second.work + result.work + 3⟩

theorem coordinate_value (cutoff index : ℕ) :
    signedValue (coordinate cutoff index).negative (coordinate cutoff index).digits = (index:ℤ)-cutoff := by
  unfold coordinate
  rw [signedAdd_value]
  simp only [signedValue, Bool.false_eq_true, if_false, if_true, canonicalCounter_value]
  ring

def coordinateWork (bound : ℕ) : ℕ := 100*(2*bound+1)^2+40*bound+11

theorem coordinate_bounds (cutoff index bound : ℕ) (hc : cutoff ≤ bound) (hi : index ≤ 2*bound) :
    (coordinate cutoff index).digits.length ≤ 2*bound+1 ∧
      (coordinate cutoff index).work ≤ coordinateWork bound := by
  let first := canonicalCounter index
  let second := canonicalCounter cutoff
  have hf : first.digits.length ≤ 2*bound := by
    rw [canonicalCounter_length]; exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n := index))).trans hi
  have hs : second.digits.length ≤ 2*bound := by
    rw [canonicalCounter_length]; exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n := cutoff))).trans (by omega)
  have hl := signedAdd_length false true first.digits second.digits
  have hw := signedAdd_work false true first.digits second.digits
  have wf : first.work ≤ 50*(2*bound+1)^2 := (canonicalCounter_work index).trans
    (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (by omega) 2))
  have ws : second.work ≤ 50*(2*bound+1)^2 := (canonicalCounter_work cutoff).trans
    (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (by omega) 2))
  constructor
  · exact hl.trans (by omega)
  · change first.work + second.work + (signedAdd false true first.digits second.digits).work + 3 ≤ _
    unfold coordinateWork
    omega

def atIndex (colors width primary cutoff : ℕ) (output : List Bool) (index : Fin (2*cutoff+1)) : RationalResult :=
  let scalar := coordinate cutoff index.val
  let primaryCode := canonicalCounter primary
  let value := BinaryMarkedKernel.average colors width primary 0 0 (!scalar.negative)
    scalar.digits primaryCode.digits output
  ⟨value.data, scalar.work + primaryCode.work + value.work + 3⟩

theorem atIndex_value (colors width primary cutoff : ℕ) (output : List Bool) (index : Fin (2*cutoff+1)) :
    (atIndex colors width primary cutoff output index).data.decode =
      RationalProposalProgram.anchorKernel colors width primary ((index.val:ℤ)-cutoff) (value output) := by
  unfold atIndex
  rw [BinaryMarkedKernel.average_value, BinaryTrimmedPair.signed_negate, coordinate_value]
  simp only [canonicalCounter_value]
  rfl

def kernelWork (width bound : ℕ) : ℕ := coordinateWork bound + 50*(bound+1)^2 +
  BinaryMarkedKernel.averageWork width (4*bound+10) + 3

theorem atIndex_bounds (colors width primary cutoff : ℕ) (output : List Bool) (index : Fin (2*cutoff+1))
    (bound : ℕ) (hq : colors ≤ bound) (hw : width ≤ bound) (hp : primary ≤ bound)
    (hc : cutoff ≤ bound) (ho : output.length ≤ bound) :
    HeightBound (atIndex colors width primary cutoff output index).data.decode (BinaryMarkedKernel.averageHeight width) ∧
      (atIndex colors width primary cutoff output index).work ≤ kernelWork width bound := by
  let scalar := coordinate cutoff index.val
  let primaryCode := canonicalCounter primary
  have hi : index.val ≤ 2*bound := by have := index.isLt; omega
  have hs := coordinate_bounds cutoff index.val bound hc hi
  have hscalar : scalar.digits.length ≤ 2*bound+1 := hs.1
  have hprimary : primaryCode.digits.length ≤ bound := by
    rw [canonicalCounter_length]; exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n := primary))).trans hp
  have hav := BinaryMarkedKernel.average_bounds colors width primary 0 0 (!scalar.negative) scalar.digits primaryCode.digits output
    (4*bound+10) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  constructor
  · exact hav.1
  · have ws : scalar.work ≤ coordinateWork bound := hs.2
    have wp : primaryCode.work ≤ 50*(bound+1)^2 := (canonicalCounter_work primary).trans
      (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (by omega) 2))
    change scalar.work + primaryCode.work +
      (BinaryMarkedKernel.average colors width primary 0 0 (!scalar.negative) scalar.digits primaryCode.digits output).work + 3 ≤ _
    unfold kernelWork
    omega

def evaluate (security colors width cutoff bits primary : ℕ) (output : List Bool) : RationalResult :=
  BinaryWindowAverage.evaluate security cutoff bits (atIndex colors width primary cutoff output)

theorem evaluate_value (security colors width cutoff bits primary : ℕ) (output : List Bool) :
    (evaluate security colors width cutoff bits primary output).data.decode =
      RationalProposalProgram.anchorEvaluate security colors width cutoff bits primary (value output) := by
  simp only [evaluate, BinaryWindowAverage.evaluate_value, atIndex_value, windowGaussianWeights,
    RationalProposalProgram.anchorEvaluate, RationalProposalProgram.gaussianWeight_eq]
  rw [← (windowIndexEquiv cutoff).sum_comp]
  rfl

theorem evaluate_bounds (security colors width cutoff bits primary : ℕ) (output : List Bool) (bound : ℕ)
    (hq : colors ≤ bound) (hw : width ≤ bound) (hp : primary ≤ bound)
    (hc : cutoff ≤ bound) (ho : output.length ≤ bound) (hcutoff : cutoff ≤ (security+2)^2) :
    HeightBound (evaluate security colors width cutoff bits primary output).data.decode
      (BinaryWindowAverage.sumHeight (2*cutoff+1) (BinaryGaussianAverage.gaussianHeight security bits)
        (BinaryMarkedKernel.averageHeight width)) ∧
      (evaluate security colors width cutoff bits primary output).work ≤
        BinaryWindowAverage.evaluateWork security cutoff bits (BinaryMarkedKernel.averageHeight width) (kernelWork width bound) := by
  have hk (index : Fin (2*cutoff+1)) := atIndex_bounds colors width primary cutoff output index bound hq hw hp hc ho
  exact BinaryWindowAverage.evaluate_bounds security cutoff bits _ _ _ hcutoff
    (fun index => (hk index).1) (fun index => (hk index).2)

def current (security bits primary : ℕ) (output : List Bool) : RationalResult :=
  let parameters := BinaryDiffuseCurrent.metadata security
  let window := BinaryActivationProgram.cutoff security
  let result := evaluate security parameters.colors parameters.width window.count bits primary output
  ⟨result.data, parameters.work + window.work + result.work + 3⟩

theorem current_value (security bits primary : ℕ) (output : List Bool) :
    (current security bits primary output).data.decode = RationalProposalProgram.anchor security bits primary (value output) := by
  rcases BinaryDiffuseCurrent.metadata_value security with ⟨hq, hw, _⟩
  unfold current
  rw [evaluate_value, hq, hw, BinaryActivationProgram.cutoff_value]
  unfold RationalProposalProgram.anchor
  rw [PublicParameterProgram.modulus_value]

noncomputable section
open scoped Classical

theorem current_error (security bits : ℕ) (primary output : FirstHistogram.Palette security) (outputCode : List Bool)
    (ho : value outputCode = output.val) :
    |((current security bits primary.val outputCode).data.decode:ℝ) -
      (InwardAnchor.smoothedAnchorLaw security primary).weight output| ≤ 1/(2:ℝ)^bits := by
  rw [current_value, ho]
  exact RationalProposalProgram.anchor_error security bits primary output

noncomputable def coordinateWorkPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  100*(2*bound+1)^2+40*bound+11
noncomputable def kernelWorkPolynomial (width bound : Polynomial ℕ) : Polynomial ℕ :=
  coordinateWorkPolynomial bound+50*(bound+1)^2+BinaryMarkedCurrent.averageWorkPolynomial width (4*bound+10)+3

theorem kernelWorkPolynomial_eval (width bound : Polynomial ℕ) (security : ℕ) :
    (kernelWorkPolynomial width bound).eval security = kernelWork (width.eval security) (bound.eval security) := by
  simp only [kernelWorkPolynomial, coordinateWorkPolynomial, kernelWork, coordinateWork,
    BinaryMarkedCurrent.averageWorkPolynomial_eval, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_ofNat, Polynomial.eval_one]

noncomputable def currentWorkPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDiffuseCurrent.metadataWorkPolynomial + BinaryActivationProgram.cutoffWorkPolynomial +
    BinaryWindowAverage.evaluateWorkPolynomial ((Polynomial.X+2)^2) precision
      (BinaryMarkedCurrent.averageHeightPolynomial ((Polynomial.X+2)^48))
      (kernelWorkPolynomial ((Polynomial.X+2)^48) (BinaryDiffuseCurrent.parameterPolynomial inputBits)) + 3

theorem current_polynomial_work (security : ℕ) (primary : FirstHistogram.Palette security) (output : List Bool)
    (precision inputBits : Polynomial ℕ) (ho : output.length ≤ inputBits.eval security) :
    (current security (precision.eval security) primary.val output).work ≤
      (currentWorkPolynomial precision inputBits).eval security := by
  let bound := BinaryDiffuseCurrent.parameterBound security (inputBits.eval security)
  rcases BinaryDiffuseCurrent.metadata_value security with ⟨hq, hw, _⟩
  have hqBound : Parameters.modulus security ≤ 131072*(security+2)^64 := by
    simpa only [Parameters.base] using (Parameters.modulus_bounds security).2
  have hp := primary.isLt
  have hcolors : (BinaryDiffuseCurrent.metadata security).colors ≤ bound := by
    rw [hq]; unfold bound BinaryDiffuseCurrent.parameterBound; omega
  have hwidth : (BinaryDiffuseCurrent.metadata security).width ≤ bound := by
    rw [hw]; unfold bound BinaryDiffuseCurrent.parameterBound; omega
  have hprimary : primary.val ≤ bound := by unfold bound BinaryDiffuseCurrent.parameterBound; omega
  have hcutoff : (BinaryActivationProgram.cutoff security).count ≤ (security+2)^2 := by
    rw [BinaryActivationProgram.cutoff_value]; omega
  have hcut : (BinaryActivationProgram.cutoff security).count ≤ bound := by
    unfold bound BinaryDiffuseCurrent.parameterBound; omega
  have houtput : output.length ≤ bound := by unfold bound BinaryDiffuseCurrent.parameterBound; omega
  have we := (evaluate_bounds security (BinaryDiffuseCurrent.metadata security).colors
    (BinaryDiffuseCurrent.metadata security).width (BinaryActivationProgram.cutoff security).count
    (precision.eval security) primary.val output bound hcolors hwidth hprimary hcut houtput hcutoff).2
  conv_rhs at we => rw [hw, BinaryActivationProgram.cutoff_value]
  have hsum := BinaryWindowAverage.sumWork_mono
    (gh := BinaryGaussianAverage.gaussianHeight security (precision.eval security))
    (kh := BinaryMarkedKernel.averageHeight ((security+2)^48))
    (kw := kernelWork ((security+2)^48) bound)
    (show 2*((security+2)^2-1)+1 ≤ 2*(security+2)^2+1 by omega) le_rfl le_rfl le_rfl
  have hfinal := Nat.add_le_add_right
    (Nat.add_le_add (show CurrentGaussianBits.tableWork security (precision.eval security) ≤
      CurrentGaussianBits.tableWork security (precision.eval security) from le_rfl) hsum) 2
  have htotal := Nat.add_le_add_right
    (Nat.add_le_add (Nat.add_le_add (BinaryDiffuseCurrent.metadata_work security) (BinaryActivationProgram.cutoff_work security))
      (we.trans hfinal)) 3
  change (current security (precision.eval security) primary.val output).work ≤ _ at htotal
  convert htotal using 1
  simp only [currentWorkPolynomial, BinaryDiffuseCurrent.metadataWorkPolynomial_eval,
    BinaryActivationProgram.cutoffWorkPolynomial_eval, BinaryWindowAverage.evaluateWorkPolynomial_eval,
    kernelWorkPolynomial_eval, BinaryDiffuseCurrent.parameterPolynomial_eval,
    BinaryMarkedCurrent.averageHeightPolynomial, BinaryMarkedKernel.averageHeight,
    BinaryWindowAverage.evaluateWork, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_ofNat]
  rfl

end
end CurrentAFT.BinaryAnchorProgram
