import CurrentAFT.BinaryAnchorProgram
import CurrentAFT.BinaryProposalMetadata
import AFT.BinaryMatrixArray

/-! # The complete current anchor matrix as an executed binary array -/
namespace CurrentAFT.BinaryAnchorTable
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalCounter PublicParameterProgram.modulus BinaryDiffuseCurrent.metadata BinaryActivationProgram.cutoff

def point (security bits primary output : ℕ) : RationalResult :=
  let code := canonicalCounter output
  let result := BinaryAnchorProgram.current security bits primary code.digits
  ⟨result.data, code.work+result.work+2⟩

theorem point_value (security bits primary output : ℕ) :
    (point security bits primary output).data.decode = RationalProposalProgram.anchor security bits primary output := by
  simp only [point, BinaryAnchorProgram.current_value, canonicalCounter_value]

def current (security bits : ℕ) : MatrixResult (PublicParameterProgram.modulus security).count :=
  let colors := PublicParameterProgram.modulus security
  let result := buildMatrix colors.count (fun primary output => point security bits primary.val output.val)
  ⟨result.data, colors.work+result.work+2⟩

theorem current_value (security bits : ℕ) (primary output : Fin (PublicParameterProgram.modulus security).count) :
    (((current security bits).data.get primary).get output).decode =
      RationalProposalProgram.anchor security bits primary.val output.val := by
  simp only [current, buildMatrix_get, point_value]

theorem anchor_data (security bits primary : ℕ) (output : List Bool) :
    (BinaryAnchorProgram.current security bits primary output).data =
      (BinaryAnchorProgram.evaluate security (BinaryDiffuseCurrent.metadata security).colors
        (BinaryDiffuseCurrent.metadata security).width (BinaryActivationProgram.cutoff security).count bits primary output).data := by
  unfold BinaryAnchorProgram.current
  rfl

noncomputable section

noncomputable def pointHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  (2*(Polynomial.X+2)^2+1)*
    (500000000*((Polynomial.X+2)^2+precision+2)^6+4*(Polynomial.X+2)^48+4)

private theorem anchor_height (security : ℕ) (primary : FirstHistogram.Palette security) (output : List Bool)
    (precision inputBits : Polynomial ℕ) (ho : output.length ≤ inputBits.eval security) :
    HeightBound (BinaryAnchorProgram.current security (precision.eval security) primary.val output).data.decode
      ((pointHeightPolynomial precision).eval security) := by
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
  have hh := (BinaryAnchorProgram.evaluate_bounds security (BinaryDiffuseCurrent.metadata security).colors
    (BinaryDiffuseCurrent.metadata security).width (BinaryActivationProgram.cutoff security).count
    (precision.eval security) primary.val output bound hcolors hwidth hprimary hcut houtput hcutoff).1
  rw [anchor_data]
  apply hh.mono
  rw [hw]
  simp only [pointHeightPolynomial, BinaryWindowAverage.sumHeight, BinaryGaussianAverage.gaussianHeight,
    CurrentGaussianBits.budget, BinaryMarkedKernel.averageHeight,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat,
    Polynomial.eval_one]
  exact Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hcutoff) 1) (by omega)

noncomputable def currentHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ := pointHeightPolynomial precision
noncomputable def currentWorkPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  let count := BinaryProposalMetadata.sizePolynomial
  let pointWork := 50*(count+1)^2+BinaryAnchorProgram.currentWorkPolynomial precision count+2
  PublicParameterProgram.workPolynomial+count*(count*(pointWork+2)+4)+4

theorem current_bounds (security : ℕ) (precision : Polynomial ℕ) :
    (∀ primary output, HeightBound (((current security (precision.eval security)).data.get primary).get output).decode
      ((currentHeightPolynomial precision).eval security)) ∧
    (current security (precision.eval security)).work ≤ (currentWorkPolynomial precision).eval security := by
  let colors := PublicParameterProgram.modulus security
  let bound := BinaryProposalMetadata.sizePolynomial.eval security
  have hc : colors.count ≤ bound := by
    change (PublicParameterProgram.modulus security).count ≤ BinaryProposalMetadata.sizePolynomial.eval security
    rw [BinaryProposalMetadata.sizePolynomial_eval, PublicParameterProgram.modulus_value]
    exact (BinaryProposalMetadata.counts_value security).1 ▸ (BinaryProposalMetadata.counts_bounds security).1
  have hpoint (primary output : Fin colors.count) :
      HeightBound (point security (precision.eval security) primary.val output.val).data.decode
        ((pointHeightPolynomial precision).eval security) ∧
      (point security (precision.eval security) primary.val output.val).work ≤
        50*(bound+1)^2+(BinaryAnchorProgram.currentWorkPolynomial precision BinaryProposalMetadata.sizePolynomial).eval security+2 := by
    let p : FirstHistogram.Palette security := ⟨primary.val, primary.isLt.trans_le (PublicParameterProgram.modulus_value security).le⟩
    have hi : output.val ≤ bound := (Nat.le_of_lt output.isLt).trans hc
    have hl : (canonicalCounter output.val).digits.length ≤ bound := by
      rw [canonicalCounter_length]
      exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n := output.val))).trans hi
    have hh := anchor_height security p (canonicalCounter output.val).digits precision BinaryProposalMetadata.sizePolynomial hl
    have wa := BinaryAnchorProgram.current_polynomial_work security p (canonicalCounter output.val).digits precision BinaryProposalMetadata.sizePolynomial hl
    have we := (canonicalCounter_work output.val).trans
      (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right hi 1) 2))
    exact ⟨hh, Nat.add_le_add_right (Nat.add_le_add we wa) 2⟩
  constructor
  · intro primary output
    simpa only [current, buildMatrix_get] using (hpoint primary output).1
  · have wm := buildMatrix_work colors.count
      (50*(bound+1)^2+(BinaryAnchorProgram.currentWorkPolynomial precision BinaryProposalMetadata.sizePolynomial).eval security+2)
      (fun primary output => point security (precision.eval security) primary.val output.val)
      (fun primary output => (hpoint primary output).2)
    have wc : colors.work ≤ PublicParameterProgram.workBound security := PublicParameterProgram.modulus_work security
    have hb := Nat.mul_le_mul hc
      (Nat.add_le_add_right (Nat.mul_le_mul_right
        (50*(bound+1)^2+(BinaryAnchorProgram.currentWorkPolynomial precision BinaryProposalMetadata.sizePolynomial).eval security+4) hc) 4)
    change colors.work+(buildMatrix colors.count (fun primary output => point security (precision.eval security) primary.val output.val)).work+2 ≤ _
    simp only [currentWorkPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_ofNat, Polynomial.eval_one, PublicParameterProgram.workPolynomial_eval]
    change _ ≤ PublicParameterProgram.workBound security+
      bound*(bound*(50*(bound+1)^2+(BinaryAnchorProgram.currentWorkPolynomial precision BinaryProposalMetadata.sizePolynomial).eval security+4)+4)+4
    have wm' : (buildMatrix colors.count (fun primary output => point security (precision.eval security) primary.val output.val)).work ≤
        colors.count*(colors.count*(50*(bound+1)^2+(BinaryAnchorProgram.currentWorkPolynomial precision BinaryProposalMetadata.sizePolynomial).eval security+4)+4)+2 := by
      convert wm using 1
    omega

end
end CurrentAFT.BinaryAnchorTable
