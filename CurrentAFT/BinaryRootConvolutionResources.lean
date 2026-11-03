import CurrentAFT.BinaryRootConvolution

/-! # Complete current-parameter resources for the root convolution -/
namespace CurrentAFT.BinaryRootConvolution
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryDiffuseCurrent.metadata BinaryActivationProgram.cutoff
  evaluate BinaryRootConvolutionKernel.current BinaryPaletteLookup.current

theorem evaluate_bounds (security count edgeCutoff scalarCutoff bits : ℕ) (table : Vector RationalBits count)
    (output : List Bool) (bound profileBits : ℕ)
    (hc : count≤bound) (he : edgeCutoff≤bound) (hs : scalarCutoff≤bound) (ho : output.length≤bound)
    (hec : edgeCutoff≤(security+2)^2) (hsc : scalarCutoff≤(security+2)^2)
    (ht : ∀ color, HeightBound (table.get color).decode profileBits) :
    HeightBound (evaluate security count edgeCutoff scalarCutoff bits table output).data.decode
      (BinarySeedAverage.outputHeight security edgeCutoff scalarCutoff bits (count*(profileBits+1))) ∧
      (evaluate security count edgeCutoff scalarCutoff bits table output).work ≤
        50*(bound+1)^2+BinarySeedAverage.workBound security edgeCutoff scalarCutoff bits (count*(profileBits+1))
          (BinaryRootConvolutionKernel.work count bound profileBits)+2 := by
  have hm : (canonicalCounter count).digits.length≤bound := by
    rw [canonicalCounter_length]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n := count))).trans hc
  have hk (left right : Fin (2*edgeCutoff+1)) (scalar : Fin (2*scalarCutoff+1)) :=
    BinaryRootConvolutionKernel.current_bounds edgeCutoff scalarCutoff (canonicalCounter count).digits output table
      left right scalar bound profileBits he hs hm ho ht
  have h := BinarySeedAverage.evaluate_bounds security edgeCutoff scalarCutoff bits
    (BinaryRootConvolutionKernel.current edgeCutoff scalarCutoff (canonicalCounter count).digits output table)
    (count*(profileBits+1)) (BinaryRootConvolutionKernel.work count bound profileBits) hec hsc
    (fun left right scalar => (hk left right scalar).1) (fun left right scalar => (hk left right scalar).2)
  constructor
  · unfold evaluate
    exact h.1
  · unfold evaluate
    have wc := (canonicalCounter_work count).trans
      (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right hc 1) 2))
    change _+_+2≤_
    omega

private theorem kernelWork_mono_count {count larger bound bits : ℕ} (hc : count≤larger) :
    BinaryRootConvolutionKernel.work count bound bits≤BinaryRootConvolutionKernel.work larger bound bits := by
  unfold BinaryRootConvolutionKernel.work BinaryPaletteLookup.work BinaryPaletteLookup.termWork primitiveWorkBound
  gcongr

noncomputable section
noncomputable def parameterPolynomial (inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.colorsPolynomial+(Polynomial.X+2)^2+inputBits
noncomputable def kernelHeightPolynomial (profileBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.colorsPolynomial*(profileBits+1)
noncomputable def keyWorkPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  BinaryBodyProgram.shiftWorkPolynomial bound+100*bound+48+60*(5*bound+4)^2+13
noncomputable def kernelWorkPolynomial (bound profileBits : Polynomial ℕ) : Polynomial ℕ :=
  let Q := BinaryFirstInverseProgram.colorsPolynomial
  let key := 5*bound+3
  keyWorkPolynomial bound+Q*(50*(Q+1)^2+48*(Q+key)+42+3*Q+3+
    primitiveWorkPolynomial ((Q+1)*(profileBits+1))+2)+2+2
noncomputable def heightPolynomial (precision _inputBits profileBits : Polynomial ℕ) : Polynomial ℕ :=
  let count := 2*(Polynomial.X+2)^2+1
  let gaussian := 500000000*((Polynomial.X+2)^2+precision+2)^6
  count*(gaussian+count*(count*(2*gaussian+kernelHeightPolynomial profileBits+1)+1)+1)
noncomputable def workPolynomial (precision inputBits profileBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDiffuseCurrent.metadataWorkPolynomial+BinaryActivationProgram.cutoffWorkPolynomial+PublicParameterProgram.workPolynomial+
    50*(parameterPolynomial inputBits+1)^2+
    BinarySeedAverage.workPolynomial ((Polynomial.X+2)^2) ((Polynomial.X+2)^2) precision
      (kernelHeightPolynomial profileBits) (kernelWorkPolynomial (parameterPolynomial inputBits) profileBits)+6

theorem keyWorkPolynomial_eval (bound : Polynomial ℕ) (security : ℕ) :
    (keyWorkPolynomial bound).eval security = BinaryRootConvolutionKernel.keyWork (bound.eval security) := by
  simp only [keyWorkPolynomial, BinaryRootConvolutionKernel.keyWork, BinaryBodyProgram.shiftWorkPolynomial,
    BinaryBodyProgram.shiftWork, BinaryAnchorProgram.coordinateWorkPolynomial, BinaryAnchorProgram.coordinateWork,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat, Polynomial.eval_one]
  ring

theorem kernelWorkPolynomial_eval (bound profileBits : Polynomial ℕ) (security : ℕ) :
    (kernelWorkPolynomial bound profileBits).eval security =
      BinaryRootConvolutionKernel.work (BinaryFirstInverseProgram.colorsPolynomial.eval security) (bound.eval security) (profileBits.eval security) := by
  simp only [kernelWorkPolynomial, BinaryRootConvolutionKernel.work, BinaryRootConvolutionKernel.keyBits,
    BinaryPaletteLookup.work, BinaryPaletteLookup.termWork, keyWorkPolynomial_eval, primitiveWorkPolynomial_eval,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat, Polynomial.eval_one]
  ring

theorem current_bounds (security : ℕ) (precision inputBits profileBits : Polynomial ℕ)
    (table : Vector RationalBits (BinaryFirstInverseProgram.colors security)) (output : List Bool)
    (ho : output.length ≤ inputBits.eval security)
    (ht : ∀ color, HeightBound (table.get color).decode (profileBits.eval security)) :
    HeightBound (current security (precision.eval security) table output).data.decode
      ((heightPolynomial precision inputBits profileBits).eval security) ∧
      (current security (precision.eval security) table output).work ≤ (workPolynomial precision inputBits profileBits).eval security := by
  let parameters := BinaryDiffuseCurrent.metadata security
  let window := BinaryActivationProgram.cutoff security
  let modulus := PublicParameterProgram.modulus security
  let B := (parameterPolynomial inputBits).eval security
  let Q := BinaryFirstInverseProgram.colorsPolynomial.eval security
  let H := profileBits.eval security
  have hq : modulus.count≤Q := BinaryFirstInverseProgram.colors_bound security
  have hB : B=Q+(security+2)^2+inputBits.eval security := by
    simp only [B, parameterPolynomial, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat, Q]
  have he : parameters.cutoff≤(security+2)^2 := by rw [(BinaryDiffuseCurrent.metadata_value security).2.2]; omega
  have hs : window.count≤(security+2)^2 := by rw [BinaryActivationProgram.cutoff_value]; omega
  have hk := evaluate_bounds security modulus.count parameters.cutoff window.count (precision.eval security) table output B H
    (hq.trans (by rw [hB]; omega)) (he.trans (by rw [hB]; omega)) (hs.trans (by rw [hB]; omega))
    (ho.trans (by rw [hB]; omega)) he hs ht
  have hheight : BinarySeedAverage.outputHeight security parameters.cutoff window.count (precision.eval security)
      (modulus.count*(H+1)) ≤ (heightPolynomial precision inputBits profileBits).eval security := by
    simp only [heightPolynomial, kernelHeightPolynomial, BinarySeedAverage.outputHeight, BinarySeedAverage.innerHeight,
      BinaryWindowAverage.sumHeight, BinaryGaussianAverage.sumHeight, BinaryGaussianAverage.termHeight,
      BinaryGaussianAverage.gaussianHeight, CurrentGaussianBits.budget, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]
    dsimp only [Q, H] at hq ⊢
    gcongr
  have wkernel := kernelWork_mono_count (bound := B) (bits := H) hq
  have wseed := BinarySeedAverage.workBound_mono (security := security) (bits := precision.eval security)
    he hs (Nat.mul_le_mul_right (H+1) hq) wkernel
  have wp := BinaryDiffuseCurrent.metadata_work security
  have ww := BinaryActivationProgram.cutoff_work security
  have wm := PublicParameterProgram.modulus_work security
  change parameters.work≤_ at wp
  change window.work≤_ at ww
  change modulus.work≤_ at wm
  constructor
  · exact hk.1.mono hheight
  · have we := hk.2.trans (Nat.add_le_add_right (Nat.add_le_add_left wseed (50*(B+1)^2)) 2)
    change parameters.work+window.work+modulus.work+
      (evaluate security modulus.count parameters.cutoff window.count (precision.eval security) table output).work+4≤_
    simp only [workPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
      Polynomial.eval_one, Polynomial.eval_X, BinaryDiffuseCurrent.metadataWorkPolynomial_eval, BinaryActivationProgram.cutoffWorkPolynomial_eval,
      PublicParameterProgram.workPolynomial_eval, BinarySeedAverage.workPolynomial_eval, kernelWorkPolynomial_eval,
      kernelHeightPolynomial]
    change _≤BinaryDiffuseCurrent.metadataWork security+BinaryActivationProgram.cutoffWork security+PublicParameterProgram.workBound security+
      50*(B+1)^2+BinarySeedAverage.workBound security ((security+2)^2) ((security+2)^2) (precision.eval security)
        (Q*(H+1)) (BinaryRootConvolutionKernel.work Q B H)+6
    omega

end
end CurrentAFT.BinaryRootConvolution
