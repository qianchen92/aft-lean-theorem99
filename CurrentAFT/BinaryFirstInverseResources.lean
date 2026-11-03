import CurrentAFT.BinaryFirstInverseProgram
import CurrentAFT.BinaryMassLiftResources

/-! # Closed current-parameter resource bounds for the mass-lift producer -/
namespace CurrentAFT.BinaryFirstInverseProgram
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus prepare BinaryReferenceTables.current
  BinaryMassLiftKernel.current BinaryMassLiftKernel.prepare
  BinaryMassLiftFormula.current BinaryRankOneFunctional.current
noncomputable section

noncomputable def cacheInputHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  signHeightPolynomial precision+BinaryActivationProgram.currentHeightPolynomial precision
noncomputable def cacheHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMassLiftKernel.prepareHeightPolynomial colorsPolynomial (cacheInputHeightPolynomial precision)+cacheInputHeightPolynomial precision
noncomputable def cacheWorkPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+colorsPolynomial*(signWorkPolynomial precision+2)+2+
    BinaryActivationProgram.currentWorkPolynomial precision+
    BinaryMassLiftKernel.prepareWorkPolynomial colorsPolynomial (cacheInputHeightPolynomial precision)+4

theorem prepare_bounds (security : ℕ) (precision : Polynomial ℕ) :
    (∀ output, HeightBound ((prepare security (precision.eval security)).sign.get output).decode
      ((cacheHeightPolynomial precision).eval security)) ∧
    HeightBound (prepare security (precision.eval security)).denominator.decode
      ((cacheHeightPolynomial precision).eval security) ∧
    (prepare security (precision.eval security)).work ≤ (cacheWorkPolynomial precision).eval security := by
  let q := colors security
  let Q := colorsPolynomial.eval security
  let H := (cacheInputHeightPolynomial precision).eval security
  let sign := buildArray q (fun output => signPoint security (precision.eval security) output.val)
  let rate := BinaryActivationProgram.current security (precision.eval security)
  have hq : q ≤ Q := colors_bound security
  have hs : (signHeightPolynomial precision).eval security ≤ H := by
    simp only [H, cacheInputHeightPolynomial, Polynomial.eval_add]; omega
  have hr : (BinaryActivationProgram.currentHeightPolynomial precision).eval security ≤ H := by
    simp only [H, cacheInputHeightPolynomial, Polynomial.eval_add]; omega
  have hsign (output : Fin q) : HeightBound (sign.data.get output).decode H := by
    rw [buildArray_get]
    exact (signPoint_bounds security precision output).1.mono hs
  have hrate : HeightBound rate.data.decode H := by
    have h := (BinaryActivationProgram.current_bounds security (precision.eval security)).1
    rw [← BinaryActivationProgram.currentHeightPolynomial_eval precision security] at h
    exact h.mono hr
  have hkernel := BinaryMassLiftKernel.prepare_bounds sign.data rate.data H hsign hrate
  have wsign := buildArray_work q ((signWorkPolynomial precision).eval security)
    (fun output => signPoint security (precision.eval security) output.val)
    (fun output => (signPoint_bounds security precision output).2)
  have wmodulus := PublicParameterProgram.modulus_work security
  have wrate := BinaryActivationProgram.current_polynomial_work precision security
  change rate.work ≤ (BinaryActivationProgram.currentWorkPolynomial precision).eval security at wrate
  have wkernel := hkernel.2.trans (BinaryMassLiftKernel.prepareWork_mono hq (le_refl H))
  have hcache : (cacheHeightPolynomial precision).eval security = BinaryMassLiftKernel.prepareHeight Q H+H := by
    simp only [cacheHeightPolynomial, Polynomial.eval_add, BinaryMassLiftKernel.prepareHeightPolynomial_eval, Q, H]
  have hsignData : (prepare security (precision.eval security)).sign = sign.data := by
    unfold BinaryFirstInverseProgram.prepare
    rfl
  have hdenominator : (prepare security (precision.eval security)).denominator =
      (BinaryMassLiftKernel.prepare sign.data rate.data).data := by
    unfold BinaryFirstInverseProgram.prepare
    rfl
  have hwork : (prepare security (precision.eval security)).work =
      (PublicParameterProgram.modulus security).work+sign.work+rate.work+
        (BinaryMassLiftKernel.prepare sign.data rate.data).work+4 := by
    unfold BinaryFirstInverseProgram.prepare
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro output
    rw [hsignData]
    exact (hsign output).mono (by rw [hcache]; omega)
  · rw [hdenominator]
    exact hkernel.1.mono ((BinaryMassLiftKernel.prepareHeight_mono hq (le_refl H)).trans (by rw [hcache]; omega))
  · rw [hwork]
    have ws : sign.work ≤ Q*((signWorkPolynomial precision).eval security+2)+2 :=
      wsign.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hq) 2)
    simp only [cacheWorkPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      PublicParameterProgram.workPolynomial_eval, BinaryMassLiftKernel.prepareWorkPolynomial_eval]
    change _ ≤ PublicParameterProgram.workBound security+Q*((signWorkPolynomial precision).eval security+2)+2+
      (BinaryActivationProgram.currentWorkPolynomial precision).eval security+BinaryMassLiftKernel.prepareWork Q H+4
    omega

noncomputable def inputHeightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  cacheHeightPolynomial precision+BinaryReferenceTables.heightPolynomial precision+inputBits
noncomputable def currentHeightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMassLiftKernel.heightPolynomial colorsPolynomial (inputHeightPolynomial precision inputBits)
noncomputable def currentWorkPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryReferenceTables.currentWorkPolynomial precision+cacheWorkPolynomial precision+
    BinaryMassLiftKernel.workPolynomial colorsPolynomial (inputHeightPolynomial precision inputBits)+3

theorem current_bounds (security : ℕ) (precision inputBits : Polynomial ℕ)
    (input : Vector RationalBits (colors security)) (output : Fin (colors security))
    (hi : ∀ color, HeightBound (input.get color).decode (inputBits.eval security)) :
    HeightBound (current security (precision.eval security) input output).data.decode
      ((currentHeightPolynomial precision inputBits).eval security) ∧
      (current security (precision.eval security) input output).work ≤
        (currentWorkPolynomial precision inputBits).eval security := by
  let H := (inputHeightPolynomial precision inputBits).eval security
  have hc := prepare_bounds security precision
  have hr := BinaryReferenceTables.current_bounds security precision
  have bcache : (cacheHeightPolynomial precision).eval security ≤ H := by
    simp only [H, inputHeightPolynomial, Polynomial.eval_add]; omega
  have breference : (BinaryReferenceTables.heightPolynomial precision).eval security ≤ H := by
    simp only [H, inputHeightPolynomial, Polynomial.eval_add]; omega
  have binput : inputBits.eval security ≤ H := by
    simp only [H, inputHeightPolynomial, Polynomial.eval_add]; omega
  have hkernel := BinaryMassLiftKernel.current_bounds
    (BinaryReferenceTables.current security (precision.eval security)).primary
    (prepare security (precision.eval security)).sign input
    (BinaryReferenceTables.current security (precision.eval security)).activation
    (prepare security (precision.eval security)).denominator output H
    (fun color => (hr.1 color).mono breference) (fun color => (hc.1 color).mono bcache)
    (fun color => (hi color).mono binput) (hr.2.2.2.1.mono breference) (hc.2.1.mono bcache)
  constructor
  · change HeightBound (BinaryMassLiftKernel.current _ _ _ _ _ _).data.decode _
    apply hkernel.1.mono
    rw [currentHeightPolynomial, BinaryMassLiftKernel.heightPolynomial_eval]
    exact BinaryMassLiftKernel.height_mono (colors_bound security) (le_refl H)
  · change _+_+_+3 ≤ _
    have wk := hkernel.2.trans (BinaryMassLiftKernel.work_mono (colors_bound security) (le_refl H))
    simp only [currentWorkPolynomial, Polynomial.eval_add, Polynomial.eval_ofNat,
      BinaryMassLiftKernel.workPolynomial_eval]
    change _ ≤ (BinaryReferenceTables.currentWorkPolynomial precision).eval security+
      (cacheWorkPolynomial precision).eval security+BinaryMassLiftKernel.work (colorsPolynomial.eval security) H+3
    omega

end
end CurrentAFT.BinaryFirstInverseProgram
