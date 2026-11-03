import CurrentAFT.BinaryWindowAverage

/-! # The three actual local Gaussian seeds evaluated by finite binary sums

Only two public blur edges and the one local scalar are averaged. This
does not enumerate the body latent word or an entire public core.
-/
namespace CurrentAFT.BinarySeedAverage
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def evaluate (security edgeCutoff scalarCutoff bits : ℕ)
    (kernel : Fin (2*edgeCutoff+1) → Fin (2*edgeCutoff+1) → Fin (2*scalarCutoff+1) → RationalResult) : RationalResult :=
  BinaryWindowAverage.evaluate security scalarCutoff bits (fun scalar =>
    BinaryGaussianAverage.evaluate security edgeCutoff bits (fun left right => kernel left right scalar))

theorem evaluate_value (security edgeCutoff scalarCutoff bits : ℕ)
    (kernel : Fin (2*edgeCutoff+1) → Fin (2*edgeCutoff+1) → Fin (2*scalarCutoff+1) → RationalResult) :
    (evaluate security edgeCutoff scalarCutoff bits kernel).data.decode =
      ∑ left, ∑ right, ∑ scalar,
        windowGaussianWeights (WindowGaussianSampler.squaredWidth security) edgeCutoff bits left *
        windowGaussianWeights (WindowGaussianSampler.squaredWidth security) edgeCutoff bits right *
        windowGaussianWeights (WindowGaussianSampler.squaredWidth security) scalarCutoff bits scalar *
        (kernel left right scalar).data.decode := by
  simp only [evaluate, BinaryWindowAverage.evaluate_value, BinaryGaussianAverage.evaluate_value,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro left _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro right _
  apply Finset.sum_congr rfl
  intro scalar _
  ring

theorem evaluate_window_value (security edgeCutoff scalarCutoff bits : ℕ)
    (kernel : Fin (2*edgeCutoff+1) → Fin (2*edgeCutoff+1) → Fin (2*scalarCutoff+1) → RationalResult) :
    (evaluate security edgeCutoff scalarCutoff bits kernel).data.decode =
      ∑ seed : (Window edgeCutoff × Window edgeCutoff) × Window scalarCutoff,
        windowApproxWeight (WindowGaussianSampler.squaredWidth security) edgeCutoff bits seed.1.1 *
        windowApproxWeight (WindowGaussianSampler.squaredWidth security) edgeCutoff bits seed.1.2 *
        windowApproxWeight (WindowGaussianSampler.squaredWidth security) scalarCutoff bits seed.2 *
        (kernel ((FiniteConvolutionProgram.windowIndexEquiv edgeCutoff).symm seed.1.1)
          ((FiniteConvolutionProgram.windowIndexEquiv edgeCutoff).symm seed.1.2)
          ((FiniteConvolutionProgram.windowIndexEquiv scalarCutoff).symm seed.2)).data.decode := by
  rw [evaluate_value]
  simp only [Fintype.sum_prod_type]
  rw [← (FiniteConvolutionProgram.windowIndexEquiv edgeCutoff).sum_comp]
  apply Finset.sum_congr rfl
  intro left _
  rw [← (FiniteConvolutionProgram.windowIndexEquiv edgeCutoff).sum_comp]
  apply Finset.sum_congr rfl
  intro right _
  rw [← (FiniteConvolutionProgram.windowIndexEquiv scalarCutoff).sum_comp]
  simp only [Equiv.symm_apply_apply, windowGaussianWeights]

def innerHeight (security edgeCutoff bits kernelHeight : ℕ) : ℕ :=
  BinaryGaussianAverage.sumHeight (2*edgeCutoff+1) (BinaryGaussianAverage.gaussianHeight security bits) kernelHeight
def outputHeight (security edgeCutoff scalarCutoff bits kernelHeight : ℕ) : ℕ :=
  BinaryWindowAverage.sumHeight (2*scalarCutoff+1) (BinaryGaussianAverage.gaussianHeight security bits)
    (innerHeight security edgeCutoff bits kernelHeight)
def workBound (security edgeCutoff scalarCutoff bits kernelHeight kernelWork : ℕ) : ℕ :=
  BinaryWindowAverage.evaluateWork security scalarCutoff bits (innerHeight security edgeCutoff bits kernelHeight)
    (BinaryGaussianAverage.evaluateWork security edgeCutoff bits kernelHeight kernelWork)

theorem evaluate_bounds (security edgeCutoff scalarCutoff bits : ℕ)
    (kernel : Fin (2*edgeCutoff+1) → Fin (2*edgeCutoff+1) → Fin (2*scalarCutoff+1) → RationalResult)
    (kh kw : ℕ) (he : edgeCutoff ≤ (security+2)^2) (hs : scalarCutoff ≤ (security+2)^2)
    (hh : ∀ left right scalar, HeightBound (kernel left right scalar).data.decode kh)
    (hw : ∀ left right scalar, (kernel left right scalar).work ≤ kw) :
    HeightBound (evaluate security edgeCutoff scalarCutoff bits kernel).data.decode
      (outputHeight security edgeCutoff scalarCutoff bits kh) ∧
      (evaluate security edgeCutoff scalarCutoff bits kernel).work ≤ workBound security edgeCutoff scalarCutoff bits kh kw := by
  have hi (scalar : Fin (2*scalarCutoff+1)) := BinaryGaussianAverage.evaluate_bounds security edgeCutoff bits
    (fun left right => kernel left right scalar) kh kw he (fun left right => hh left right scalar)
    (fun left right => hw left right scalar)
  exact BinaryWindowAverage.evaluate_bounds security scalarCutoff bits _ _ _ hs
    (fun scalar => (hi scalar).1) (fun scalar => (hi scalar).2)

theorem workBound_mono {security bits e e' s s' kh kh' kw kw' : ℕ}
    (he : e ≤ e') (hs : s ≤ s') (hh : kh ≤ kh') (hw : kw ≤ kw') :
    workBound security e s bits kh kw ≤ workBound security e' s' bits kh' kw' := by
  unfold workBound BinaryWindowAverage.evaluateWork
  apply Nat.add_le_add_right
  apply Nat.add_le_add le_rfl
  apply BinaryWindowAverage.sumWork_mono (by omega) le_rfl
  · unfold innerHeight BinaryGaussianAverage.sumHeight BinaryGaussianAverage.termHeight
    gcongr
  · unfold BinaryGaussianAverage.evaluateWork
    exact Nat.add_le_add_right (Nat.add_le_add le_rfl (BinaryGaussianAverage.sumWork_mono (by omega) le_rfl hh hw)) 2

noncomputable def innerHeightPolynomial (edge precision kh : Polynomial ℕ) : Polynomial ℕ :=
  let count := 2*edge+1
  count*(count*(2*(500000000*((Polynomial.X+2)^2+precision+2)^6)+kh+1)+1)
noncomputable def workPolynomial (edge scalar precision kh kw : Polynomial ℕ) : Polynomial ℕ :=
  BinaryWindowAverage.evaluateWorkPolynomial scalar precision (innerHeightPolynomial edge precision kh)
    (BinaryGaussianAverage.evaluateWorkPolynomial edge precision kh kw)

theorem workPolynomial_eval (edge scalar precision kh kw : Polynomial ℕ) (security : ℕ) :
    (workPolynomial edge scalar precision kh kw).eval security =
      workBound security (edge.eval security) (scalar.eval security) (precision.eval security) (kh.eval security) (kw.eval security) := by
  simp only [workPolynomial, innerHeightPolynomial, workBound, innerHeight,
    BinaryWindowAverage.evaluateWorkPolynomial_eval, BinaryGaussianAverage.evaluateWorkPolynomial_eval,
    BinaryGaussianAverage.sumHeight, BinaryGaussianAverage.termHeight, BinaryGaussianAverage.gaussianHeight,
    CurrentGaussianBits.budget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]

end CurrentAFT.BinarySeedAverage
