import AFT.V7ActualPrimary
import AFT.V7RootSmoothing

/-! # Actual calibrated-primary and root-body finite output channels -/

namespace AFT.GaussianSource

open scoped BigOperators Classical
open SafeConvolution

noncomputable section

attribute [local instance] actualModulusNeZero

def actualRootLaw (parameter : ℕ) : FiniteDist (Fin (Parameters.modulus parameter)) :=
  (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter)
    (Parameters.bodies parameter) (Parameters.bodies_positive parameter)).map
    (fun sample => paletteEmbedding parameter (sample : ℤ))

/-- The leading primary channel includes its actual activation factor. -/
def actualPrimaryChannel (cutoffScale : ℝ) (parameter : ℕ)
    (input output : Fin (Parameters.modulus parameter)) : ℝ :=
  v7Activation cutoffScale parameter * LinearMap.toMatrix' (actualResponse cutoffScale parameter) output input

/-- The body channel uses the actual clipped, zero-sum conditional root
marginal; its input is the public safe center. -/
def actualBodyChannel (parameter : ℕ) (input output : Fin (Parameters.modulus parameter)) : ℝ :=
  (actualRootLaw parameter).weight (output - input)

theorem actualPrimaryChannel_profile (cutoffScale : ℝ) (parameter : ℕ)
    (profile : Fin (Parameters.modulus parameter) → ℝ) (output : Fin (Parameters.modulus parameter)) :
    (∑ input, profile input * actualPrimaryChannel cutoffScale parameter input output) =
      v7Activation cutoffScale parameter * actualResponse cutoffScale parameter profile output := by
  rw [← LinearMap.toMatrix'_mulVec]
  simp only [actualPrimaryChannel, Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro input _
  ring

theorem actualBodyChannel_profile (parameter : ℕ)
    (profile : Fin (Parameters.modulus parameter) → ℝ) (output : Fin (Parameters.modulus parameter)) :
    (∑ input, profile input * actualBodyChannel parameter input output) =
      convolution (actualRootLaw parameter).weight profile output := by
  have hh := Equiv.sum_comp (Equiv.subLeft output)
    (fun input : Fin (Parameters.modulus parameter) => profile input * (actualRootLaw parameter).weight (output - input))
  have heq (shift : Fin (Parameters.modulus parameter)) : output - (output - shift) = shift := by abel
  simpa only [Equiv.subLeft_apply, heq, actualBodyChannel, convolution_apply, mul_comm] using hh.symm

theorem actualBodyChannel_nonneg (parameter : ℕ) (input output : Fin (Parameters.modulus parameter)) :
    0 ≤ actualBodyChannel parameter input output := (actualRootLaw parameter).nonneg _

theorem actualBodyChannel_mass (parameter : ℕ) (input : Fin (Parameters.modulus parameter)) :
    (∑ output, actualBodyChannel parameter input output) = 1 := by
  exact (translated_sum (actualRootLaw parameter).weight input).trans (actualRootLaw parameter).sum_one

end
end AFT.GaussianSource
