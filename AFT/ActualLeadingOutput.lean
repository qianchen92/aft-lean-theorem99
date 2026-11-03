import AFT.RepresentedOutput
import AFT.MixedSingleton
import AFT.ActualOutputChannels
import AFT.V7ReferenceLaws

/-! # Literal leading evaluation at the actual V7 probability laws -/

namespace AFT.RepresentedPolynomial

open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

variable {Color Output : Type*} [Fintype Color] [Fintype Output]

theorem singleton_seedOutput (primary body : FiniteDist Color)
    (primaryChannel bodyChannel : Color → Output → ℝ) (kernel : Color → ℝ) :
    seedOutput primary body primaryChannel bodyChannel (primarySingletonInput kernel) =
      ∑ output, MvPolynomial.C (∑ input, primary.weight input * kernel input * primaryChannel input output) *
        MvPolynomial.X output := by
  unfold seedOutput
  change (∑ word : Fin 1 → Color, MvPolynomial.C (kernel (word 0) *
    ∏ slot, primary.weight (word slot)) * ∏ slot, channelForm primaryChannel (word slot)) = _
  rw [← Equiv.sum_comp (Equiv.funUnique (Fin 1) Color).symm]
  simp only [Equiv.funUnique_symm_apply, uniqueElim_const, Fin.prod_univ_one, channelForm, Finset.mul_sum,
    ← mul_assoc, ← map_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro output _
  simp only [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro input _
  congr 2
  ring

theorem body_singleton_seedOutput (primary body : FiniteDist Color)
    (primaryChannel bodyChannel : Color → Output → ℝ) (kernel : Color → ℝ) :
    seedOutput primary body primaryChannel bodyChannel (bodySingletonInput kernel) =
      ∑ output, MvPolynomial.C (∑ input, body.weight input * kernel input * bodyChannel input output) *
        MvPolynomial.X output := by
  have heq : seedOutput primary body primaryChannel bodyChannel (bodySingletonInput kernel) =
      seedOutput body primary bodyChannel primaryChannel (primarySingletonInput kernel) := by
    rfl
  rw [heq, singleton_seedOutput]

end

end AFT.RepresentedPolynomial

namespace AFT.V7Calibration

open GaussianSource RepresentedPolynomial SafeConvolution
open scoped BigOperators Classical

noncomputable section

attribute [local instance] actualModulusNeZero

def actualLeadingOutput (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) :
    Table (InputSeed (Fin (Parameters.modulus parameter))) →ₐ[ℝ]
      MvPolynomial (Fin (Parameters.modulus parameter)) ℝ :=
  outputHom (actualPrimaryLaw cutoffScale parameter beta) (actualBodyLaw cutoffScale parameter beta)
    (actualPrimaryChannel cutoffScale parameter) (actualBodyChannel parameter)

theorem actualLeadingOutput_primary (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (kernel : Fin (Parameters.modulus parameter) → ℝ) :
    actualLeadingOutput cutoffScale parameter beta (MvPolynomial.X (primarySingletonInput kernel)) =
      ∑ output, MvPolynomial.C (v7Activation cutoffScale parameter *
        actualResponse cutoffScale parameter
          (fun input => (actualPrimaryLaw cutoffScale parameter beta).weight input * kernel input) output) *
        MvPolynomial.X output := by
  rw [actualLeadingOutput, outputHom_X, singleton_seedOutput]
  apply Finset.sum_congr rfl
  intro output _
  congr 2
  exact actualPrimaryChannel_profile cutoffScale parameter _ output

theorem actualLeadingOutput_body (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (kernel : Fin (Parameters.modulus parameter) → ℝ) :
    actualLeadingOutput cutoffScale parameter beta (MvPolynomial.X (bodySingletonInput kernel)) =
      ∑ output, MvPolynomial.C (convolution (actualRootLaw parameter).weight
        (fun input => (actualBodyLaw cutoffScale parameter beta).weight input * kernel input) output) *
        MvPolynomial.X output := by
  rw [actualLeadingOutput, outputHom_X, body_singleton_seedOutput]
  apply Finset.sum_congr rfl
  intro output _
  congr 2
  exact actualBodyChannel_profile parameter _ output

end

end AFT.V7Calibration
