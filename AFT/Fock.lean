import Mathlib.Tactic

/-!
# Hilbert estimates for genuinely joint tagged kernels

Reference V7's mixed-tail argument applies one local Hilbert operator in each
input coordinate. The theorem below proves the finite tensorization step for
an arbitrary joint kernel, without a rank-one or nuclear-norm assumption.
The concrete model's local operator estimates remain separate obligations.
-/

namespace AFT
namespace Fock

open scoped BigOperators

variable {Input₁ Input₂ Output₁ Output₂ : Type*}
variable [Fintype Input₁] [Fintype Input₂] [Fintype Output₁] [Fintype Output₂]

/-- A finite Hilbert operator specified by its matrix in orthonormal bases. -/
def response (matrix : Output₁ → Input₁ → ℝ) (input : Input₁ → ℝ) (output : Output₁) : ℝ :=
  ∑ index, matrix output index * input index

/-- The tensor product acts directly on the complete joint input kernel. -/
def tensorResponse (first : Output₁ → Input₁ → ℝ) (second : Output₂ → Input₂ → ℝ)
    (kernel : Input₁ → Input₂ → ℝ) (output₁ : Output₁) (output₂ : Output₂) : ℝ :=
  ∑ input₁, ∑ input₂,
    first output₁ input₁ * second output₂ input₂ * kernel input₁ input₂

omit [Fintype Output₁] [Fintype Output₂] in
/-- Applying the two matrices in either order gives their tensor action. -/
theorem tensorResponse_eq_iterated (first : Output₁ → Input₁ → ℝ)
    (second : Output₂ → Input₂ → ℝ) (kernel : Input₁ → Input₂ → ℝ)
    (output₁ : Output₁) (output₂ : Output₂) :
    tensorResponse first second kernel output₁ output₂ =
      response second (fun input₂ => response first (fun input₁ => kernel input₁ input₂)
        output₁) output₂ := by
  simp only [tensorResponse, response, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro input₁ _
  apply Finset.sum_congr rfl
  intro input₂ _
  ring

/-- Squared Hilbert operator norms multiply on arbitrary joint kernels.
This proves the tensor step used for tagged primary/body controls, and in
particular does not replace a joint kernel by a sum of rank-one bounds. -/
theorem joint_kernel_response_bound (first : Output₁ → Input₁ → ℝ)
    (second : Output₂ → Input₂ → ℝ) (firstBound secondBound : ℝ)
    (hsecondBound : 0 ≤ secondBound)
    (hfirst : ∀ input : Input₁ → ℝ,
      ∑ output, response first input output ^ 2 ≤
        firstBound * ∑ index, input index ^ 2)
    (hsecond : ∀ input : Input₂ → ℝ,
      ∑ output, response second input output ^ 2 ≤
        secondBound * ∑ index, input index ^ 2)
    (kernel : Input₁ → Input₂ → ℝ) :
    ∑ output₁, ∑ output₂, tensorResponse first second kernel output₁ output₂ ^ 2 ≤
      (firstBound * secondBound) * ∑ input₁, ∑ input₂, kernel input₁ input₂ ^ 2 := by
  simp_rw [tensorResponse_eq_iterated]
  calc
    (∑ output₁, ∑ output₂,
        response second (fun input₂ => response first (fun input₁ => kernel input₁ input₂)
          output₁) output₂ ^ 2) ≤
        ∑ output₁, secondBound * ∑ input₂,
          response first (fun input₁ => kernel input₁ input₂) output₁ ^ 2 := by
      apply Finset.sum_le_sum
      intro output₁ _
      exact hsecond _
    _ = secondBound * ∑ input₂, ∑ output₁,
          response first (fun input₁ => kernel input₁ input₂) output₁ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ secondBound * ∑ input₂, firstBound * ∑ input₁, kernel input₁ input₂ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hsecondBound
      apply Finset.sum_le_sum
      intro input₂ _
      exact hfirst _
    _ = (firstBound * secondBound) * ∑ input₁, ∑ input₂,
          kernel input₁ input₂ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      ring

end Fock
end AFT
