import AFT.JointPairOutput

/-! # Exact leading image of the actual one-primary one-body inverse -/

namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Color : Type*} [Fintype Color]

theorem mixed_pair_seedOutputMass (primary body : FiniteDist Color)
    (primaryChannel bodyChannel : Color → Color → ℝ) (kernel : (Fin 2 → Color) → ℝ)
    (output : Fin 2 → Color) :
    seedOutputMass primary body primaryChannel bodyChannel ⟨1, 1, kernel⟩ output =
      ∑ first, ∑ second, (primary.weight first * body.weight second * kernel ![first, second]) *
        primaryChannel first (output 0) * bodyChannel second (output 1) := by
  unfold seedOutputMass
  calc
    _ = ∑ word : Fin 2 → Color,
      (kernel word * (primary.weight (word 0) * body.weight (word 1))) *
        (primaryChannel (word 0) (output 0) * bodyChannel (word 1) (output 1)) := by
      apply Finset.sum_congr (by ext; simp)
      intro word _
      change (kernel word *
        (∏ slot : Fin 2, (inputReference primary body ⟨1, 1, kernel⟩ slot).weight (word slot))) *
        (∏ slot : Fin 2, seedChannel primaryChannel bodyChannel ⟨1, 1, kernel⟩ slot (word slot) (output slot)) = _
      simp only [Fin.prod_univ_two]
      rfl
    _ = _ := by
      rw [← (finTwoArrowEquiv Color).symm.sum_comp, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro first _
      apply Finset.sum_congr rfl
      intro second _
      change (kernel ![first, second] * (primary.weight first * body.weight second)) *
        (primaryChannel first (output 0) * bodyChannel second (output 1)) = _
      ring

omit [Fintype Color] in
theorem update_pair_first (first second next : Color) :
    Function.update ![first, second] (0 : Fin 2) next = ![next, second] := by
  funext slot
  fin_cases slot <;> simp

theorem inverse_mixed_pair_row (primary body : FiniteDist Color)
    (rho : ℝ) (hrho : rho ≠ 0) (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ))
    (kernel : (Fin 2 → Color) → ℝ) (hprimary : ∀ color, primary.weight color ≠ 0)
    (output center : Color) :
    rho * operator (fun input => primary.weight input *
      (inversePrimarySeed primary body rho operator ⟨1, 1, kernel⟩).kernel ![input, center]) output =
      primary.weight output * kernel ![output, center] := by
  have hi := congrFun (inversePrimarySeed_exact primary body rho hrho operator ⟨1, 1, kernel⟩ hprimary)
    ![output, center]
  have hc : primaryCoordinates (⟨1, 1, kernel⟩ : InputSeed Color) = [0] := by
    simp [primaryCoordinates, List.ofFn_succ]
  simp only [hc, List.reverse_cons, List.reverse_nil, List.nil_append, MixedKernel.inputIteration_cons,
    MixedKernel.inputIteration_nil, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul, pow_one] at hi
  change rho * (operator (fun input => primary.weight input *
    (inversePrimarySeed primary body rho operator ⟨1, 1, kernel⟩).kernel
      (Function.update ![output, center] (0 : Fin 2) input)) output / primary.weight output) = kernel ![output, center] at hi
  have hu (input : Color) : Function.update ![output, center] (0 : Fin 2) input = ![input, center] := by
    funext slot
    fin_cases slot <;> simp
  simp only [hu] at hi
  field_simp [hprimary output] at hi
  nlinarith [hi]

theorem inverse_mixed_pair_seedOutputMass (primary body : FiniteDist Color)
    (rho : ℝ) (hrho : rho ≠ 0) (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ))
    (bodyChannel : Color → Color → ℝ) (kernel : (Fin 2 → Color) → ℝ)
    (hprimary : ∀ color, primary.weight color ≠ 0) (output : Fin 2 → Color) :
    seedOutputMass primary body (fun input output => rho * LinearMap.toMatrix' operator.toLinearMap output input)
      bodyChannel (inversePrimarySeed primary body rho operator ⟨1, 1, kernel⟩) output =
      ∑ center, primary.weight (output 0) * body.weight center * kernel ![output 0, center] *
        bodyChannel center (output 1) := by
  change seedOutputMass _ _ _ _ ⟨1, 1, _⟩ output = _
  rw [mixed_pair_seedOutputMass, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro center _
  have hi := inverse_mixed_pair_row primary body rho hrho operator kernel hprimary (output 0) center
  change rho * operator.toLinearMap (fun input => primary.weight input *
    (inversePrimarySeed primary body rho operator ⟨1, 1, kernel⟩).kernel ![input, center]) (output 0) = _ at hi
  rw [← LinearMap.toMatrix'_mulVec] at hi
  change rho * (∑ input, LinearMap.toMatrix' operator.toLinearMap (output 0) input *
    (primary.weight input * (inversePrimarySeed primary body rho operator ⟨1, 1, kernel⟩).kernel ![input, center])) = _ at hi
  calc
    _ = (body.weight center * bodyChannel center (output 1)) *
        (rho * ∑ input, LinearMap.toMatrix' operator.toLinearMap (output 0) input *
          (primary.weight input * (inversePrimarySeed primary body rho operator ⟨1, 1, kernel⟩).kernel ![input, center])) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro input _
      simp only [inversePrimarySeed, pow_one]
      ring
    _ = _ := by rw [hi]; ring

end
end AFT.RepresentedPolynomial

set_option maxHeartbeats 1000000

namespace AFT.V7Calibration
open GaussianSource RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem actual_inverse_mixed_pair_outputMass (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (hop : operator.toLinearMap = actualResponse C n) (hrho : v7Activation C n ≠ 0)
    (hp : ∀ color, (actualPrimaryLaw C n beta).weight color ≠ 0)
    (kernel : (Fin 2 → Fin (Parameters.modulus n)) → ℝ)
    (output : Fin 2 → Fin (Parameters.modulus n)) :
    seedOutputMass (actualPrimaryLaw C n beta) (actualBodyLaw C n beta)
      (actualPrimaryChannel C n) (actualBodyChannel n)
      (inversePrimarySeed (actualPrimaryLaw C n beta) (actualBodyLaw C n beta)
        (v7Activation C n) operator ⟨1, 1, kernel⟩) output =
      ∑ center, (actualPrimaryLaw C n beta).weight (output 0) * (actualBodyLaw C n beta).weight center *
        kernel ![output 0, center] * actualBodyChannel n center (output 1) := by
  have hh := inverse_mixed_pair_seedOutputMass (actualPrimaryLaw C n beta) (actualBodyLaw C n beta)
    (v7Activation C n) hrho operator (actualBodyChannel n) kernel hp output
  have hdecision : (fun a b : Fin (Parameters.modulus n) => Classical.propDecidable (a = b)) =
      instDecidableEqFin (Parameters.modulus n) := Subsingleton.elim _ _
  rw [hdecision] at hh
  unfold actualPrimaryChannel
  rw [← hop]
  exact hh

end
end AFT.V7Calibration
