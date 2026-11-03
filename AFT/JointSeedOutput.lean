import AFT.MixedCoordinateProducts
import AFT.PrimarySeedInverse
import AFT.ActualLeadingOutput

/-! # Exact joint leading outputs of the literal primary inverse seeds -/

namespace AFT.RepresentedPolynomial

open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Color : Type*} [Fintype Color]

omit [Fintype Color] in
theorem primaryCoordinates_nodup (seed : InputSeed Color) : (primaryCoordinates seed).Nodup := by
  apply List.nodup_ofFn.mpr
  intro first second heq
  exact Fin.ext (congrArg (fun index : Fin (seed.primaryOrder + seed.bodyOrder) => index.val) heq)

omit [Fintype Color] in
theorem primaryCoordinates_complete (seed : InputSeed Color) (hbody : seed.bodyOrder = 0)
    (slot : Fin (seed.primaryOrder + seed.bodyOrder)) : slot ∈ primaryCoordinates seed := by
  rcases seed with ⟨order, bodyOrder, kernel⟩
  cases hbody
  apply List.mem_ofFn.mpr
  exact ⟨slot, Fin.ext rfl⟩

theorem all_primary_reference (primary body : FiniteDist Color) (seed : InputSeed Color)
    (hbody : seed.bodyOrder = 0) (slot : Fin (seed.primaryOrder + seed.bodyOrder)) :
    inputReference primary body seed slot = primary :=
  primaryCoordinates_reference primary body seed slot (primaryCoordinates_complete seed hbody slot)

omit [Fintype Color] in
theorem all_primary_channel (primaryChannel bodyChannel : Color → Color → ℝ) (seed : InputSeed Color)
    (hbody : seed.bodyOrder = 0) (slot : Fin (seed.primaryOrder + seed.bodyOrder)) :
    seedChannel primaryChannel bodyChannel seed slot = primaryChannel := by
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp (primaryCoordinates_complete seed hbody slot)
  simp only [seedChannel, Fin.addCases_left]

/-- A general full joint kernel, rather than a rank-one proxy, passes through
the actual product of calibrated profile channels. -/
theorem primary_seedOutputMass_iteration (primary body : FiniteDist Color)
    (rho : ℝ) (operator : Module.End ℝ (Color → ℝ)) (bodyChannel : Color → Color → ℝ)
    (seed : InputSeed Color) (hbody : seed.bodyOrder = 0)
    (hprimary : ∀ color, primary.weight color ≠ 0)
    (output : Fin (seed.primaryOrder + seed.bodyOrder) → Color) :
    seedOutputMass primary body (fun input output => rho * LinearMap.toMatrix' operator output input)
      bodyChannel seed output =
      rho ^ seed.primaryOrder * (∏ slot, primary.weight (output slot)) *
        MixedKernel.inputIteration (primaryCoordinates seed).reverse (fun _ => operator)
          (inputReference primary body seed) seed.kernel output := by
  have hm := MixedKernel.weighted_inputIteration_matrix (primaryCoordinates seed).reverse
    (by simpa only [List.nodup_reverse] using primaryCoordinates_nodup seed)
    (fun slot => List.mem_reverse.mpr (primaryCoordinates_complete seed hbody slot))
    (fun _ => operator) (inputReference primary body seed)
    (fun slot color => by rw [all_primary_reference primary body seed hbody slot]; exact hprimary color)
    seed.kernel output
  simp only [all_primary_reference primary body seed hbody] at hm
  rw [mul_assoc, hm, Finset.mul_sum]
  unfold seedOutputMass
  simp only [all_primary_reference primary body seed hbody,
    all_primary_channel _ _ seed hbody, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, hbody, Nat.add_zero]
  apply Finset.sum_congr rfl
  intro point _
  ring

/-- The actual inverse seed recovers precisely the full original signed
joint input mass after every primary channel, including all activation factors. -/
theorem inverse_primary_seedOutputMass (primary body : FiniteDist Color)
    (rho : ℝ) (hrho : rho ≠ 0) (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ))
    (bodyChannel : Color → Color → ℝ) (seed : InputSeed Color) (hbody : seed.bodyOrder = 0)
    (hprimary : ∀ color, primary.weight color ≠ 0)
    (output : Fin (seed.primaryOrder + seed.bodyOrder) → Color) :
    seedOutputMass primary body (fun input output => rho * LinearMap.toMatrix' operator.toLinearMap output input)
      bodyChannel (inversePrimarySeed primary body rho operator seed) output =
      seed.kernel output * ∏ slot, primary.weight (output slot) := by
  rw [primary_seedOutputMass_iteration primary body rho operator.toLinearMap bodyChannel
    (inversePrimarySeed primary body rho operator seed) hbody hprimary]
  have hi := congrFun (inversePrimarySeed_exact primary body rho hrho operator seed hprimary) output
  simp only [Pi.smul_apply, smul_eq_mul] at hi
  change rho ^ seed.primaryOrder * (∏ slot, primary.weight (output slot)) *
    MixedKernel.inputIteration (primaryCoordinates seed).reverse (fun _ => operator.toLinearMap)
      (inputReference primary body seed) (inversePrimarySeed primary body rho operator seed).kernel output = _
  calc
    _ = (∏ slot, primary.weight (output slot)) *
      (rho ^ seed.primaryOrder * MixedKernel.inputIteration (primaryCoordinates seed).reverse
        (fun _ => operator.toLinearMap) (inputReference primary body seed)
        (inversePrimarySeed primary body rho operator seed).kernel output) := by ring
    _ = _ := by rw [hi]; ring

end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration

open GaussianSource RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem actualLeadingOutput_inverse_joint_primary (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (hop : operator.toLinearMap = actualResponse C n) (hrho : v7Activation C n ≠ 0)
    (hp : ∀ color, (actualPrimaryLaw C n beta).weight color ≠ 0)
    (seed : InputSeed (Fin (Parameters.modulus n))) (hbody : seed.bodyOrder = 0) :
    actualLeadingOutput C n beta
      (MvPolynomial.X (inversePrimarySeed (actualPrimaryLaw C n beta) (actualBodyLaw C n beta)
        (v7Activation C n) operator seed)) =
      ∑ output : Fin (seed.primaryOrder + seed.bodyOrder) → Fin (Parameters.modulus n),
        MvPolynomial.C (seed.kernel output * ∏ slot, (actualPrimaryLaw C n beta).weight (output slot)) *
          ∏ slot, MvPolynomial.X (output slot) := by
  rw [actualLeadingOutput, outputHom_X, seedOutput_eq_mass]
  apply Finset.sum_congr rfl
  intro output _
  congr 2
  have hh := inverse_primary_seedOutputMass (actualPrimaryLaw C n beta) (actualBodyLaw C n beta)
    (v7Activation C n) hrho operator (actualBodyChannel n) seed hbody hp output
  have hdecision : (fun a b : Fin (Parameters.modulus n) => Classical.propDecidable (a = b)) =
      instDecidableEqFin (Parameters.modulus n) := Subsingleton.elim _ _
  rw [hdecision] at hh
  change seedOutputMass _ _ (fun input output => v7Activation C n *
    LinearMap.toMatrix' (actualResponse C n) output input) _ _ output = _
  rw [← hop]
  exact hh

end
end AFT.V7Calibration
