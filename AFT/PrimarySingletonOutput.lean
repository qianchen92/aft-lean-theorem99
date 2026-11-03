import AFT.SafeBodyOutput
import AFT.PrimarySeedInverse

/-! # Exact leading output of each inverse singleton input -/

namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Color : Type*} [Fintype Color]

theorem inversePrimarySeed_bodySingleton (primary body : FiniteDist Color) (rho : ℝ)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (kernel : Color → ℝ) :
    inversePrimarySeed primary body rho operator (bodySingletonInput kernel) = bodySingletonInput kernel := by
  unfold inversePrimarySeed bodySingletonInput
  congr 1
  simp only [primaryCoordinates,List.ofFn_zero,MixedKernel.inputIteration_nil,LinearMap.id_apply,pow_zero,one_smul]

theorem inversePrimarySeed_primarySingleton (primary body : FiniteDist Color) (rho : ℝ)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (kernel : Color → ℝ) :
    inversePrimarySeed primary body rho operator (primarySingletonInput kernel) =
      primarySingletonInput (fun color => rho⁻¹*(operator.symm (fun input => primary.weight input*kernel input) color/primary.weight color)) := by
  unfold inversePrimarySeed primarySingletonInput
  congr 1
  funext word
  simp only [primaryCoordinates,List.ofFn_succ,List.ofFn_zero,
    MixedKernel.inputIteration,MixedKernel.partialInputLinear,inputReference,pow_one,
    Pi.smul_apply,smul_eq_mul]
  change rho⁻¹*(operator.symm (fun input => primary.weight input * kernel ((Function.update word 0 input) 0))
    (word 0)/primary.weight (word 0)) = _
  simp only [Function.update_self,MixedKernel.singletonKernel]

end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open GaussianSource RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section

theorem actualLeadingOutput_inverse_primary (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (hop : operator.toLinearMap = actualResponse C n) (hrho : v7Activation C n ≠ 0)
    (hp : ∀ color, (actualPrimaryLaw C n beta).weight color ≠ 0)
    (profile : Fin (Parameters.modulus n) → ℝ) :
    actualLeadingOutput C n beta
      (MvPolynomial.X (inversePrimarySeed (actualPrimaryLaw C n beta) (actualBodyLaw C n beta)
        (v7Activation C n) operator (primarySingletonInput (fun color => profile color/(actualPrimaryLaw C n beta).weight color)))) =
      ∑ output, MvPolynomial.C (profile output)*MvPolynomial.X output := by
  rw [inversePrimarySeed_primarySingleton,actualLeadingOutput_primary]
  have hrecover : (fun color => (actualPrimaryLaw C n beta).weight color*(profile color/(actualPrimaryLaw C n beta).weight color)) = profile := by
    funext color
    field_simp [hp color]
  rw [hrecover]
  have heq : (fun color => (actualPrimaryLaw C n beta).weight color*((v7Activation C n)⁻¹*
      (operator.symm profile color/(actualPrimaryLaw C n beta).weight color))) =
      (v7Activation C n)⁻¹ • operator.symm profile := by
    funext color
    simp only [Pi.smul_apply,smul_eq_mul]
    field_simp [hp color]
  rw [heq,map_smul,← hop]
  simp only [LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,Pi.smul_apply,smul_eq_mul]
  simp only [← mul_assoc,mul_inv_cancel₀ hrho,one_mul]

end
end AFT.V7Calibration
