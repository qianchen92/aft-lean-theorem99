import AFT.ReferenceCoefficientTable

/-! # Literal finite quotients of actual local physical generating laws -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

def referenceInverseTable (primary body reference : FiniteDist Color) (rho : ℝ)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (mass : (Slot → Color) → ℝ) : Table (InputSeed Color) :=
  inversePrimaryTable primary body rho operator (referenceCoefficientTable primary reference mass)

def referenceQuotientTable (primary body reference : FiniteDist Color) (rho : ℝ)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ))
    (numerator denominator : (Slot → Color) → ℝ) (depth : ℕ) : Table (InputSeed Color) :=
  referenceInverseTable primary body reference rho operator numerator *
    finiteCorrection (referenceInverseTable primary body reference rho operator denominator) depth

theorem referenceInverseTable_hasOrder (primary body reference : FiniteDist Color) (rho : ℝ)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (mass : (Slot → Color) → ℝ) :
    HasOrder (fun seed : InputSeed Color => seed.primaryOrder+seed.bodyOrder) 1
      (referenceInverseTable primary body reference rho operator mass) :=
  inversePrimaryTable_hasOrder _ _ _ _ _ _ (referenceCoefficientTable_hasOrder _ _ _)

theorem referenceQuotientTable_canonical (primary body reference : FiniteDist Color) (rho : ℝ)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ))
    (hp : ∀ color,0 < primary.weight color)
    (hmass : ∀ profile,(∑ color,operator.symm profile color)=∑ color,profile color)
    (numerator denominator : (Slot → Color) → ℝ) (depth : ℕ) :
    InputTableCanonical primary body (referenceQuotientTable primary body reference rho operator numerator denominator depth) :=
  (referenceCoefficientTable_inverse_canonical primary body reference rho operator hp hmass numerator).mul
    ((referenceCoefficientTable_inverse_canonical primary body reference rho operator hp hmass denominator).finiteCorrection depth)

theorem referenceQuotientTable_hasOrder (primary body reference : FiniteDist Color) (rho : ℝ)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ))
    (numerator denominator : (Slot → Color) → ℝ) (depth : ℕ) :
    HasOrder (fun seed : InputSeed Color => seed.primaryOrder+seed.bodyOrder) 1
      (referenceQuotientTable primary body reference rho operator numerator denominator depth) := by
  exact hasOrder_mul _ 1 0 _ _ (referenceInverseTable_hasOrder _ _ _ _ _ _) (hasOrder_zero _ _)

/-- The quotient is a finite polynomial on actual canonical inputs; its
activity uses no convergence of an infinite formal inverse. -/
theorem referenceQuotientTable_activity_le (primary body reference : FiniteDist Color)
    (primaryPool bodyPool radius rho : ℝ) (hradius : 0 ≤ radius)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ))
    (numerator denominator : (Slot → Color) → ℝ) (depth : ℕ)
    (hsmall : activity (inputWeight primary body primaryPool bodyPool radius)
      (referenceInverseTable primary body reference rho operator denominator) ≤ 1/2) :
    activity (inputWeight primary body primaryPool bodyPool radius)
      (referenceQuotientTable primary body reference rho operator numerator denominator depth) ≤
      2*activity (inputWeight primary body primaryPool bodyPool radius)
        (referenceInverseTable primary body reference rho operator numerator) := by
  apply (activity_mul_le _ (fun seed => inputWeight_nonneg _ _ _ _ _ seed hradius) _ _).trans
  exact (mul_le_mul_of_nonneg_left (activity_finiteCorrection_le_two _
    (fun seed => inputWeight_nonneg _ _ _ _ _ seed hradius) _ depth hsmall)
    (activity_nonneg _ (fun seed => inputWeight_nonneg _ _ _ _ _ seed hradius) _)).trans_eq (by ring)

end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open GaussianSource RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot]

/-- The actual leading image is the literal finite quotient of the physical
numerator and positive denominator, with their genuine total masses. -/
theorem actual_referenceQuotientTable_image (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (hop : operator.toLinearMap=actualResponse C n) (hrho : v7Activation C n ≠ 0)
    (hp : ∀ color,0 < (actualPrimaryLaw C n beta).weight color)
    (numerator denominator : (Slot → Fin (Parameters.modulus n)) → ℝ)
    (hn : (∑ word,numerator word)=0) (hd : (∑ word,denominator word)=1) (depth : ℕ) :
    actualLeadingOutput C n beta
      (referenceQuotientTable (actualPrimaryLaw C n beta) (actualBodyLaw C n beta)
        (actualReferenceLaw C n beta) (v7Activation C n) operator numerator denominator depth) =
      centeredGeneratingLinear (actualReferenceLaw C n beta).weight numerator *
        finiteCorrection (centeredGeneratingLinear (actualReferenceLaw C n beta).weight denominator-1) depth := by
  have hnum := actual_referenceCoefficientTable_inverse_image C n beta operator hop hrho hp numerator
  have hden := actual_referenceCoefficientTable_inverse_image C n beta operator hop hrho hp denominator
  rw [hn,map_zero,sub_zero] at hnum
  rw [hd,map_one] at hden
  unfold referenceQuotientTable referenceInverseTable
  rw [map_mul,hnum]
  congr 1
  simp only [finiteCorrection,map_sum,map_pow,map_neg,hden]

/-- Multiplying the finite quotient by its true denominator leaves exactly
the next-order power, so every coefficient through the cutoff is exact. -/
theorem actual_referenceQuotientTable_residual (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (hop : operator.toLinearMap=actualResponse C n) (hrho : v7Activation C n ≠ 0)
    (hp : ∀ color,0 < (actualPrimaryLaw C n beta).weight color)
    (numerator denominator : (Slot → Fin (Parameters.modulus n)) → ℝ)
    (hn : (∑ word,numerator word)=0) (hd : (∑ word,denominator word)=1) (depth : ℕ) :
    truncate (fun _ : Fin (Parameters.modulus n) => 1) depth
      (actualLeadingOutput C n beta
        (referenceQuotientTable (actualPrimaryLaw C n beta) (actualBodyLaw C n beta)
          (actualReferenceLaw C n beta) (v7Activation C n) operator numerator denominator depth)*
        centeredGeneratingLinear (actualReferenceLaw C n beta).weight denominator) =
      truncate (fun _ : Fin (Parameters.modulus n) => 1) depth
        (centeredGeneratingLinear (actualReferenceLaw C n beta).weight numerator) := by
  let error := referenceInverseTable (actualPrimaryLaw C n beta) (actualBodyLaw C n beta)
    (actualReferenceLaw C n beta) (v7Activation C n) operator denominator
  have he := referenceInverseTable_hasOrder (actualPrimaryLaw C n beta) (actualBodyLaw C n beta)
    (actualReferenceLaw C n beta) (v7Activation C n) operator denominator
  have hden := actual_referenceCoefficientTable_inverse_image C n beta operator hop hrho hp denominator
  rw [hd,map_one] at hden
  have hout : HasOrder (fun _ : Fin (Parameters.modulus n) => 1) 1
      (centeredGeneratingLinear (actualReferenceLaw C n beta).weight denominator-1) := by
    rw [← hden]
    exact outputHom_hasOrder _ _ _ _ _ _ he
  have hidentity := truncate_finiteCorrection_residual (fun _ : Fin (Parameters.modulus n) => 1) depth _ hout
  simp only [add_sub_cancel] at hidentity
  rw [actual_referenceQuotientTable_image C n beta operator hop hrho hp numerator denominator hn hd depth]
  rw [mul_assoc,mul_comm (finiteCorrection _ _) _,truncate_mul,
    hidentity, mul_one,truncate_idempotent]

end
end AFT.V7Calibration
