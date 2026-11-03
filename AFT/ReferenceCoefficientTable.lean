import AFT.ReferenceCoefficientPolynomial
import AFT.PrimaryFiniteSeed
import AFT.RepresentedCanonical

/-! # Every actual finite signed PGF has a literal canonical input table -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]
local instance referenceTableSubtypeDecEq (selected : Finset Slot) : DecidableEq selected := Classical.decEq _

def referenceCoefficientSeed (primary reference : FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (selected : Finset Slot) : InputSeed Color :=
  primaryFiniteSeed (LocalTensors.referenceRestrictedComponent (fun _ : Slot => primary)
    (fun _ : Slot => reference) mass selected)

/-- Keep every nonconstant selected coefficient as a separate literal seed. -/
def referenceCoefficientTable (primary reference : FiniteDist Color)
    (mass : (Slot → Color) → ℝ) : Table (InputSeed Color) :=
  ∑ selected ∈ (Finset.univ : Finset (Finset Slot)).erase ∅,
    MvPolynomial.X (referenceCoefficientSeed primary reference mass selected)

theorem referenceCoefficientSeed_weight (primary body reference : FiniteDist Color)
    (primaryPool bodyPool radius : ℝ) (mass : (Slot → Color) → ℝ) (selected : Finset Slot) :
    inputWeight primary body primaryPool bodyPool radius (referenceCoefficientSeed primary reference mass selected) =
      MixedKernel.activity (fun _ : selected => (Real.sqrt primaryPool)⁻¹) (fun _ : selected => primary)
        (LocalTensors.referenceRestrictedComponent (fun _ : Slot => primary)
          (fun _ : Slot => reference) mass selected) := primaryFiniteSeed_weight _ _ _ _ _ _

theorem referenceCoefficientSeed_form (primary reference : FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (selected : Finset Slot) :
    jointPrimaryForm primary (referenceCoefficientSeed primary reference mass selected) =
      referenceCoefficientForm primary reference mass selected := primaryFiniteSeed_form _ _

theorem referenceCoefficientSeed_canonical (primary body reference : FiniteDist Color)
    (hp : ∀ color,0 < primary.weight color) (mass : (Slot → Color) → ℝ) (selected : Finset Slot) :
    Hoeffding.Canonical (inputReference primary body (referenceCoefficientSeed primary reference mass selected))
      Finset.univ (referenceCoefficientSeed primary reference mass selected).kernel :=
  primaryFiniteSeed_canonical _ _ _ (LocalTensors.referenceRestrictedComponent_canonical _ _ (fun _ => hp) _ _)

theorem referenceCoefficientTable_canonical (primary body reference : FiniteDist Color)
    (hp : ∀ color,0 < primary.weight color) (mass : (Slot → Color) → ℝ) :
    InputTableCanonical primary body (referenceCoefficientTable primary reference mass) :=
  InputTableCanonical.sum _ _ fun selected _ =>
    InputTableCanonical.X _ (referenceCoefficientSeed_canonical primary body reference hp mass selected)

theorem referenceCoefficientTable_hasOrder (primary reference : FiniteDist Color)
    (mass : (Slot → Color) → ℝ) :
    HasOrder (fun seed : InputSeed Color => seed.primaryOrder+seed.bodyOrder) 1
      (referenceCoefficientTable primary reference mass) := by
  apply hasOrder_sum
  intro selected hs
  have hcard : 1 ≤ selected.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hs).1)
  simpa only [map_one,one_mul] using hasOrder_C_mul_X
    (fun seed : InputSeed Color => seed.primaryOrder+seed.bodyOrder) 1
    (referenceCoefficientSeed primary reference mass selected) 1 (by
      simpa only [referenceCoefficientSeed,primaryFiniteSeed,Fintype.card_coe,Nat.add_zero] using hcard)

/-- An exact image for each actual selected joint coefficient reconstructs
the full physical PGF, not just an abstract polynomial with matching degree. -/
theorem referenceCoefficientTable_image (primary reference : FiniteDist Color)
    (hp : ∀ color,0 < primary.weight color) (mass : (Slot → Color) → ℝ)
    (image : Table (InputSeed Color) →ₐ[ℝ] MvPolynomial Color ℝ)
    (himage : ∀ selected,image (MvPolynomial.X (referenceCoefficientSeed primary reference mass selected)) =
      referenceCoefficientForm primary reference mass selected) :
    image (referenceCoefficientTable primary reference mass) =
      centeredGeneratingLinear reference.weight mass-MvPolynomial.C (∑ word,mass word) := by
  unfold referenceCoefficientTable
  simp_rw [map_sum,himage]
  rw [centeredGeneratingLinear_reference_expansion primary reference hp mass]
  have hh := Finset.sum_erase_add (Finset.univ : Finset (Finset Slot))
    (referenceCoefficientForm primary reference mass) (Finset.mem_univ ∅)
  rw [referenceCoefficientForm_empty] at hh
  apply eq_sub_iff_add_eq.mpr
  simpa only [map_sum] using hh


theorem referenceCoefficientTable_inverse_canonical (primary body reference : FiniteDist Color)
    (rho : ℝ) (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ))
    (hp : ∀ color,0 < primary.weight color)
    (hmass : ∀ profile,(∑ color,operator.symm profile color)=∑ color,profile color)
    (mass : (Slot → Color) → ℝ) :
    InputTableCanonical primary body (inversePrimaryTable primary body rho operator
      (referenceCoefficientTable primary reference mass)) := by
  unfold referenceCoefficientTable
  simp only [map_sum,inversePrimaryTable,MvPolynomial.aeval_X]
  apply InputTableCanonical.sum
  intro selected _
  exact InputTableCanonical.X _ (inversePrimarySeed_canonical primary body rho operator _
    (fun color => (hp color).ne') hmass
    (referenceCoefficientSeed_canonical primary body reference hp mass selected))

theorem referenceCoefficientTable_inverse_activity_le (primary body reference : FiniteDist Color)
    (primaryPool bodyPool radius rho : ℝ) (hradius : 0 ≤ radius)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (mass : (Slot → Color) → ℝ)
    (bound : Finset Slot → ℝ)
    (hbound : ∀ selected,selected ≠ ∅ →
      inputWeight primary body primaryPool bodyPool radius
        (inversePrimarySeed primary body rho operator (referenceCoefficientSeed primary reference mass selected)) ≤ bound selected) :
    activity (inputWeight primary body primaryPool bodyPool radius)
      (inversePrimaryTable primary body rho operator (referenceCoefficientTable primary reference mass)) ≤
        ∑ selected ∈ (Finset.univ : Finset (Finset Slot)).erase ∅,bound selected := by
  unfold referenceCoefficientTable
  simp only [map_sum,inversePrimaryTable,MvPolynomial.aeval_X]
  apply (activity_sum_le _ (fun seed => inputWeight_nonneg _ _ _ _ _ seed hradius) _ _).trans
  apply Finset.sum_le_sum
  intro selected hs
  rw [activity_X]
  exact hbound selected (Finset.mem_erase.mp hs).1

end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open RepresentedPolynomial GaussianSource
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot]

/-- The same actual calibrated inverse sends the literal finite table of
an arbitrary signed local mass to its complete centered physical PGF. -/
theorem actual_referenceCoefficientTable_inverse_image (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (hop : operator.toLinearMap=actualResponse C n) (hrho : v7Activation C n ≠ 0)
    (hp : ∀ color,0 < (actualPrimaryLaw C n beta).weight color)
    (mass : (Slot → Fin (Parameters.modulus n)) → ℝ) :
    actualLeadingOutput C n beta
      (inversePrimaryTable (actualPrimaryLaw C n beta) (actualBodyLaw C n beta) (v7Activation C n) operator
        (referenceCoefficientTable (actualPrimaryLaw C n beta) (actualReferenceLaw C n beta) mass)) =
      centeredGeneratingLinear (actualReferenceLaw C n beta).weight mass-MvPolynomial.C (∑ word,mass word) := by
  apply referenceCoefficientTable_image (actualPrimaryLaw C n beta) (actualReferenceLaw C n beta) hp mass
    ((actualLeadingOutput C n beta).comp
      (inversePrimaryTable (actualPrimaryLaw C n beta) (actualBodyLaw C n beta) (v7Activation C n) operator))
  intro selected
  simp only [AlgHom.comp_apply,inversePrimaryTable,MvPolynomial.aeval_X]
  rw [actualLeadingOutput_inverse_joint_primary C n beta operator hop hrho (fun color => (hp color).ne') _ rfl]
  exact referenceCoefficientSeed_form _ _ _ _

end
end AFT.V7Calibration
