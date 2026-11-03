import AFT.ReferenceCoefficientTable
import AFT.FourOutputCounts

/-! # Separating the exact physical linear response from literal higher inputs -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]
local instance referenceHigherSubtypeDecEq (selected : Finset Slot) : DecidableEq selected := Classical.decEq _

def referenceHigherTable (primary reference : FiniteDist Color)
    (mass : (Slot → Color) → ℝ) : Table (InputSeed Color) :=
  ∑ selected ∈ (Finset.univ : Finset (Finset Slot)).filter (fun selected => 2 ≤ selected.card),
    MvPolynomial.X (referenceCoefficientSeed primary reference mass selected)

def physicalFirstProfile (mass : (Slot → Color) → ℝ) (color : Color) : ℝ :=
  ∑ word,mass word*(∑ slot,if word slot=color then 1 else 0)

theorem physicalFirstProfile_form (mass : (Slot → Color) → ℝ) :
    profileForm (physicalFirstProfile mass) =
      ∑ word,MvPolynomial.C (mass word)*∑ slot,MvPolynomial.X (word slot) := by
  simp only [profileForm,LinearMap.coe_mk,AddHom.coe_mk,physicalFirstProfile,map_sum,map_mul,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro word _
  simp only [Finset.mul_sum,Finset.sum_mul,mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro slot _
  simp

theorem referenceCoefficientForm_linear_sum (primary reference : FiniteDist Color)
    (hp : ∀ color,0 < primary.weight color) (mass : (Slot → Color) → ℝ)
    (hmass : (∑ word,mass word)=0) :
    (∑ selected ∈ (Finset.univ : Finset (Finset Slot)).filter (fun selected => selected.card=1),
      referenceCoefficientForm primary reference mass selected) = profileForm (physicalFirstProfile mass) := by
  have heq : (∑ slot : Slot,referenceCoefficientForm primary reference mass {slot}) =
      ∑ selected ∈ (Finset.univ : Finset (Finset Slot)).filter (fun selected => selected.card=1),
        referenceCoefficientForm primary reference mass selected := by
    apply Finset.sum_bij (fun slot _ => ({slot} : Finset Slot))
    · intro slot _; simp
    · intro first _ second _ he; exact Finset.singleton_injective he
    · intro selected hs
      obtain ⟨slot,rfl⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hs).2
      exact ⟨slot,Finset.mem_univ _,rfl⟩
    · intro slot _; rfl
  rw [← heq]
  simp_rw [referenceCoefficientForm_formula primary reference hp]
  have hsingle (slot : Slot) (source : Slot → Color) :
      (∏ index : ({slot} : Finset Slot),(MvPolynomial.X (source index)-profileForm reference.weight)) =
      MvPolynomial.X (source slot)-profileForm reference.weight :=
    Fintype.prod_subsingleton _ (⟨slot,Finset.mem_singleton_self slot⟩ : ({slot} : Finset Slot))
  simp_rw [hsingle]
  rw [Finset.sum_comm]
  simp only [mul_sub,Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_const,nsmul_eq_mul,Finset.card_univ]
  have hc : (∑ source,MvPolynomial.C (mass source)*((Fintype.card Slot : MvPolynomial Color ℝ)*profileForm reference.weight)) = 0 := by
    rw [← Finset.sum_mul,← map_sum,hmass,map_zero,zero_mul]
  rw [hc,sub_zero,physicalFirstProfile_form]

/-- Only the actual linear response is removed; all higher physical
coefficients retain their full joint kernels and literal seed labels. -/
theorem referenceHigherTable_image (primary reference : FiniteDist Color)
    (hp : ∀ color,0 < primary.weight color) (mass : (Slot → Color) → ℝ)
    (hmass : (∑ word,mass word)=0)
    (image : Table (InputSeed Color) →ₐ[ℝ] MvPolynomial Color ℝ)
    (himage : ∀ selected,image (MvPolynomial.X (referenceCoefficientSeed primary reference mass selected)) =
      referenceCoefficientForm primary reference mass selected) :
    image (referenceHigherTable primary reference mass) =
      centeredGeneratingLinear reference.weight mass-profileForm (physicalFirstProfile mass) := by
  unfold referenceHigherTable
  simp_rw [map_sum,himage]
  rw [centeredGeneratingLinear_reference_expansion primary reference hp mass]
  have hsplit : (∑ selected : Finset Slot,referenceCoefficientForm primary reference mass selected) =
      referenceCoefficientForm primary reference mass ∅+
      (∑ selected ∈ (Finset.univ : Finset (Finset Slot)).filter (fun selected => selected.card=1),
        referenceCoefficientForm primary reference mass selected)+
      ∑ selected ∈ (Finset.univ : Finset (Finset Slot)).filter (fun selected => 2 ≤ selected.card),
        referenceCoefficientForm primary reference mass selected := by
    calc
      _ = ∑ selected : Finset Slot,
          ((if selected=∅ then referenceCoefficientForm primary reference mass selected else 0)+
          (if selected.card=1 then referenceCoefficientForm primary reference mass selected else 0)+
          (if 2 ≤ selected.card then referenceCoefficientForm primary reference mass selected else 0)) := by
        apply Finset.sum_congr rfl
        intro selected _
        by_cases he : selected=∅
        · simp [he]
        · have hpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
          by_cases ho : selected.card=1
          · simp [he,ho]
          · simp [he,ho,show 2 ≤ selected.card by omega]
      _ = _ := by simp only [Finset.sum_add_distrib,Finset.sum_filter,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [hsplit,referenceCoefficientForm_empty,hmass,map_zero,zero_add,
    referenceCoefficientForm_linear_sum primary reference hp mass hmass]
  ring

theorem referenceHigherTable_hasOrder (primary reference : FiniteDist Color)
    (mass : (Slot → Color) → ℝ) :
    HasOrder (fun seed : InputSeed Color => seed.primaryOrder+seed.bodyOrder) 2
      (referenceHigherTable primary reference mass) := by
  apply hasOrder_sum
  intro selected hs
  simpa only [map_one,one_mul] using hasOrder_C_mul_X
    (fun seed : InputSeed Color => seed.primaryOrder+seed.bodyOrder) 2
    (referenceCoefficientSeed primary reference mass selected) 1 (by
      simpa only [referenceCoefficientSeed,primaryFiniteSeed,Fintype.card_coe,Nat.add_zero] using (Finset.mem_filter.mp hs).2)


theorem referenceHigherTable_inverse_canonical (primary body reference : FiniteDist Color)
    (rho : ℝ) (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ))
    (hp : ∀ color,0 < primary.weight color)
    (hmass : ∀ profile,(∑ color,operator.symm profile color)=∑ color,profile color)
    (mass : (Slot → Color) → ℝ) :
    InputTableCanonical primary body (inversePrimaryTable primary body rho operator
      (referenceHigherTable primary reference mass)) := by
  unfold referenceHigherTable
  simp only [map_sum,inversePrimaryTable,MvPolynomial.aeval_X]
  apply InputTableCanonical.sum
  intro selected _
  exact InputTableCanonical.X _ (inversePrimarySeed_canonical primary body rho operator _
    (fun color => (hp color).ne') hmass
    (referenceCoefficientSeed_canonical primary body reference hp mass selected))

end
end AFT.RepresentedPolynomial


namespace AFT.V7Calibration
open GaussianSource RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot]

theorem actual_referenceHigherTable_inverse_image (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (hop : operator.toLinearMap=actualResponse C n) (hrho : v7Activation C n ≠ 0)
    (hp : ∀ color,0 < (actualPrimaryLaw C n beta).weight color)
    (mass : (Slot → Fin (Parameters.modulus n)) → ℝ) (hmass : (∑ word,mass word)=0) :
    actualLeadingOutput C n beta
      (inversePrimaryTable (actualPrimaryLaw C n beta) (actualBodyLaw C n beta) (v7Activation C n) operator
        (referenceHigherTable (actualPrimaryLaw C n beta) (actualReferenceLaw C n beta) mass)) =
      centeredGeneratingLinear (actualReferenceLaw C n beta).weight mass-profileForm (physicalFirstProfile mass) := by
  apply referenceHigherTable_image (actualPrimaryLaw C n beta) (actualReferenceLaw C n beta) hp mass hmass
    ((actualLeadingOutput C n beta).comp
      (inversePrimaryTable (actualPrimaryLaw C n beta) (actualBodyLaw C n beta) (v7Activation C n) operator))
  intro selected
  simp only [AlgHom.comp_apply,inversePrimaryTable,MvPolynomial.aeval_X]
  rw [actualLeadingOutput_inverse_joint_primary C n beta operator hop hrho (fun color => (hp color).ne') _ rfl]
  exact referenceCoefficientSeed_form _ _ _ _

end
end AFT.V7Calibration
