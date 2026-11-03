import AFT.OrderedJointKernel
import AFT.MixedSeedRoleEquivalence

/-! # Explicit ordered coordinates agree with the original monomial roles -/
namespace AFT.RationalNumerics
open RepresentedPolynomial V7Calibration
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 450000
variable {Leaf Color : Type*}

def orderedControlIndex (shape : Leaf → KernelShape)
    (value : (label : Leaf) → (Fin ((shape label).primary+(shape label).body) → Color) → ℝ) :
    (factors : List Leaf) → ControlProductSlot (factors.map (fun label => shapeSeed (shape label) (value label))) ≃
      Fin ((orderedJointShape shape factors).primary+(orderedJointShape shape factors).body)
  | [] => show PEmpty ≃ Fin 0 from Equiv.equivOfIsEmpty _ _
  | label::rest =>
    (Equiv.sumCongr (Equiv.refl _) (orderedControlIndex shape value rest)).trans
      (joinedKernelIndex (shape label) (orderedJointShape shape rest))

theorem joinedKernelIndex_role (first second : KernelShape) :
    (fun slot => Fin.addCases (fun _ : Fin (first.primary+second.primary) => true)
      (fun _ : Fin (first.body+second.body) => false) (joinedKernelIndex first second slot))=
    Sum.elim (Fin.addCases (fun _ : Fin first.primary => true) (fun _ : Fin first.body => false))
      (Fin.addCases (fun _ : Fin second.primary => true) (fun _ : Fin second.body => false)) := by
  funext slot
  rcases slot with slot|slot
  · cases slot using Fin.addCases <;> simp [joinedKernelIndex,Equiv.sumSumSumComm,KernelShape.join]
  · cases slot using Fin.addCases <;> simp [joinedKernelIndex,Equiv.sumSumSumComm,KernelShape.join]

theorem orderedControlIndex_role (shape : Leaf → KernelShape)
    (value : (label : Leaf) → (Fin ((shape label).primary+(shape label).body) → Color) → ℝ)
    (factors : List Leaf) (slot) :
    inputSeedRole (orderedJointSeed shape value factors) (orderedControlIndex shape value factors slot)=
      controlProductRole (factors.map (fun label => shapeSeed (shape label) (value label))) slot := by
  induction factors with
  | nil => exact PEmpty.elim slot
  | cons label rest ih =>
    change Fin.addCases (motive := fun _ => Bool) (fun _ : Fin ((shape label).primary+(orderedJointShape shape rest).primary) => true)
      (fun _ : Fin ((shape label).body+(orderedJointShape shape rest).body) => false)
      (joinedKernelIndex (shape label) (orderedJointShape shape rest)
        (Equiv.sumCongr (Equiv.refl _) (orderedControlIndex shape value rest) slot))=_
    rw [congrFun (joinedKernelIndex_role _ _) (Equiv.sumCongr (Equiv.refl _) (orderedControlIndex shape value rest) slot)]
    change Fin ((shape label).primary+(shape label).body) ⊕
      ControlProductSlot (rest.map (fun label => shapeSeed (shape label) (value label))) at slot
    cases slot with
    | inl slot => rfl
    | inr slot => exact ih slot

theorem orderedControlIndex_kernel (shape : Leaf → KernelShape)
    (value : (label : Leaf) → (Fin ((shape label).primary+(shape label).body) → Color) → ℝ)
    (factors : List Leaf) (word) :
    controlProductKernel (factors.map (fun label => shapeSeed (shape label) (value label)))
      (word ∘ orderedControlIndex shape value factors)=orderedJointKernel shape value factors word := by
  induction factors with
  | nil => rfl
  | cons label rest ih =>
    change value label (fun slot => word (joinedKernelIndex _ _ (Sum.inl slot))) *
      controlProductKernel (rest.map (fun label => shapeSeed (shape label) (value label)))
        (fun slot => word (joinedKernelIndex _ _ (Sum.inr (orderedControlIndex shape value rest slot))))=_
    rw [show (fun slot => word (joinedKernelIndex (shape label) (orderedJointShape shape rest)
      (Sum.inr (orderedControlIndex shape value rest slot))))=
      (fun slot => word (joinedKernelIndex (shape label) (orderedJointShape shape rest) (Sum.inr slot))) ∘
        orderedControlIndex shape value rest from rfl,ih]
    rfl

def orderedJointProductRoleEquiv (shape : Leaf → KernelShape)
    (value : (label : Leaf) → (Fin ((shape label).primary+(shape label).body) → Color) → ℝ)
    (factors : List Leaf) :
    SeedRoleEquiv (orderedJointSeed shape value factors)
      (mixedProductSeed (factors.map (fun label => shapeSeed (shape label) (value label)))) where
  coordinates := (orderedControlIndex shape value factors).symm.trans
    ((controlPoolEquiv (factors.map (fun label => shapeSeed (shape label) (value label)))).symm.trans mixedFiniteEquiv)
  role slot := by
    let seeds := factors.map (fun label => shapeSeed (shape label) (value label))
    obtain ⟨old,rfl⟩ := (orderedControlIndex shape value factors).surjective slot
    simp only [Equiv.trans_apply]
    erw [(orderedControlIndex shape value factors).symm_apply_apply old]
    rw [orderedControlIndex_role]
    obtain ⟨old,rfl⟩ := (controlPoolEquiv seeds).surjective old
    change inputSeedRole (mixedFiniteSeed (twoPoolControlKernel seeds))
      (mixedFiniteEquiv ((controlPoolEquiv seeds).symm (controlPoolEquiv seeds old)))=
      controlProductRole seeds (controlPoolEquiv seeds old)
    rw [Equiv.symm_apply_apply]
    cases old with
    | inl old => simp [mixedFiniteSeed,mixedFiniteEquiv,inputSeedRole,controlPoolEquiv,old.property]
    | inr old => simp [mixedFiniteSeed,mixedFiniteEquiv,inputSeedRole,controlPoolEquiv,old.property]
  kernel word := by
    rw [show (orderedJointSeed shape value factors).kernel=orderedJointKernel shape value factors from rfl,
      ←orderedControlIndex_kernel shape value factors]
    change controlProductKernel _ _=controlProductKernel _ _
    congr 1
    funext slot
    simp only [Function.comp_apply,Equiv.trans_apply]
    exact congrArg (fun item => word (mixedFiniteEquiv ((controlPoolEquiv _).symm item)))
      ((orderedControlIndex shape value factors).symm_apply_apply slot)

def orderedJointMonomialRoleEquiv (shape : Leaf → KernelShape)
    (value : (label : Leaf) → (Fin ((shape label).primary+(shape label).body) → Color) → ℝ)
    (factors : List Leaf) :
    SeedRoleEquiv (orderedJointSeed shape value factors)
      (mixedMonomialSeed (orderedSeedPowers (fun label => shapeSeed (shape label) (value label)) factors)) :=
  (orderedJointProductRoleEquiv shape value factors).trans
    (orderedProductMonomialRoleEquiv (fun label => shapeSeed (shape label) (value label)) factors)

end
end AFT.RationalNumerics
