import AFT.SeedRoleEquivalence

/-! # Ordered product seeds and the original monomial share one full role equivalence -/
namespace AFT.RepresentedPolynomial
open V7Calibration
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
variable {Color Primary Body OtherPrimary OtherBody : Type*}
  [Fintype Primary] [Fintype Body] [Fintype OtherPrimary] [Fintype OtherBody]

def mixedFiniteSeedRoleEquiv (p : Primary ≃ OtherPrimary) (b : Body ≃ OtherBody)
    (first : (Primary ⊕ Body → Color) → ℝ) (second : (OtherPrimary ⊕ OtherBody → Color) → ℝ)
    (hk : ∀ word,first (word ∘ Equiv.sumCongr p b)=second word) :
    SeedRoleEquiv (mixedFiniteSeed first) (mixedFiniteSeed second) where
  coordinates := mixedFiniteEquiv.symm.trans ((Equiv.sumCongr p b).trans mixedFiniteEquiv)
  role slot := by
    obtain ⟨slot,rfl⟩ := mixedFiniteEquiv.surjective slot
    cases slot <;> simp [mixedFiniteEquiv,inputSeedRole,mixedFiniteSeed]
  kernel word := by
    change first (((word ∘ (mixedFiniteEquiv.symm.trans ((Equiv.sumCongr p b).trans mixedFiniteEquiv))) ∘ mixedFiniteEquiv))=
      second (word ∘ mixedFiniteEquiv)
    rw [←hk (word ∘ mixedFiniteEquiv)]
    congr 1
    funext slot
    simp

/-- The product-coordinate bijection from an occurrence permutation induces
an equivalence of the actual single joint input seeds. -/
def mixedProductSeedRoleEquiv {first second : List (InputSeed Color)} (h : first.Perm second) :
    SeedRoleEquiv (mixedProductSeed first) (mixedProductSeed second) := by
  let e := Classical.choose (controlProduct_permutation h)
  have hr := (Classical.choose_spec (controlProduct_permutation h)).1
  have hk := (Classical.choose_spec (controlProduct_permutation h)).2
  let ep : ControlPrimarySlot first ≃ ControlPrimarySlot second :=
    Equiv.subtypeEquiv e (fun slot => by rw [hr])
  let eb : ControlBodySlot first ≃ ControlBodySlot second :=
    Equiv.subtypeEquiv e (fun slot => by rw [hr])
  have hpool (slot : ControlPrimarySlot first ⊕ ControlBodySlot first) :
      controlPoolEquiv second (Equiv.sumCongr ep eb slot)=e (controlPoolEquiv first slot) := by
    cases slot <;> rfl
  apply mixedFiniteSeedRoleEquiv ep eb (twoPoolControlKernel first) (twoPoolControlKernel second)
  intro word
  unfold twoPoolControlKernel
  rw [←hk (word ∘ (controlPoolEquiv second).symm)]
  congr 1
  funext slot
  change word (Equiv.sumCongr ep eb ((controlPoolEquiv first).symm slot))=
    word ((controlPoolEquiv second).symm (e slot))
  apply congrArg word
  apply (controlPoolEquiv second).injective
  rw [hpool,Equiv.apply_symm_apply,Equiv.apply_symm_apply]

/-- No equality test or sorting of decoded real kernels is performed by the
runtime list. Its semantic monomial has this exact coordinate equivalence. -/
def orderedProductMonomialRoleEquiv {Code : Type*} (decode : Code → InputSeed Color) (factors : List Code) :
    SeedRoleEquiv (mixedProductSeed (factors.map decode))
      (mixedMonomialSeed (RationalNumerics.orderedSeedPowers decode factors)) :=
  mixedProductSeedRoleEquiv (orderedSeedPowers_occurrences decode factors)

end
end AFT.RepresentedPolynomial
