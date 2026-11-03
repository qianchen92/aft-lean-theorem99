import CurrentAFT.GroupedKernelNorm

/-! # Canonical mixed fibers of arbitrary joint grouped tensor channels -/

namespace CurrentAFT.GroupedKernelNorm
open AFT ControlCoordinates ControlProduct ControlNorm
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
local instance canonicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} :
    DecidableEq (Sigma Slots) := Classical.decEq _
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

variable {Group Primary Body : Type*} [Fintype Group] [Fintype Primary] [Fintype Body]
  (PrimarySlots BodySlots : Group → Type*)
  [∀ group, Fintype (PrimarySlots group)] [∀ group, Fintype (BodySlots group)]
  {Input : Group → Type*} [∀ group, Fintype (Input group)]

private theorem sigma_update_same {Index Color : Type*} {Slots : Index → Type*}
    (word : Sigma Slots → Color) (group : Index) (slot : Slots group) (color : Color) :
    (fun part : Slots group => Function.update word ⟨group, slot⟩ color ⟨group, part⟩) =
      Function.update (fun part : Slots group => word ⟨group, part⟩) slot color := by
  funext part
  by_cases hequal : part = slot
  · subst part; simp
  · simp only [Function.update_of_ne hequal, Function.update_of_ne (show
      (⟨group, part⟩ : Sigma Slots) ≠ ⟨group, slot⟩ from fun h =>
        hequal (eq_of_heq (Sigma.mk.inj_iff.mp h).2))]

private theorem sigma_update_other {Index Color : Type*} {Slots : Index → Type*}
    (word : Sigma Slots → Color) (group other : Index) (hne : other ≠ group)
    (slot : Slots group) (color : Color) :
    (fun part : Slots other => Function.update word ⟨group, slot⟩ color ⟨other, part⟩) =
      (fun part : Slots other => word ⟨other, part⟩) := by
  funext part
  apply Function.update_of_ne
  intro hequal
  exact hne (congrArg Sigma.fst hequal)

omit [Fintype Body] [∀ group, Fintype (PrimarySlots group)]
  [∀ group, Fintype (BodySlots group)] in
theorem flatten_tensor_primaryCentered (primary : FiniteDist Primary)
    (channel : ∀ group, (Input group → ℝ) →ₗ[ℝ]
      (((PrimarySlots group → Primary) × (BodySlots group → Body)) → ℝ))
    (hcentered : ∀ group score, PrimaryCentered primary
      (fun colors centers => channel group score (colors, centers)))
    (kernel : ((group : Group) → Input group) → ℝ) :
    PrimaryCentered primary
      (flatten PrimarySlots BodySlots (DependentTensorChannel.apply channel kernel)) := by
  intro selected colors centers
  rcases selected with ⟨group, slot⟩
  simp only [flatten, wordEquiv, Equiv.coe_fn_mk, DependentTensorChannel.apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro inputs _
  have hprod (color : Primary) :
      (∏ other, channel other (Pi.single (inputs other) 1)
        ((fun part => Function.update colors ⟨group, slot⟩ color ⟨other, part⟩),
          (fun part => centers ⟨other, part⟩))) =
      channel group (Pi.single (inputs group) 1)
        (Function.update (fun part => colors ⟨group, part⟩) slot color,
          fun part => centers ⟨group, part⟩) *
      ∏ other ∈ (Finset.univ : Finset Group).erase group,
        channel other (Pi.single (inputs other) 1)
          ((fun part => colors ⟨other, part⟩), (fun part => centers ⟨other, part⟩)) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ group), sigma_update_same]
    congr 1
    apply Finset.prod_congr rfl
    intro other hother
    rw [sigma_update_other colors group other (Finset.mem_erase.mp hother).1 slot color]
  simp only [hprod]
  calc
    _ = (kernel inputs * ∏ other ∈ (Finset.univ : Finset Group).erase group,
        channel other (Pi.single (inputs other) 1)
          ((fun part => colors ⟨other, part⟩), (fun part => centers ⟨other, part⟩))) *
        ∑ color, primary.weight color * channel group (Pi.single (inputs group) 1)
          (Function.update (fun part => colors ⟨group, part⟩) slot color,
            fun part => centers ⟨group, part⟩) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro color _
      ring
    _ = 0 := by rw [hcentered group (Pi.single (inputs group) 1) slot, mul_zero]

omit [Fintype Primary] [∀ group, Fintype (PrimarySlots group)]
  [∀ group, Fintype (BodySlots group)] in
theorem flatten_tensor_bodyCentered (body : FiniteDist Body)
    (channel : ∀ group, (Input group → ℝ) →ₗ[ℝ]
      (((PrimarySlots group → Primary) × (BodySlots group → Body)) → ℝ))
    (hcentered : ∀ group score, BodyCentered body
      (fun colors centers => channel group score (colors, centers)))
    (kernel : ((group : Group) → Input group) → ℝ) :
    BodyCentered body
      (flatten PrimarySlots BodySlots (DependentTensorChannel.apply channel kernel)) := by
  intro selected colors centers
  rcases selected with ⟨group, slot⟩
  simp only [flatten, wordEquiv, Equiv.coe_fn_mk, DependentTensorChannel.apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro inputs _
  have hprod (center : Body) :
      (∏ other, channel other (Pi.single (inputs other) 1)
        ((fun part => colors ⟨other, part⟩),
          fun part => Function.update centers ⟨group, slot⟩ center ⟨other, part⟩)) =
      channel group (Pi.single (inputs group) 1)
        ((fun part => colors ⟨group, part⟩),
          Function.update (fun part => centers ⟨group, part⟩) slot center) *
      ∏ other ∈ (Finset.univ : Finset Group).erase group,
        channel other (Pi.single (inputs other) 1)
          ((fun part => colors ⟨other, part⟩), (fun part => centers ⟨other, part⟩)) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ group), sigma_update_same]
    congr 1
    apply Finset.prod_congr rfl
    intro other hother
    rw [sigma_update_other centers group other (Finset.mem_erase.mp hother).1 slot center]
  simp only [hprod]
  calc
    _ = (kernel inputs * ∏ other ∈ (Finset.univ : Finset Group).erase group,
        channel other (Pi.single (inputs other) 1)
          ((fun part => colors ⟨other, part⟩), (fun part => centers ⟨other, part⟩))) *
        ∑ center, body.weight center * channel group (Pi.single (inputs group) 1)
          ((fun part => colors ⟨group, part⟩),
            Function.update (fun part => centers ⟨group, part⟩) slot center) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro center _
      ring
    _ = 0 := by rw [hcentered group (Pi.single (inputs group) 1) slot, mul_zero]

def canonicalTensor (primary : FiniteDist Primary) (body : FiniteDist Body) {r s : ℕ}
    (primaryEquiv : Sigma PrimarySlots ≃ Fin r) (bodyEquiv : Sigma BodySlots ≃ Fin s)
    (channel : ∀ group, (Input group → ℝ) →ₗ[ℝ]
      (((PrimarySlots group → Primary) × (BodySlots group → Body)) → ℝ))
    (hprimary : ∀ group score, PrimaryCentered primary
      (fun colors centers => channel group score (colors, centers)))
    (hbody : ∀ group score, BodyCentered body
      (fun colors centers => channel group score (colors, centers)))
    (kernel : ((group : Group) → Input group) → ℝ) : canonicalKernels primary body r s := by
  have hflat : flatten PrimarySlots BodySlots (DependentTensorChannel.apply channel kernel) ∈
      centeredKernelSpace primary body :=
    ⟨flatten_tensor_primaryCentered PrimarySlots BodySlots primary channel hprimary kernel,
      flatten_tensor_bodyCentered PrimarySlots BodySlots body channel hbody kernel⟩
  have hcanonical := symmetrize_centered primary body _
    (reindexKernel_centered primary body primaryEquiv bodyEquiv _ hflat)
  refine ⟨canonicalize PrimarySlots BodySlots primaryEquiv bodyEquiv
    (DependentTensorChannel.apply channel kernel), hcanonical.1, hcanonical.2, ?_⟩
  intro primaryOrder bodyOrder colors centers
  change symmetrize _ (colors ∘ primaryOrder) (centers ∘ bodyOrder) =
    symmetrize _ colors centers
  rw [symmetrize_primary_permutation, symmetrize_body_permutation]

end
end CurrentAFT.GroupedKernelNorm
