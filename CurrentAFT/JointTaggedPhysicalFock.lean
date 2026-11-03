import CurrentAFT.OrdinaryPhysicalFock
import AFT.FinitePairedPools
import AFT.MixedReindex

/-!
# Unpaired common-alphabet kernels and actual mixed physical channels

The original coefficient kernel is enlarged only by independent unused
coordinates. The paired four-output channel is then applied exactly once.
-/

namespace CurrentAFT.JointTaggedPhysicalFock

open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy PhysicalFockRates
  TaggedPhysicalFock OrdinaryPhysicalFock ControlCoordinates
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.dimension Parameters.legCount ProposalPrimary.primaryLaw

section Generic

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

private theorem independent_sum_expectation {Left Right Color : Type*}
    [Fintype Left] [Fintype Right] [Fintype Color]
    [DecidableEq Left] [DecidableEq Right] [DecidableEq (Left ⊕ Right)]
    (first : Left → FiniteDist Color) (second : Right → FiniteDist Color)
    (test : (Left ⊕ Right → Color) → ℝ) :
    (FiniteDist.independent (Sum.elim first second)).expectation test =
      (FiniteDist.independent first).expectation (fun left =>
        (FiniteDist.independent second).expectation (fun right => test (Sum.elim left right))) := by
  unfold FiniteDist.expectation FiniteDist.independent
  rw [← (Equiv.sumArrowEquivProdArrow Left Right Color).symm.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro left _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro right _
  simp only [Equiv.sumArrowEquivProdArrow, Equiv.coe_fn_symm_mk, Fintype.prod_sum_type,
    Sum.elim_inl, Sum.elim_inr]
  ring

private theorem independent_pair_expectation {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (first : Slot → FiniteDist Primary) (second : Slot → FiniteDist Body)
    (value : (Slot → Primary × Body) → ℝ) :
    (FiniteDist.independent (fun slot => (first slot).prod (second slot))).expectation value =
      (FiniteDist.independent first).expectation (fun left =>
        (FiniteDist.independent second).expectation (fun right => value (fun slot => (left slot, right slot)))) := by
  unfold FiniteDist.expectation FiniteDist.independent
  rw [← (Equiv.arrowProdEquivProdArrow Slot (fun _ => Primary) (fun _ => Body)).symm.sum_comp,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro left _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro right _
  simp only [Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk, FiniteDist.prod_weight,
    Finset.prod_mul_distrib, mul_assoc]

def unpairedKernel {r s : ℕ} (kernel : DensityKernel (Primary := Primary) (Body := Body) r s)
    (word : (Fin r ⊕ Fin s) → Primary × Body) : ℝ :=
  kernel (fun index => (word (.inl index)).1) (fun index => (word (.inr index)).2)

theorem unpairedKernel_canonical (primary : FiniteDist Primary) (body : FiniteDist Body) (r s : ℕ)
    (kernel : canonicalKernels primary body r s) :
    Hoeffding.Canonical (fun _ : Fin r ⊕ Fin s => primary.prod body) Finset.univ
      (unpairedKernel kernel.val) := by
  constructor
  · intro first second hequal
    have h : first = second := funext (fun index => hequal index (Finset.mem_univ _))
    rw [h]
  · intro index _ word
    cases index with
    | inl index =>
      have hupdate (group : Primary × Body) : unpairedKernel kernel.val (Function.update word (.inl index) group) =
          kernel.val (Function.update (fun slot => (word (.inl slot)).1) index group.1)
            (fun slot => (word (.inr slot)).2) := by
        unfold unpairedKernel
        apply congrArg₂ kernel.val
        · funext slot
          by_cases hs : slot = index <;> simp [hs, Function.update]
        · funext slot
          simp [Function.update]
      simp_rw [hupdate]
      change (primary.prod body).expectation (fun group => kernel.val
        (Function.update (fun slot => (word (.inl slot)).1) index group.1)
        (fun slot => (word (.inr slot)).2)) = 0
      rw [FiniteDist.expectation_prod]
      simp only [FiniteDist.expectation_const]
      exact kernel.property.1 index _ _
    | inr index =>
      have hupdate (group : Primary × Body) : unpairedKernel kernel.val (Function.update word (.inr index) group) =
          kernel.val (fun slot => (word (.inl slot)).1)
            (Function.update (fun slot => (word (.inr slot)).2) index group.2) := by
        unfold unpairedKernel
        apply congrArg₂ kernel.val
        · funext slot
          simp [Function.update]
        · funext slot
          by_cases hs : slot = index <;> simp [hs, Function.update]
      simp_rw [hupdate]
      change (primary.prod body).expectation (fun group => kernel.val
        (fun slot => (word (.inl slot)).1)
        (Function.update (fun slot => (word (.inr slot)).2) index group.2)) = 0
      rw [FiniteDist.expectation_prod]
      have hzero : (fun _ : Primary => body.expectation (fun point => kernel.val
          (fun slot => (word (.inl slot)).1)
          (Function.update (fun slot => (word (.inr slot)).2) index point))) = fun _ => 0 := by
        funext point
        exact kernel.property.2.1 index _ _
      rw [hzero, FiniteDist.expectation_const]

theorem unpaired_expectation (primary : FiniteDist Primary) (body : FiniteDist Body) (r s : ℕ)
    (value : (Fin r → Primary) → (Fin s → Body) → ℝ) :
    (FiniteDist.independent (fun _ : Fin r ⊕ Fin s => primary.prod body)).expectation
      (fun word => value (fun index => (word (.inl index)).1) (fun index => (word (.inr index)).2)) =
      ((FiniteDist.independent (fun _ : Fin r => primary)).prod
        (FiniteDist.independent (fun _ : Fin s => body))).expectation (fun pair => value pair.1 pair.2) := by
  have hsplit := independent_sum_expectation
    (fun _ : Fin r => primary.prod body) (fun _ : Fin s => primary.prod body)
    (fun word => value (fun index => (word (.inl index)).1) (fun index => (word (.inr index)).2))
  have hfamily : (fun _ : Fin r ⊕ Fin s => primary.prod body) =
      Sum.elim (fun _ : Fin r => primary.prod body) (fun _ : Fin s => primary.prod body) := by
    funext index
    cases index <;> rfl
  rw [FiniteDist.expectation_prod]
  rw [hfamily, hsplit, independent_pair_expectation]
  simp only [Sum.elim_inl, Sum.elim_inr]
  apply Finset.sum_congr rfl
  intro left _
  have hbody :
      (FiniteDist.independent (fun _ : Fin s => primary.prod body)).expectation
        (fun right => value left (fun index => (right index).2)) =
        (FiniteDist.independent (fun _ : Fin s => body)).expectation (fun right => value left right) := by
    rw [independent_pair_expectation]
    simp only [FiniteDist.expectation_const]
  simp_rw [hbody]
  rw [FiniteDist.expectation_const]

theorem unpairedKernel_energy (primary : FiniteDist Primary) (body : FiniteDist Body) (r s : ℕ)
    (kernel : DensityKernel (Primary := Primary) (Body := Body) r s) :
    (FiniteDist.independent (fun _ : Fin r ⊕ Fin s => primary.prod body)).l2Sq (unpairedKernel kernel) =
      ControlNorm.blockEnergy primary body kernel := by
  exact unpaired_expectation primary body r s (fun left right => kernel left right ^ 2)

def finiteKernel {r s : ℕ} (kernel : DensityKernel (Primary := Primary) (Body := Body) r s)
    (word : Fin (r + s) → Primary × Body) : ℝ :=
  unpairedKernel kernel (word ∘ finSumFinEquiv)

theorem finiteKernel_canonical (primary : FiniteDist Primary) (body : FiniteDist Body) (r s : ℕ)
    (kernel : canonicalKernels primary body r s) :
    Hoeffding.Canonical (fun _ : Fin (r + s) => primary.prod body) Finset.univ (finiteKernel kernel.val) := by
  exact MixedKernel.CoordinateTransport.canonical_equiv finSumFinEquiv
    (fun _ : Fin r ⊕ Fin s => primary.prod body) (unpairedKernel kernel.val)
    (unpairedKernel_canonical primary body r s kernel)

theorem finiteKernel_energy (primary : FiniteDist Primary) (body : FiniteDist Body) (r s : ℕ)
    (kernel : DensityKernel (Primary := Primary) (Body := Body) r s) :
    (FiniteDist.independent (fun _ : Fin (r + s) => primary.prod body)).l2Sq (finiteKernel kernel) =
      ControlNorm.blockEnergy primary body kernel := by
  have h := CanonicalMoments.independent_equiv_expectation_general
    (finSumFinEquiv : Fin r ⊕ Fin s ≃ Fin (r + s)) (fun _ => primary.prod body)
    (fun word => unpairedKernel kernel word ^ 2)
  exact h.trans (unpairedKernel_energy primary body r s kernel)

def reducePrimary (body : FiniteDist Body) : ((Primary × Body) → ℝ) →ₗ[ℝ] (Primary → ℝ) where
  toFun score first := body.expectation (fun second => score (first, second))
  map_add' first second := by funext point; exact FiniteDist.expectation_add _ _ _
  map_smul' scalar score := by
    funext point
    simp only [Pi.smul_apply, smul_eq_mul, FiniteDist.expectation_const_mul, RingHom.id_apply]

def reduceBody (primary : FiniteDist Primary) : ((Primary × Body) → ℝ) →ₗ[ℝ] (Body → ℝ) where
  toFun score second := primary.expectation (fun first => score (first, second))
  map_add' first second := by funext point; exact FiniteDist.expectation_add _ _ _
  map_smul' scalar score := by
    funext point
    simp only [Pi.smul_apply, smul_eq_mul, FiniteDist.expectation_const_mul, RingHom.id_apply]

theorem reducePrimary_mean (primary : FiniteDist Primary) (body : FiniteDist Body) (score : Primary × Body → ℝ) :
    primary.expectation (reducePrimary body score) = (primary.prod body).expectation score :=
  (FiniteDist.expectation_prod primary body score).symm

theorem reduceBody_mean (primary : FiniteDist Primary) (body : FiniteDist Body) (score : Primary × Body → ℝ) :
    body.expectation (reduceBody primary score) = (primary.prod body).expectation score := by
  rw [FiniteDist.expectation_prod]
  exact FiniteDist.expectation_comm body primary (fun second first => score (first, second))

theorem reducePrimary_energy (primary : FiniteDist Primary) (body : FiniteDist Body) (score : Primary × Body → ℝ) :
    primary.l2Sq (reducePrimary body score) ≤ (primary.prod body).l2Sq score := by
  simp only [FiniteDist.l2Sq, FiniteDist.expectation_prod]
  exact Finset.sum_le_sum (fun first _ => mul_le_mul_of_nonneg_left
    (BlockFock.mean_square_le body (fun second => score (first, second))) (primary.nonneg first))

theorem reduceBody_energy (primary : FiniteDist Primary) (body : FiniteDist Body) (score : Primary × Body → ℝ) :
    body.l2Sq (reduceBody primary score) ≤ (primary.prod body).l2Sq score := by
  have h := Finset.sum_le_sum (fun second (_ : second ∈ (Finset.univ : Finset Body)) =>
    mul_le_mul_of_nonneg_left (BlockFock.mean_square_le primary (fun first => score (first, second))) (body.nonneg second))
  apply h.trans_eq
  simp only [FiniteDist.l2Sq, FiniteDist.expectation_prod]
  exact FiniteDist.expectation_comm body primary (fun second first => score (first, second) ^ 2)

end Generic

abbrev Group (security : ℕ) := SafeControlGroups.SafeGroup security

def primaryChannel (security : ℕ) (compensatorRoot attachmentRoot : ℤ) :
    (Group security → ℝ) →ₗ[ℝ] ((Fin 4 → FirstHistogram.Palette security) → ℝ) :=
  (averagedPairedChannel security compensatorRoot attachmentRoot).comp
    (reducePrimary (ActualControls.bodyReference security))

def ordinaryChannel (security : ℕ) (root : ℤ) :
    (Group security → ℝ) →ₗ[ℝ] ((Fin 1 → FirstHistogram.Palette security) → ℝ) :=
  (bodyChannel security root).comp (reduceBody (primaryLaw security))

theorem primaryChannel_energy (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (score : Group security → ℝ) (hcentered : (SafeControlGroups.reference security).expectation score = 0)
    (multiple : ℝ) (hmultiple : 0 ≤ multiple) (hscale : normalizedScale security multiple ≤ 1) :
    BlockProducts.taggedCoefficientEnergy (uniformReference security)
      (primaryChannel security compensatorRoot attachmentRoot score) (Parameters.dimension security)
        (multiple * BackgroundRates.radius security) ≤
      (pairedConstant multiple / (Parameters.legCount security : ℝ)) * (SafeControlGroups.reference security).l2Sq score := by
  have hmean : (primaryLaw security).expectation
      (reducePrimary (ActualControls.bodyReference security) score) = 0 := by
    rw [reducePrimary_mean]
    exact hcentered
  have h := averagedPaired_energy_le security compensatorRoot attachmentRoot
    (reducePrimary (ActualControls.bodyReference security) score) hmean multiple hmultiple hscale
  apply h.trans
  apply mul_le_mul_of_nonneg_left (reducePrimary_energy (primaryLaw security) (ActualControls.bodyReference security) score)
  exact div_nonneg (pairedConstant_nonneg multiple) (Nat.cast_nonneg _)

theorem ordinaryChannel_energy (security : ℕ) (root : ℤ) (score : Group security → ℝ)
    (hcentered : (SafeControlGroups.reference security).expectation score = 0) (multiple : ℝ) :
    BlockProducts.taggedCoefficientEnergy (uniformReference security)
      (ordinaryChannel security root score) (Parameters.dimension security) (multiple * BackgroundRates.radius security) ≤
      (32 * normalizedScale security multiple ^ 2) * (SafeControlGroups.reference security).l2Sq score := by
  have hmean : (ActualControls.bodyReference security).expectation (reduceBody (primaryLaw security) score) = 0 := by
    rw [reduceBody_mean]
    exact hcentered
  have h := bodyChannel_energy_le security root (reduceBody (primaryLaw security) score) hmean multiple
  apply h.trans
  exact mul_le_mul_of_nonneg_left (reduceBody_energy (primaryLaw security) (ActualControls.bodyReference security) score) (by positivity)

def roleSlots (r s : ℕ) : (Fin r ⊕ Fin s) → Type
  | .inl _ => Fin 4
  | .inr _ => Fin 1

instance roleSlotsFintype (r s : ℕ) (index : Fin r ⊕ Fin s) : Fintype (roleSlots r s index) := by
  cases index with
  | inl _ => exact inferInstanceAs (Fintype (Fin 4))
  | inr _ => exact inferInstanceAs (Fintype (Fin 1))

def roleChannel (security r s : ℕ) (compensatorRoot attachmentRoot : Fin r → ℤ) (bodyRoot : Fin s → ℤ) :
    (index : Fin r ⊕ Fin s) → (Group security → ℝ) →ₗ[ℝ] ((roleSlots r s index → FirstHistogram.Palette security) → ℝ)
  | .inl index => primaryChannel security (compensatorRoot index) (attachmentRoot index)
  | .inr index => ordinaryChannel security (bodyRoot index)

def roleBound (security r s : ℕ) (multiple : ℝ) : Fin r ⊕ Fin s → ℝ
  | .inl _ => Real.sqrt (pairedConstant multiple / (Parameters.legCount security : ℝ))
  | .inr _ => Real.sqrt (32 * normalizedScale security multiple ^ 2)

theorem roleChannel_energy (security r s : ℕ) (compensatorRoot attachmentRoot : Fin r → ℤ)
    (bodyRoot : Fin s → ℤ) (multiple : ℝ) (hmultiple : 0 ≤ multiple)
    (hscale : normalizedScale security multiple ≤ 1) (index : Fin r ⊕ Fin s)
    (score : Group security → ℝ) (hcentered : (SafeControlGroups.reference security).expectation score = 0) :
    BlockProducts.taggedCoefficientEnergy (uniformReference security)
      (roleChannel security r s compensatorRoot attachmentRoot bodyRoot index score) (Parameters.dimension security)
        (multiple * BackgroundRates.radius security) ≤
      roleBound security r s multiple index ^ 2 * (SafeControlGroups.reference security).l2Sq score := by
  cases index with
  | inl index =>
    rw [roleBound, Real.sq_sqrt (div_nonneg (pairedConstant_nonneg multiple) (Nat.cast_nonneg _))]
    exact primaryChannel_energy security (compensatorRoot index) (attachmentRoot index) score hcentered multiple hmultiple hscale
  | inr index =>
    rw [roleBound, Real.sq_sqrt (by positivity : 0 ≤ 32 * normalizedScale security multiple ^ 2)]
    exact ordinaryChannel_energy security (bodyRoot index) score hcentered multiple

def physicalSlots (r s : ℕ) (index : Fin (r + s)) : Type :=
  roleSlots r s (finSumFinEquiv.symm index)

instance physicalSlotsFintype (r s : ℕ) (index : Fin (r + s)) : Fintype (physicalSlots r s index) :=
  roleSlotsFintype r s (finSumFinEquiv.symm index)

def physicalChannel (security r s : ℕ) (compensatorRoot attachmentRoot : Fin r → ℤ) (bodyRoot : Fin s → ℤ)
    (index : Fin (r + s)) :
    (Group security → ℝ) →ₗ[ℝ] ((physicalSlots r s index → FirstHistogram.Palette security) → ℝ) :=
  roleChannel security r s compensatorRoot attachmentRoot bodyRoot (finSumFinEquiv.symm index)

/-- The actual mixed output of an arbitrary original canonical kernel.
The added independent coordinates are unused before applying the paired
physical response once, and every input remains in one joint finite sum. -/
def jointMass (security r s : ℕ) (compensatorRoot attachmentRoot : Fin r → ℤ) (bodyRoot : Fin s → ℤ)
    (kernel : DensityKernel (Primary := FirstHistogram.Palette security)
      (Body := ActualControls.SafePalette security) r s) :
    (Sigma (physicalSlots r s) → FirstHistogram.Palette security) → ℝ :=
  JointPhysicalChannel.mass (physicalSlots r s)
    (physicalChannel security r s compensatorRoot attachmentRoot bodyRoot) (finiteKernel kernel)

theorem physicalSlots_card_le (r s : ℕ) (index : Fin (r + s)) : Fintype.card (physicalSlots r s index) ≤ 4 := by
  have h (index : Fin r ⊕ Fin s) : Fintype.card (roleSlots r s index) ≤ 4 := by
    cases index with
    | inl _ => change Fintype.card (Fin 4) ≤ 4; norm_num
    | inr _ => change Fintype.card (Fin 1) ≤ 4; norm_num
  exact h (finSumFinEquiv.symm index)

theorem physicalSlots_card (r s : ℕ) : Fintype.card (Sigma (physicalSlots r s)) = 4 * r + s := by
  rw [Fintype.card_sigma]
  change (∑ index : Fin (r + s), Fintype.card (roleSlots r s (finSumFinEquiv.symm index))) = _
  rw [finSumFinEquiv.symm.sum_comp (fun index : Fin r ⊕ Fin s => Fintype.card (roleSlots r s index))]
  simp [roleSlots, Fintype.sum_sum_type, mul_comm]

theorem roleBound_product (security r s : ℕ) (multiple : ℝ) :
    (∏ index : Fin (r + s), roleBound security r s multiple (finSumFinEquiv.symm index) ^ 2) =
      (pairedConstant multiple / (Parameters.legCount security : ℝ)) ^ r *
        (32 * normalizedScale security multiple ^ 2) ^ s := by
  rw [finSumFinEquiv.symm.prod_comp (fun index : Fin r ⊕ Fin s => roleBound security r s multiple index ^ 2)]
  simp only [Fintype.prod_sum_type, roleBound,
    Real.sq_sqrt (div_nonneg (pairedConstant_nonneg multiple) (Nat.cast_nonneg _)),
    Real.sq_sqrt (by positivity : 0 ≤ 32 * normalizedScale security multiple ^ 2),
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private theorem law_nonempty {State : Type*} [Fintype State] (law : FiniteDist State) : Nonempty State := by
  by_contra h
  haveI : IsEmpty State := not_nonempty_iff.mp h
  have := law.sum_one
  simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_ne_one] at this

/-- Complete marked Fock energy for an arbitrary nonseparable two-alphabet
coefficient kernel. Constants depend on its fixed arities, without a
palette-size or tensor-rank factor. -/
theorem jointMass_energy_le (security r s : ℕ) (compensatorRoot attachmentRoot : Fin r → ℤ)
    (bodyRoot : Fin s → ℤ)
    (kernel : canonicalKernels (primaryLaw security) (ActualControls.bodyReference security) r s)
    (multiple : ℝ) (hmultiple : 0 ≤ multiple) (hscale : normalizedScale security multiple ≤ 1) :
    BlockProducts.taggedCoefficientEnergy (uniformReference security)
      (jointMass security r s compensatorRoot attachmentRoot bodyRoot kernel.val)
      (Parameters.dimension security) (multiple * BackgroundRates.radius security) ≤
      ((4 * r + s + 1 : ℕ) * ((5 : ℕ) ^ (r + s) : ℕ) * ((4 * (r + s)).factorial : ℝ)) *
        (((pairedConstant multiple / (Parameters.legCount security : ℝ)) ^ r *
          (32 * normalizedScale security multiple ^ 2) ^ s) *
            ControlNorm.blockEnergy (primaryLaw security) (ActualControls.bodyReference security) kernel.val) := by
  letI : Nonempty (Group security) := law_nonempty (SafeControlGroups.reference security)
  have h := JointPhysicalChannel.joint_mass_canonical_energy_le (r + s)
    (physicalSlots r s) (uniformReference security) 4 (Parameters.dimension security)
    (multiple * BackgroundRates.radius security) (physicalSlots_card_le r s)
    (fun _ : Fin (r + s) => SafeControlGroups.reference security)
    (physicalChannel security r s compensatorRoot attachmentRoot bodyRoot)
    (fun index => roleBound security r s multiple (finSumFinEquiv.symm index))
    (fun index score hcentered => roleChannel_energy security r s compensatorRoot attachmentRoot bodyRoot
      multiple hmultiple hscale (finSumFinEquiv.symm index) score hcentered)
    (finiteKernel kernel.val)
    (finiteKernel_canonical (primaryLaw security) (ActualControls.bodyReference security) r s kernel)
  rw [physicalSlots_card, roleBound_product, SafeControlGroups.reference, finiteKernel_energy] at h
  simpa only [Nat.reduceAdd, Nat.mul_comm (r + s) 4] using h

def jointConstant (r s : ℕ) (multiple : ℝ) : ℝ :=
  ((4 * r + s + 1 : ℕ) * ((5 : ℕ) ^ (r + s) : ℕ) * ((4 * (r + s)).factorial : ℝ)) *
    (pairedConstant multiple ^ r * (32 * multiple ^ 2) ^ s)

theorem jointConstant_nonneg (r s : ℕ) (multiple : ℝ) : 0 ≤ jointConstant r s multiple := by
  unfold jointConstant
  have := pairedConstant_nonneg multiple
  positivity

/-- The actual complete joint Fock response is bounded by the manuscript's
two-pool graded Hilbert weight. The constant is independent of security,
the palette size, the root values, and the rank of the joint kernel. -/
theorem jointMass_graded_energy_le (security r s : ℕ) (compensatorRoot attachmentRoot : Fin r → ℤ)
    (bodyRoot : Fin s → ℤ)
    (kernel : canonicalKernels (primaryLaw security) (ActualControls.bodyReference security) r s)
    (multiple : ℝ) (hmultiple : 0 ≤ multiple) (hscale : normalizedScale security multiple ≤ 1) :
    BlockProducts.taggedCoefficientEnergy (uniformReference security)
      (jointMass security r s compensatorRoot attachmentRoot bodyRoot kernel.val)
      (Parameters.dimension security) (multiple * BackgroundRates.radius security) ≤
      jointConstant r s multiple *
        (ControlNorm.gradeWeight (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security) r s *
          ControlNorm.blockL2 (primaryLaw security) (ActualControls.bodyReference security) kernel.val) ^ 2 := by
  have h := jointMass_energy_le security r s compensatorRoot attachmentRoot bodyRoot kernel multiple hmultiple hscale
  have hbody : 32 * normalizedScale security multiple ^ 2 ≤
      (32 * multiple ^ 2) * BackgroundRates.bodyFactor security ^ 2 := by
    have h := mul_le_mul_of_nonneg_left (normalizedScale_bodyFactor_le security multiple hmultiple)
      (by norm_num : (0 : ℝ) ≤ 32)
    nlinarith only [h]
  have hprimary : pairedConstant multiple / (Parameters.legCount security : ℝ) =
      pairedConstant multiple * BackgroundRates.primaryFactor security ^ 2 := by
    rw [primaryFactor_square]
    ring
  have hweight : (pairedConstant multiple / (Parameters.legCount security : ℝ)) ^ r *
      (32 * normalizedScale security multiple ^ 2) ^ s ≤
      (pairedConstant multiple ^ r * (32 * multiple ^ 2) ^ s) *
        ControlNorm.gradeWeight (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security) r s ^ 2 := by
    apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbody s)
      (pow_nonneg (div_nonneg (pairedConstant_nonneg multiple) (Nat.cast_nonneg _)) r)).trans_eq
    rw [hprimary]
    simp only [ControlNorm.gradeWeight, mul_pow, ← pow_mul, Nat.mul_comm r 2, Nat.mul_comm s 2]
    ring
  apply h.trans
  have he := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hweight
      (ControlNorm.blockEnergy_nonneg (primaryLaw security) (ActualControls.bodyReference security) kernel.val))
    (show (0 : ℝ) ≤ ((4 * r + s + 1 : ℕ) * ((5 : ℕ) ^ (r + s) : ℕ) * ((4 * (r + s)).factorial : ℝ)) by positivity)
  apply he.trans_eq
  simp only [mul_pow, ControlNorm.blockL2_sq]
  unfold jointConstant
  ring

end

end CurrentAFT.JointTaggedPhysicalFock
