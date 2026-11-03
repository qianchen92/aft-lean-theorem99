import CurrentAFT.ControlCoordinates

/-!
# Actual disjoint-slot products of current canonical control kernels

Two kernels are first tensored on disjoint sums of their primary slots and
of their body slots. The combined slots are then separately averaged over
all permutations, including repeated permutations, exactly as in the current
manuscript. This is a finite operation on actual density kernels, not an
assumed abstract algebra. Truncation above the specified total order is zero.

This file is a homogeneous-product foundation. A complete multiplication on
all truncated coefficient families and its associativity remain separate
proof obligations unless explicitly stated below.
-/

namespace CurrentAFT.ControlProduct

open AFT ControlCoordinates
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) :=
  Classical.decEq _

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

/-- Slot labels have independent types for the two public-control pools. -/
abbrev Kernel (PrimarySlots BodySlots : Type*) :=
  (PrimarySlots → Primary) → (BodySlots → Body) → ℝ

section SlotSpaces

variable {PS BS PT BT : Type*} [Fintype PS] [Fintype BS] [Fintype PT] [Fintype BT]

def PrimaryCentered (primary : FiniteDist Primary)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) : Prop :=
  ∀ index colors centers, ∑ color, primary.weight color *
    kernel (Function.update colors index color) centers = 0

def BodyCentered (body : FiniteDist Body)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) : Prop :=
  ∀ index colors centers, ∑ center, body.weight center *
    kernel colors (Function.update centers index center) = 0

/-- Only centering is imposed before symmetrization. The raw tensor need
not be separately symmetric in the combined slots. -/
def centeredKernelSpace (primary : FiniteDist Primary) (body : FiniteDist Body) :
    Submodule ℝ (Kernel (Primary := Primary) (Body := Body) PS BS) where
  carrier := {kernel | PrimaryCentered primary kernel ∧ BodyCentered body kernel}
  zero_mem' := by constructor <;> intro index colors centers <;> simp
  add_mem' := by
    intro first second hfirst hsecond
    constructor
    · intro index colors centers
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib,
        hfirst.1 index colors centers, hsecond.1 index colors centers, add_zero]
    · intro index colors centers
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib,
        hfirst.2 index colors centers, hsecond.2 index colors centers, add_zero]
  smul_mem' := by
    intro scalar kernel hkernel
    constructor
    · intro index colors centers
      change (∑ color, primary.weight color *
        (scalar * kernel (Function.update colors index color) centers)) = 0
      calc
        _ = scalar * ∑ color, primary.weight color *
            kernel (Function.update colors index color) centers := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro color _
          ring
        _ = 0 := by rw [hkernel.1 index colors centers, mul_zero]
    · intro index colors centers
      change (∑ center, body.weight center *
        (scalar * kernel colors (Function.update centers index center))) = 0
      calc
        _ = scalar * ∑ center, body.weight center *
            kernel colors (Function.update centers index center) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro center _
          ring
        _ = 0 := by rw [hkernel.2 index colors centers, mul_zero]

/-- Pull a kernel to equivalent slot labels, without changing its colors. -/
def reindexKernel (primaryEquiv : PS ≃ PT) (bodyEquiv : BS ≃ BT)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) :
    Kernel (Primary := Primary) (Body := Body) PT BT :=
  fun colors centers => kernel (colors ∘ primaryEquiv) (centers ∘ bodyEquiv)

private theorem update_precompose_equiv {Index NewIndex Color : Type*}
    (equiv : Index ≃ NewIndex) (word : NewIndex → Color) (index : NewIndex) (color : Color) :
    Function.update word index color ∘ equiv =
      Function.update (word ∘ equiv) (equiv.symm index) color := by
  simpa only [Equiv.apply_symm_apply] using
    Function.update_comp_eq_of_injective word equiv.injective (equiv.symm index) color

omit [Fintype PS] [Fintype BS] [Fintype PT] [Fintype BT] in
theorem reindexKernel_centered (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryEquiv : PS ≃ PT) (bodyEquiv : BS ≃ BT)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS)
    (hkernel : kernel ∈ centeredKernelSpace primary body) :
    reindexKernel primaryEquiv bodyEquiv kernel ∈ centeredKernelSpace primary body := by
  constructor
  · intro index colors centers
    simp only [reindexKernel, update_precompose_equiv]
    exact hkernel.1 (primaryEquiv.symm index) _ _
  · intro index colors centers
    simp only [reindexKernel, update_precompose_equiv]
    exact hkernel.2 (bodyEquiv.symm index) _ _

/-- The literal tensor uses disjoint slot sets. This has no overlapping
physical indices and therefore differs from multiplying two U-statistics. -/
def disjointTensor (first : Kernel (Primary := Primary) (Body := Body) PS BS)
    (second : Kernel (Primary := Primary) (Body := Body) PT BT) :
    Kernel (Primary := Primary) (Body := Body) (PS ⊕ PT) (BS ⊕ BT) :=
  fun colors centers => first (colors ∘ Sum.inl) (centers ∘ Sum.inl) *
    second (colors ∘ Sum.inr) (centers ∘ Sum.inr)

omit [Fintype PS] [Fintype BS] [Fintype PT] [Fintype BT] in
theorem disjointTensor_centered (primary : FiniteDist Primary) (body : FiniteDist Body)
    (first : Kernel (Primary := Primary) (Body := Body) PS BS)
    (second : Kernel (Primary := Primary) (Body := Body) PT BT)
    (hfirst : first ∈ centeredKernelSpace primary body)
    (hsecond : second ∈ centeredKernelSpace primary body) :
    disjointTensor first second ∈ centeredKernelSpace primary body := by
  constructor
  · intro index colors centers
    cases index with
    | inl index =>
      have hleft color : Function.update colors (Sum.inl index) color ∘ Sum.inl =
          Function.update (colors ∘ Sum.inl) index color :=
        Function.update_comp_eq_of_injective colors Sum.inl_injective index color
      have hright color : Function.update colors (Sum.inl index) color ∘ Sum.inr = colors ∘ Sum.inr :=
        Function.update_comp_eq_of_forall_ne colors color (fun _ => Sum.inr_ne_inl)
      simp only [disjointTensor, hleft, hright, ← mul_assoc, ← Finset.sum_mul,
        hfirst.1 index, zero_mul]
    | inr index =>
      have hleft color : Function.update colors (Sum.inr index) color ∘ Sum.inl = colors ∘ Sum.inl :=
        Function.update_comp_eq_of_forall_ne colors color (fun _ => Sum.inl_ne_inr)
      have hright color : Function.update colors (Sum.inr index) color ∘ Sum.inr =
          Function.update (colors ∘ Sum.inr) index color :=
        Function.update_comp_eq_of_injective colors Sum.inr_injective index color
      simp only [disjointTensor, hleft, hright]
      calc
        _ = first (colors ∘ Sum.inl) (centers ∘ Sum.inl) *
            ∑ color, primary.weight color * second (Function.update (colors ∘ Sum.inr) index color)
              (centers ∘ Sum.inr) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro color _
          ring
        _ = 0 := by rw [hsecond.1 index, mul_zero]
  · intro index colors centers
    cases index with
    | inl index =>
      have hleft center : Function.update centers (Sum.inl index) center ∘ Sum.inl =
          Function.update (centers ∘ Sum.inl) index center :=
        Function.update_comp_eq_of_injective centers Sum.inl_injective index center
      have hright center : Function.update centers (Sum.inl index) center ∘ Sum.inr = centers ∘ Sum.inr :=
        Function.update_comp_eq_of_forall_ne centers center (fun _ => Sum.inr_ne_inl)
      simp only [disjointTensor, hleft, hright, ← mul_assoc, ← Finset.sum_mul,
        hfirst.2 index, zero_mul]
    | inr index =>
      have hleft center : Function.update centers (Sum.inr index) center ∘ Sum.inl = centers ∘ Sum.inl :=
        Function.update_comp_eq_of_forall_ne centers center (fun _ => Sum.inl_ne_inr)
      have hright center : Function.update centers (Sum.inr index) center ∘ Sum.inr =
          Function.update (centers ∘ Sum.inr) index center :=
        Function.update_comp_eq_of_injective centers Sum.inr_injective index center
      simp only [disjointTensor, hleft, hright]
      calc
        _ = first (colors ∘ Sum.inl) (centers ∘ Sum.inl) *
            ∑ center, body.weight center * second (colors ∘ Sum.inr)
              (Function.update (centers ∘ Sum.inr) index center) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro center _
          ring
        _ = 0 := by rw [hsecond.2 index, mul_zero]

/-- Average both slot permutations, including all repeated permutations. -/
def symmetrize (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) :
    Kernel (Primary := Primary) (Body := Body) PS BS :=
  ∑ primaryOrder : Equiv.Perm PS, (FiniteDist.uniform (Equiv.Perm PS)).weight primaryOrder •
    ∑ bodyOrder : Equiv.Perm BS, (FiniteDist.uniform (Equiv.Perm BS)).weight bodyOrder •
      reindexKernel primaryOrder bodyOrder kernel

omit [Fintype Primary] [Fintype Body] in
theorem symmetrize_apply (kernel : Kernel (Primary := Primary) (Body := Body) PS BS)
    (colors : PS → Primary) (centers : BS → Body) :
    symmetrize kernel colors centers =
      (Fintype.card (Equiv.Perm PS) : ℝ)⁻¹ * (Fintype.card (Equiv.Perm BS) : ℝ)⁻¹ *
        ∑ primaryOrder : Equiv.Perm PS, ∑ bodyOrder : Equiv.Perm BS,
          kernel (colors ∘ primaryOrder) (centers ∘ bodyOrder) := by
  simp only [symmetrize, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    FiniteDist.uniform_weight, reindexKernel, ← Finset.mul_sum, mul_assoc]

theorem symmetrize_centered (primary : FiniteDist Primary) (body : FiniteDist Body)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS)
    (hkernel : kernel ∈ centeredKernelSpace primary body) :
    symmetrize kernel ∈ centeredKernelSpace primary body := by
  unfold symmetrize
  apply Submodule.sum_mem
  intro primaryOrder _
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro bodyOrder _
  apply Submodule.smul_mem
  exact reindexKernel_centered primary body primaryOrder bodyOrder kernel hkernel

omit [Fintype Primary] [Fintype Body] in
theorem symmetrize_primary_permutation
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS)
    (colors : PS → Primary) (centers : BS → Body) (permutation : Equiv.Perm PS) :
    symmetrize kernel (colors ∘ permutation) centers = symmetrize kernel colors centers := by
  rw [symmetrize_apply, symmetrize_apply]
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft permutation)
    (fun primaryOrder : Equiv.Perm PS => ∑ bodyOrder : Equiv.Perm BS,
      kernel (colors ∘ primaryOrder) (centers ∘ bodyOrder))

omit [Fintype Primary] [Fintype Body] in
theorem symmetrize_body_permutation
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS)
    (colors : PS → Primary) (centers : BS → Body) (permutation : Equiv.Perm BS) :
    symmetrize kernel colors (centers ∘ permutation) = symmetrize kernel colors centers := by
  rw [symmetrize_apply, symmetrize_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro primaryOrder _
  exact Equiv.sum_comp (Equiv.mulLeft permutation)
    (fun bodyOrder : Equiv.Perm BS => kernel (colors ∘ primaryOrder) (centers ∘ bodyOrder))

omit [Fintype Primary] [Fintype Body] in
theorem symmetrize_of_symmetric
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS)
    (hsymmetric : ∀ (primaryOrder : Equiv.Perm PS) (bodyOrder : Equiv.Perm BS) colors centers,
      kernel (colors ∘ primaryOrder) (centers ∘ bodyOrder) = kernel colors centers) :
    symmetrize kernel = kernel := by
  funext colors centers
  rw [symmetrize_apply]
  simp only [hsymmetric, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hprimary : (Fintype.card (Equiv.Perm PS) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hbody : (Fintype.card (Equiv.Perm BS) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

omit [Fintype Primary] [Fintype Body] in
/-- Relabeling the complete slot sets commutes with the actual permutation
average, by a bijection between their full permutation groups. -/
theorem reindexKernel_symmetrize (primaryEquiv : PS ≃ PT) (bodyEquiv : BS ≃ BT)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) :
    reindexKernel primaryEquiv bodyEquiv (symmetrize kernel) =
      symmetrize (reindexKernel primaryEquiv bodyEquiv kernel) := by
  funext colors centers
  change symmetrize kernel (colors ∘ primaryEquiv) (centers ∘ bodyEquiv) = _
  rw [symmetrize_apply, symmetrize_apply]
  have hp : Fintype.card (Equiv.Perm PS) = Fintype.card (Equiv.Perm PT) :=
    Fintype.card_congr primaryEquiv.permCongr
  have hb : Fintype.card (Equiv.Perm BS) = Fintype.card (Equiv.Perm BT) :=
    Fintype.card_congr bodyEquiv.permCongr
  rw [hp, hb]
  congr 1
  symm
  rw [← primaryEquiv.permCongr.sum_comp]
  apply Finset.sum_congr rfl
  intro primaryOrder _
  rw [← bodyEquiv.permCongr.sum_comp]
  apply Finset.sum_congr rfl
  intro bodyOrder _
  unfold reindexKernel
  apply congrArg₂ kernel
  · funext index
    simp only [Function.comp_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  · funext index
    simp only [Function.comp_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply]

omit [Fintype Primary] [Fintype Body] [Fintype PS] [Fintype BS] [Fintype PT] [Fintype BT] in
theorem disjointTensor_swap
    (first : Kernel (Primary := Primary) (Body := Body) PS BS)
    (second : Kernel (Primary := Primary) (Body := Body) PT BT) :
    reindexKernel (Equiv.sumComm PS PT) (Equiv.sumComm BS BT) (disjointTensor first second) =
      disjointTensor second first := by
  funext colors centers
  simp only [reindexKernel, disjointTensor, Function.comp_def, Equiv.sumComm_apply,
    Sum.swap, Sum.elim_inl, Sum.elim_inr]
  ring

omit [Fintype Primary] [Fintype Body] in
/-- Commutativity on the actual disjoint slot labels. Both slot types are
swapped explicitly, rather than identified by an assumed algebra law. -/
theorem symmetrizedTensor_swap
    (first : Kernel (Primary := Primary) (Body := Body) PS BS)
    (second : Kernel (Primary := Primary) (Body := Body) PT BT) :
    reindexKernel (Equiv.sumComm PS PT) (Equiv.sumComm BS BT)
        (symmetrize (disjointTensor first second)) =
      symmetrize (disjointTensor second first) := by
  rw [reindexKernel_symmetrize, disjointTensor_swap]

/-- The averaging operation is a proved linear map on the actual arrays. -/
def symmetrizeLinear :
    Kernel (Primary := Primary) (Body := Body) PS BS →ₗ[ℝ]
      Kernel (Primary := Primary) (Body := Body) PS BS where
  toFun := symmetrize
  map_add' first second := by
    funext colors centers
    simp only [symmetrize_apply, Pi.add_apply, Finset.sum_add_distrib]
    ring
  map_smul' scalar kernel := by
    funext colors centers
    simp only [symmetrize_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      ← Finset.mul_sum]
    ring

def tensorLeftLinear (second : Kernel (Primary := Primary) (Body := Body) PT BT) :
    Kernel (Primary := Primary) (Body := Body) PS BS →ₗ[ℝ]
      Kernel (Primary := Primary) (Body := Body) (PS ⊕ PT) (BS ⊕ BT) where
  toFun first := disjointTensor first second
  map_add' first other := by
    funext colors centers
    simp only [disjointTensor, Pi.add_apply, add_mul]
  map_smul' scalar first := by
    funext colors centers
    simp only [disjointTensor, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

def tensorRightLinear (first : Kernel (Primary := Primary) (Body := Body) PS BS) :
    Kernel (Primary := Primary) (Body := Body) PT BT →ₗ[ℝ]
      Kernel (Primary := Primary) (Body := Body) (PS ⊕ PT) (BS ⊕ BT) where
  toFun second := disjointTensor first second
  map_add' second other := by
    funext colors centers
    simp only [disjointTensor, Pi.add_apply, mul_add]
  map_smul' scalar second := by
    funext colors centers
    simp only [disjointTensor, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

omit [Fintype Primary] [Fintype Body] in
theorem symmetrize_reindex_permutations
    (primaryOrder : Equiv.Perm PS) (bodyOrder : Equiv.Perm BS)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) :
    symmetrize (reindexKernel primaryOrder bodyOrder kernel) = symmetrize kernel := by
  rw [← reindexKernel_symmetrize]
  funext colors centers
  change symmetrize kernel (colors ∘ primaryOrder) (centers ∘ bodyOrder) = _
  rw [symmetrize_primary_permutation, symmetrize_body_permutation]

omit [Fintype Primary] [Fintype Body] [Fintype PS] [Fintype BS] [Fintype PT] [Fintype BT] in
theorem disjointTensor_reindex_first
    (primaryOrder : Equiv.Perm PS) (bodyOrder : Equiv.Perm BS)
    (first : Kernel (Primary := Primary) (Body := Body) PS BS)
    (second : Kernel (Primary := Primary) (Body := Body) PT BT) :
    disjointTensor (reindexKernel primaryOrder bodyOrder first) second =
      reindexKernel (Equiv.sumCongr primaryOrder (Equiv.refl PT))
        (Equiv.sumCongr bodyOrder (Equiv.refl BT)) (disjointTensor first second) := by
  funext colors centers
  simp [disjointTensor, reindexKernel, Function.comp_def]

omit [Fintype Primary] [Fintype Body] [Fintype PS] [Fintype BS] [Fintype PT] [Fintype BT] in
theorem disjointTensor_reindex_second
    (primaryOrder : Equiv.Perm PT) (bodyOrder : Equiv.Perm BT)
    (first : Kernel (Primary := Primary) (Body := Body) PS BS)
    (second : Kernel (Primary := Primary) (Body := Body) PT BT) :
    disjointTensor first (reindexKernel primaryOrder bodyOrder second) =
      reindexKernel (Equiv.sumCongr (Equiv.refl PS) primaryOrder)
        (Equiv.sumCongr (Equiv.refl BS) bodyOrder) (disjointTensor first second) := by
  funext colors centers
  simp [disjointTensor, reindexKernel, Function.comp_def]

omit [Fintype Primary] [Fintype Body] in
/-- A full permutation average absorbs the internal first-block average.
The proof expands both finite averages and reindexes each summand. -/
theorem symmetrizedTensor_first_symmetrize
    (first : Kernel (Primary := Primary) (Body := Body) PS BS)
    (second : Kernel (Primary := Primary) (Body := Body) PT BT) :
    symmetrize (disjointTensor (symmetrize first) second) = symmetrize (disjointTensor first second) := by
  let operation : Kernel (Primary := Primary) (Body := Body) PS BS →ₗ[ℝ]
      Kernel (Primary := Primary) (Body := Body) (PS ⊕ PT) (BS ⊕ BT) :=
    symmetrizeLinear.comp (tensorLeftLinear second)
  change operation (symmetrize first) = operation first
  have hterm (primaryOrder : Equiv.Perm PS) (bodyOrder : Equiv.Perm BS) :
      operation (reindexKernel primaryOrder bodyOrder first) = operation first := by
    change symmetrize (disjointTensor (reindexKernel primaryOrder bodyOrder first) second) = _
    rw [disjointTensor_reindex_first, symmetrize_reindex_permutations]
    rfl
  unfold symmetrize
  rw [map_sum]
  simp_rw [map_smul, map_sum, map_smul, hterm]
  simp only [← Finset.sum_smul, FiniteDist.sum_one, one_smul]

omit [Fintype Primary] [Fintype Body] in
theorem symmetrizedTensor_second_symmetrize
    (first : Kernel (Primary := Primary) (Body := Body) PS BS)
    (second : Kernel (Primary := Primary) (Body := Body) PT BT) :
    symmetrize (disjointTensor first (symmetrize second)) = symmetrize (disjointTensor first second) := by
  let operation : Kernel (Primary := Primary) (Body := Body) PT BT →ₗ[ℝ]
      Kernel (Primary := Primary) (Body := Body) (PS ⊕ PT) (BS ⊕ BT) :=
    symmetrizeLinear.comp (tensorRightLinear first)
  change operation (symmetrize second) = operation second
  have hterm (primaryOrder : Equiv.Perm PT) (bodyOrder : Equiv.Perm BT) :
      operation (reindexKernel primaryOrder bodyOrder second) = operation second := by
    change symmetrize (disjointTensor first (reindexKernel primaryOrder bodyOrder second)) = _
    rw [disjointTensor_reindex_second, symmetrize_reindex_permutations]
    rfl
  unfold symmetrize
  rw [map_sum]
  simp_rw [map_smul, map_sum, map_smul, hterm]
  simp only [← Finset.sum_smul, FiniteDist.sum_one, one_smul]

variable {PU BU : Type*} [Fintype PU] [Fintype BU]

omit [Fintype Primary] [Fintype Body] [Fintype PS] [Fintype BS] [Fintype PT] [Fintype BT]
  [Fintype PU] [Fintype BU] in
theorem disjointTensor_assoc
    (first : Kernel (Primary := Primary) (Body := Body) PS BS)
    (second : Kernel (Primary := Primary) (Body := Body) PT BT)
    (third : Kernel (Primary := Primary) (Body := Body) PU BU) :
    reindexKernel (Equiv.sumAssoc PS PT PU) (Equiv.sumAssoc BS BT BU)
        (disjointTensor (disjointTensor first second) third) =
      disjointTensor first (disjointTensor second third) := by
  funext colors centers
  simp only [reindexKernel, disjointTensor, Function.comp_def,
    Equiv.sumAssoc_apply_inl_inl, Equiv.sumAssoc_apply_inl_inr, Equiv.sumAssoc_apply_inr]
  ring

omit [Fintype Primary] [Fintype Body] in
/-- Associativity of the actual separately symmetrized disjoint tensors.
The only identification is the explicit associator of the slot sums. No
abstract star law or physical U-statistic product identity is assumed. -/
theorem symmetrizedTensor_assoc
    (first : Kernel (Primary := Primary) (Body := Body) PS BS)
    (second : Kernel (Primary := Primary) (Body := Body) PT BT)
    (third : Kernel (Primary := Primary) (Body := Body) PU BU) :
    reindexKernel (Equiv.sumAssoc PS PT PU) (Equiv.sumAssoc BS BT BU)
        (symmetrize (disjointTensor (symmetrize (disjointTensor first second)) third)) =
      symmetrize (disjointTensor first (symmetrize (disjointTensor second third))) := by
  rw [symmetrizedTensor_first_symmetrize, symmetrizedTensor_second_symmetrize,
    reindexKernel_symmetrize, disjointTensor_assoc]

end SlotSpaces

/-- The actual raw tensor in the manuscript's finite ordered slot labels. -/
def finDisjointTensor {r s r' s' : ℕ}
    (first : DensityKernel (Primary := Primary) (Body := Body) r s)
    (second : DensityKernel (Primary := Primary) (Body := Body) r' s') :
    DensityKernel (Primary := Primary) (Body := Body) (r + r') (s + s') :=
  reindexKernel finSumFinEquiv finSumFinEquiv (disjointTensor first second)

/-- The homogeneous star product has been constructed on actual canonical
density kernels. Centering and separate symmetry are proved properties. -/
def homogeneousProduct (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s r' s' : ℕ} (first : canonicalKernels primary body r s)
    (second : canonicalKernels primary body r' s') :
    canonicalKernels primary body (r + r') (s + s') := by
  let result := symmetrize (finDisjointTensor first.val second.val)
  have hfirst : first.val ∈ centeredKernelSpace primary body := ⟨first.property.1, first.property.2.1⟩
  have hsecond : second.val ∈ centeredKernelSpace primary body := ⟨second.property.1, second.property.2.1⟩
  have hcenter : result ∈ centeredKernelSpace primary body :=
    symmetrize_centered primary body _
      (reindexKernel_centered primary body finSumFinEquiv finSumFinEquiv _
        (disjointTensor_centered primary body first.val second.val hfirst hsecond))
  refine ⟨result, hcenter.1, hcenter.2, ?_⟩
  intro primaryOrder bodyOrder colors centers
  change symmetrize _ (colors ∘ primaryOrder) (centers ∘ bodyOrder) = symmetrize _ colors centers
  rw [symmetrize_primary_permutation, symmetrize_body_permutation]

/-- Fixed-order truncation drops the whole homogeneous product above the
order. It never rescales the retained kernel. -/
def truncatedHomogeneousProduct (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) {r s r' s' : ℕ} (first : canonicalKernels primary body r s)
    (second : canonicalKernels primary body r' s') :
    canonicalKernels primary body (r + r') (s + s') :=
  if r + r' + (s + s') ≤ order then homogeneousProduct primary body first second else 0

theorem truncatedHomogeneousProduct_retained (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) {r s r' s' : ℕ} (first : canonicalKernels primary body r s)
    (second : canonicalKernels primary body r' s') (hdegree : r + r' + (s + s') ≤ order) :
    truncatedHomogeneousProduct primary body order first second = homogeneousProduct primary body first second := by
  simp only [truncatedHomogeneousProduct, if_pos hdegree]

theorem truncatedHomogeneousProduct_dropped (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) {r s r' s' : ℕ} (first : canonicalKernels primary body r s)
    (second : canonicalKernels primary body r' s') (hdegree : order < r + r' + (s + s')) :
    truncatedHomogeneousProduct primary body order first second = 0 := by
  simp only [truncatedHomogeneousProduct, if_neg (by omega : ¬r + r' + (s + s') ≤ order)]

/-- The separate permutation average uses both full factorial normalizers.
There are no omitted permutations when slot labels or colors repeat. -/
theorem homogeneousProduct_apply (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s r' s' : ℕ} (first : canonicalKernels primary body r s)
    (second : canonicalKernels primary body r' s')
    (colors : Fin (r + r') → Primary) (centers : Fin (s + s') → Body) :
    (homogeneousProduct primary body first second).val colors centers =
      ((r + r').factorial : ℝ)⁻¹ * ((s + s').factorial : ℝ)⁻¹ *
        ∑ primaryOrder : Equiv.Perm (Fin (r + r')), ∑ bodyOrder : Equiv.Perm (Fin (s + s')),
          finDisjointTensor first.val second.val (colors ∘ primaryOrder) (centers ∘ bodyOrder) := by
  exact (symmetrize_apply (finDisjointTensor first.val second.val) colors centers).trans (by
    simp only [Fintype.card_perm, Fintype.card_fin])

/-- Block swapping between the manuscript's ordered total-slot labels. -/
def finBlockSwap (left right : ℕ) : Fin (left + right) ≃ Fin (right + left) :=
  finSumFinEquiv.symm.trans ((Equiv.sumComm (Fin left) (Fin right)).trans finSumFinEquiv)

omit [Fintype Primary] [Fintype Body] in
theorem finDisjointTensor_swap {r s r' s' : ℕ}
    (first : DensityKernel (Primary := Primary) (Body := Body) r s)
    (second : DensityKernel (Primary := Primary) (Body := Body) r' s') :
    reindexKernel (finBlockSwap r r') (finBlockSwap s s') (finDisjointTensor first second) =
      finDisjointTensor second first := by
  funext colors centers
  simp only [finDisjointTensor, reindexKernel, disjointTensor, Function.comp_def,
    finBlockSwap, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.sumComm_apply,
    Sum.swap, Sum.elim_inl, Sum.elim_inr]
  ring

/-- The actual homogeneous product is commutative after its explicit block
swap; this is proved from the permutation averages and raw tensors. -/
theorem homogeneousProduct_comm (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s r' s' : ℕ} (first : canonicalKernels primary body r s)
    (second : canonicalKernels primary body r' s') :
    reindexKernel (finBlockSwap r r') (finBlockSwap s s')
        (homogeneousProduct primary body first second).val =
      (homogeneousProduct primary body second first).val := by
  change reindexKernel _ _ (symmetrize (finDisjointTensor first.val second.val)) =
    symmetrize (finDisjointTensor second.val first.val)
  rw [reindexKernel_symmetrize, finDisjointTensor_swap]

/-- The degree-zero scalar unit is the actual constant density kernel. -/
def scalarUnit (primary : FiniteDist Primary) (body : FiniteDist Body) :
    canonicalKernels primary body 0 0 := by
  refine ⟨fun _ _ => 1, ?_, ?_, ?_⟩
  · intro index
    exact Fin.elim0 index
  · intro index
    exact Fin.elim0 index
  · unfold SeparatelySymmetric
    intros
    rfl

def finLeftUnit (count : ℕ) : Fin (0 + count) ≃ Fin count :=
  finSumFinEquiv.symm.trans (Equiv.emptySum (Fin 0) (Fin count))

def finRightUnit (count : ℕ) : Fin (count + 0) ≃ Fin count :=
  finSumFinEquiv.symm.trans (Equiv.sumEmpty (Fin count) (Fin 0))

theorem finDisjointTensor_unit_left (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s : ℕ} (kernel : canonicalKernels primary body r s) :
    reindexKernel (finLeftUnit r) (finLeftUnit s)
      (finDisjointTensor (scalarUnit primary body).val kernel.val) = kernel.val := by
  funext colors centers
  simp only [finDisjointTensor, reindexKernel, disjointTensor, scalarUnit,
    finLeftUnit, Function.comp_def, Equiv.trans_apply, Equiv.symm_apply_apply,
    Equiv.emptySum_apply_inr, one_mul]

theorem finDisjointTensor_unit_right (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s : ℕ} (kernel : canonicalKernels primary body r s) :
    reindexKernel (finRightUnit r) (finRightUnit s)
      (finDisjointTensor kernel.val (scalarUnit primary body).val) = kernel.val := by
  funext colors centers
  simp only [finDisjointTensor, reindexKernel, disjointTensor, scalarUnit,
    finRightUnit, Function.comp_def, Equiv.trans_apply, Equiv.symm_apply_apply,
    Equiv.sumEmpty_apply_inl, mul_one]

/-- Left multiplication by the real degree-zero unit fixes every canonical
kernel, after the explicit empty-block identification. -/
theorem homogeneousProduct_unit_left (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s : ℕ} (kernel : canonicalKernels primary body r s) :
    reindexKernel (finLeftUnit r) (finLeftUnit s)
      (homogeneousProduct primary body (scalarUnit primary body) kernel).val = kernel.val := by
  change reindexKernel _ _ (symmetrize (finDisjointTensor _ _)) = _
  rw [reindexKernel_symmetrize, finDisjointTensor_unit_left]
  exact symmetrize_of_symmetric kernel.val kernel.property.2.2

theorem homogeneousProduct_unit_right (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s : ℕ} (kernel : canonicalKernels primary body r s) :
    reindexKernel (finRightUnit r) (finRightUnit s)
      (homogeneousProduct primary body kernel (scalarUnit primary body)).val = kernel.val := by
  change reindexKernel _ _ (symmetrize (finDisjointTensor _ _)) = _
  rw [reindexKernel_symmetrize, finDisjointTensor_unit_right]
  exact symmetrize_of_symmetric kernel.val kernel.property.2.2

/-- The number of full permutations equals the number of unordered shuffles
times the permutations internal to the two selected blocks. -/
theorem factorial_shuffle_count (left right : ℕ) :
    (left + right).choose left * left.factorial * right.factorial = (left + right).factorial := by
  rw [Nat.choose_symm_add]
  exact Nat.add_choose_mul_factorial_mul_factorial left right

/-- Both pools carry their own shuffle and internal-permutation factors.
This is the exact combinatorial denominator of the full separate average. -/
theorem twoPool_shuffle_normalizer (r s r' s' : ℕ) :
    (((r + r').choose r : ℝ) * ((s + s').choose s : ℝ)) *
        ((r.factorial : ℝ) * (r'.factorial : ℝ) * (s.factorial : ℝ) * (s'.factorial : ℝ)) =
      ((r + r').factorial : ℝ) * ((s + s').factorial : ℝ) := by
  have hp : ((r + r').choose r : ℝ) * (r.factorial : ℝ) * (r'.factorial : ℝ) =
      ((r + r').factorial : ℝ) := by exact_mod_cast factorial_shuffle_count r r'
  have hb : ((s + s').choose s : ℝ) * (s.factorial : ℝ) * (s'.factorial : ℝ) =
      ((s + s').factorial : ℝ) := by exact_mod_cast factorial_shuffle_count s s'
  calc
    _ = (((r + r').choose r : ℝ) * (r.factorial : ℝ) * (r'.factorial : ℝ)) *
        (((s + s').choose s : ℝ) * (s.factorial : ℝ) * (s'.factorial : ℝ)) := by ring
    _ = _ := by rw [hp, hb]

end

end CurrentAFT.ControlProduct
