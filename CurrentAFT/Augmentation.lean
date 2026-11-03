import CurrentAFT.FamilyEvaluation

/-! # The actual scalar-coordinate algebra homomorphism -/

namespace CurrentAFT.Augmentation

open AFT ControlCoordinates ControlProduct GradedControlAlgebra
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

theorem arity_eq_zero (order : ℕ) (arity : TruncatedArity order)
    (hprimary : arity.val.1.val = 0) (hbody : arity.val.2.val = 0) :
    arity = zeroArity order := by
  apply Subtype.ext
  exact Prod.ext (Fin.ext hprimary) (Fin.ext hbody)

theorem product_zero_fiber (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (first second : KernelFamily primary body order) :
    (first * second) (zeroArity order) =
      homogeneousProduct primary body (first (zeroArity order)) (second (zeroArity order)) := by
  change familyProduct primary body order first second (zeroArity order) = _
  unfold familyProduct
  rw [Finset.sum_eq_single (zeroArity order)]
  · rw [Finset.sum_eq_single (zeroArity order)]
    · rw [dif_pos ⟨rfl, rfl⟩]
      rfl
    · intro right _ hright
      rw [dif_neg]
      intro hmatch
      apply hright
      apply arity_eq_zero order right <;> simp only [zeroArity, Fin.val_zero, zero_add] at hmatch
      · exact hmatch.1
      · exact hmatch.2
    · simp
  · intro left _ hleft
    apply Finset.sum_eq_zero
    intro right _
    rw [dif_neg]
    intro hmatch
    apply hleft
    apply arity_eq_zero order left <;> simp only [zeroArity, Fin.val_zero] at hmatch
    · omega
    · omega
  · simp

theorem scalarAt_product (primary : FiniteDist Primary) (body : FiniteDist Body)
    (first second : canonicalKernels primary body 0 0) :
    scalarAt primary body (homogeneousProduct primary body first second) =
      scalarAt primary body first * scalarAt primary body second := by
  have hconst (kernel : canonicalKernels primary body 0 0) :
      kernel = (scalarAt primary body kernel) • scalarUnit primary body := by
    rw [← scalarKernel_scalarAt primary body kernel]
    apply Subtype.ext
    funext colors centers
    simp only [scalarKernel, scalarUnit, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_one]
    rfl
  rw [hconst first, CommonQueueAssembly.homogeneousProduct_smul_left]
  have hunit : homogeneousProduct primary body (scalarUnit primary body) second = second := by
    apply Subtype.ext
    have h := homogeneousProduct_unit_left primary body second
    have hequiv : finLeftUnit 0 = Equiv.refl (Fin 0) := Subsingleton.elim _ _
    simpa only [hequiv, reindexKernel, Function.comp_id, Equiv.coe_refl] using h
  rw [hunit]
  simp only [scalarAt, scalarUnit, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_one]

def scalar (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (family : KernelFamily primary body order) : ℝ := scalarAt primary body (family (zeroArity order))

def scalarHom (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) :
    KernelFamily primary body order →ₐ[ℝ] ℝ where
  toFun := scalar primary body order
  map_zero' := rfl
  map_one' := by
    change scalarAt primary body ((familyUnit primary body order) (zeroArity order)) = 1
    rw [familyUnit, Pi.single_eq_same]
    rfl
  map_add' first second := rfl
  map_mul' first second := by
    change scalarAt primary body ((first * second) (zeroArity order)) = _
    rw [product_zero_fiber, scalarAt_product]
    rfl
  commutes' value := by
    rw [Algebra.algebraMap_eq_smul_one]
    change value * scalar primary body order 1 = value
    have hone : scalar primary body order (1 : KernelFamily primary body order) = 1 := by
      change scalarAt primary body ((familyUnit primary body order) (zeroArity order)) = 1
      rw [familyUnit, Pi.single_eq_same]
      rfl
    rw [hone, mul_one]

theorem zero_fiber_eq_iff_scalar_eq (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (first second : KernelFamily primary body order) :
    first (zeroArity order) = second (zeroArity order) ↔
      scalarHom primary body order first = scalarHom primary body order second := by
  exact (scalarAt_injective primary body).eq_iff.symm

theorem product_unit_constant (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) {Index : Type*} (terms : Finset Index)
    (atoms : Index → KernelFamily primary body order)
    (hzero : ∀ index ∈ terms, atoms index (zeroArity order) = 0) :
    (∏ index ∈ terms, (1 + atoms index)) (zeroArity order) =
      (1 : KernelFamily primary body order) (zeroArity order) := by
  apply (zero_fiber_eq_iff_scalar_eq primary body order _ _).mpr
  rw [map_prod, map_one]
  apply Finset.prod_eq_one
  intro index hindex
  rw [map_add, map_one]
  have hscalar : scalarHom primary body order (atoms index) = 0 := by
    change scalarAt primary body (atoms index (zeroArity order)) = 0
    rw [hzero index hindex]
    rfl
  rw [hscalar, add_zero]

end

end CurrentAFT.Augmentation
