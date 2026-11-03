import CurrentAFT.ControlNorm
import CurrentAFT.ControlCoherence

/-!
# Finite arity families and their actual truncated coefficient convolution

The coefficient space is represented by all canonical kernel fibers at
arities of total degree at most the fixed order, including degree zero.
The explicit linear equivalence below identifies this finite family with
`ControlCoordinates.CoefficientSpace`, whose scalar is stored separately.
Multiplication is an actual finite arity convolution of the already proved
homogeneous disjoint-slot products. No algebra law is included as a field
or used as a hypothesis.
-/

namespace CurrentAFT.GradedControlAlgebra

open AFT ControlCoordinates ControlProduct ControlNorm
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

abbrev TruncatedArity (order : ℕ) :=
  {arity : Fin (order + 1) × Fin (order + 1) // arity.1.val + arity.2.val ≤ order}

def zeroArity (order : ℕ) : TruncatedArity order := ⟨(0, 0), by simp⟩

def positiveArity (order : ℕ) (arity : PositiveArity order) : TruncatedArity order :=
  ⟨arity.val, arity.property.2⟩

abbrev KernelFamily (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) :=
  (arity : TruncatedArity order) → canonicalKernels primary body arity.val.1.val arity.val.2.val

instance kernelFamily_finiteDimensional (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) : FiniteDimensional ℝ (KernelFamily primary body order) := by infer_instance

def scalarKernel (primary : FiniteDist Primary) (body : FiniteDist Body) (scalar : ℝ) :
    canonicalKernels primary body 0 0 := by
  refine ⟨fun _ _ => scalar, ?_, ?_, ?_⟩
  · intro index
    exact Fin.elim0 index
  · intro index
    exact Fin.elim0 index
  · unfold SeparatelySymmetric
    intros
    rfl

def scalarAt (primary : FiniteDist Primary) (body : FiniteDist Body)
    (kernel : canonicalKernels primary body 0 0) : ℝ :=
  kernel.val Fin.elim0 Fin.elim0

theorem scalarKernel_scalarAt (primary : FiniteDist Primary) (body : FiniteDist Body)
    (kernel : canonicalKernels primary body 0 0) :
    scalarKernel primary body (scalarAt primary body kernel) = kernel := by
  apply Subtype.ext
  funext colors centers
  have hc : colors = (Fin.elim0 : Fin 0 → Primary) := Subsingleton.elim _ _
  have hb : centers = (Fin.elim0 : Fin 0 → Body) := Subsingleton.elim _ _
  simp only [scalarKernel, scalarAt, hc, hb]

theorem scalarAt_injective (primary : FiniteDist Primary) (body : FiniteDist Body) :
    Function.Injective (scalarAt primary body) := by
  intro first second hequal
  rw [← scalarKernel_scalarAt primary body first, ← scalarKernel_scalarAt primary body second, hequal]

/-- Evaluate the zero fiber and retain every positive canonical kernel. -/
def familyToCoefficients (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) :
    KernelFamily primary body order →ₗ[ℝ] CoefficientSpace primary body order where
  toFun family := (scalarAt primary body (family (zeroArity order)),
    fun arity => family (positiveArity order arity))
  map_add' first second := by
    apply Prod.ext
    · rfl
    · funext arity
      rfl
  map_smul' scalar family := by
    apply Prod.ext
    · rfl
    · funext arity
      rfl

/-- Reconstruct the zero kernel from the scalar; positive fibers are copied
without choosing a tensor basis or adding unconstrained higher arities. -/
def coefficientsToFamily (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (coefficient : CoefficientSpace primary body order) : KernelFamily primary body order := by
  intro arity
  rcases arity with ⟨⟨⟨r, hr⟩, ⟨s, hs⟩⟩, hdegree⟩
  by_cases hzero : r + s = 0
  · have hrzero : r = 0 := by omega
    have hszero : s = 0 := by omega
    subst r
    subst s
    exact scalarKernel primary body coefficient.1
  · exact coefficient.2 ⟨(⟨r, hr⟩, ⟨s, hs⟩), ⟨by change 1 ≤ r + s; omega, hdegree⟩⟩

theorem coefficientsToFamily_zero (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (coefficient : CoefficientSpace primary body order) :
    coefficientsToFamily primary body order coefficient (zeroArity order) =
      scalarKernel primary body coefficient.1 := by
  rfl

theorem coefficientsToFamily_positive (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (coefficient : CoefficientSpace primary body order) (arity : PositiveArity order) :
    coefficientsToFamily primary body order coefficient (positiveArity order arity) = coefficient.2 arity := by
  rcases arity with ⟨⟨⟨r, hr⟩, ⟨s, hs⟩⟩, hdegree⟩
  have hpositive : 1 ≤ r + s := hdegree.1
  have hzero : ¬r + s = 0 := by omega
  simp only [coefficientsToFamily, positiveArity, dif_neg hzero]

theorem familyToCoefficients_injective (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) : Function.Injective (familyToCoefficients primary body order) := by
  intro first second hequal
  funext arity
  by_cases hzero : arity.val.1.val + arity.val.2.val = 0
  · have harity : arity = zeroArity order := by
      apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext
      · change arity.val.1.val = 0
        omega
      · change arity.val.2.val = 0
        omega
    subst arity
    apply scalarAt_injective primary body
    exact congrArg Prod.fst hequal
  · let positive : PositiveArity order := ⟨arity.val, ⟨by omega, arity.property⟩⟩
    exact congrArg (fun coefficient => coefficient.2 positive) hequal

theorem familyToCoefficients_surjective (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) : Function.Surjective (familyToCoefficients primary body order) := by
  intro coefficient
  refine ⟨coefficientsToFamily primary body order coefficient, ?_⟩
  apply Prod.ext
  · change scalarAt primary body (coefficientsToFamily primary body order coefficient (zeroArity order)) = coefficient.1
    rw [coefficientsToFamily_zero]
    rfl
  · funext arity
    exact coefficientsToFamily_positive primary body order coefficient arity

/-- An actual linear equivalence with the current scalar-plus-positive-kernel
coefficient space, rather than a new abstract algebra representation. -/
def familyCoefficientEquiv (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) :
    KernelFamily primary body order ≃ₗ[ℝ] CoefficientSpace primary body order :=
  LinearEquiv.ofBijective (familyToCoefficients primary body order)
    ⟨familyToCoefficients_injective primary body order, familyToCoefficients_surjective primary body order⟩

/-- Equality transport between fibers is only a relabeling of their finite
ordered slot types; it adds no new kernel values. -/
def transportKernel (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s r' s' : ℕ} (hr : r = r') (hs : s = s')
    (kernel : canonicalKernels primary body r s) : canonicalKernels primary body r' s' := by
  subst r'
  subst s'
  exact kernel

theorem transportKernel_zero (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s r' s' : ℕ} (hr : r = r') (hs : s = s') :
    transportKernel primary body hr hs (0 : canonicalKernels primary body r s) = 0 := by
  subst r'
  subst s'
  rfl

theorem transportKernel_add (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s r' s' : ℕ} (hr : r = r') (hs : s = s') (first second : canonicalKernels primary body r s) :
    transportKernel primary body hr hs (first + second) =
      transportKernel primary body hr hs first + transportKernel primary body hr hs second := by
  subst r'
  subst s'
  rfl

theorem transportKernel_smul (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s r' s' : ℕ} (hr : r = r') (hs : s = s') (scalar : ℝ) (kernel : canonicalKernels primary body r s) :
    transportKernel primary body hr hs (scalar • kernel) = scalar • transportKernel primary body hr hs kernel := by
  subst r'
  subst s'
  rfl

theorem transportKernel_val (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s r' s' : ℕ} (hr : r = r') (hs : s = s') (kernel : canonicalKernels primary body r s) :
    (transportKernel primary body hr hs kernel).val = reindexKernel (finCongr hr) (finCongr hs) kernel.val := by
  subst r'
  subst s'
  rfl

theorem transportKernel_comp (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s r' s' r'' s'' : ℕ} (hr : r = r') (hs : s = s') (hr' : r' = r'') (hs' : s' = s'')
    (kernel : canonicalKernels primary body r s) :
    transportKernel primary body hr' hs' (transportKernel primary body hr hs kernel) =
      transportKernel primary body (hr.trans hr') (hs.trans hs') kernel := by
  subst r'
  subst s'
  subst r''
  subst s''
  rfl

theorem transport_homogeneousProduct_comm (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s r' s' targetR targetS : ℕ}
    (hr : r + r' = targetR) (hs : s + s' = targetS)
    (hr' : r' + r = targetR) (hs' : s' + s = targetS)
    (first : canonicalKernels primary body r s) (second : canonicalKernels primary body r' s') :
    transportKernel primary body hr hs (homogeneousProduct primary body first second) =
      transportKernel primary body hr' hs' (homogeneousProduct primary body second first) := by
  have hcomm : transportKernel primary body (Nat.add_comm r r') (Nat.add_comm s s')
      (homogeneousProduct primary body first second) = homogeneousProduct primary body second first := by
    apply Subtype.ext
    rw [transportKernel_val]
    exact ControlCoherence.homogeneousProduct_comm_cast primary body first second
  calc
    _ = transportKernel primary body hr' hs'
        (transportKernel primary body (Nat.add_comm r r') (Nat.add_comm s s')
          (homogeneousProduct primary body first second)) := by rw [transportKernel_comp]
    _ = _ := by rw [hcomm]

theorem transport_homogeneousProduct_unit_left (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s : ℕ} (kernel : canonicalKernels primary body r s) :
    transportKernel primary body (Nat.zero_add r) (Nat.zero_add s)
      (homogeneousProduct primary body (scalarUnit primary body) kernel) = kernel := by
  apply Subtype.ext
  rw [transportKernel_val]
  apply Eq.trans _ (homogeneousProduct_unit_left primary body kernel)
  exact ControlCoherence.symmetric_reindex_unique _ _ _ _ _
    (homogeneousProduct primary body (scalarUnit primary body) kernel).property.2.2

theorem transport_homogeneousProduct_unit_right (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s : ℕ} (kernel : canonicalKernels primary body r s) :
    transportKernel primary body (Nat.add_zero r) (Nat.add_zero s)
      (homogeneousProduct primary body kernel (scalarUnit primary body)) = kernel := by
  apply Subtype.ext
  rw [transportKernel_val]
  apply Eq.trans _ (homogeneousProduct_unit_right primary body kernel)
  exact ControlCoherence.symmetric_reindex_unique _ _ _ _ _
    (homogeneousProduct primary body kernel (scalarUnit primary body)).property.2.2

theorem homogeneousProduct_zero_left (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s r' s' : ℕ} (second : canonicalKernels primary body r' s') :
    homogeneousProduct primary body (0 : canonicalKernels primary body r s) second = 0 := by
  apply Subtype.ext
  funext colors centers
  simp only [homogeneousProduct, symmetrize_apply, finDisjointTensor, reindexKernel,
    disjointTensor, Submodule.coe_zero, Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero]

theorem homogeneousProduct_zero_right (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s r' s' : ℕ} (first : canonicalKernels primary body r s) :
    homogeneousProduct primary body first (0 : canonicalKernels primary body r' s') = 0 := by
  apply Subtype.ext
  funext colors centers
  simp only [homogeneousProduct, symmetrize_apply, finDisjointTensor, reindexKernel,
    disjointTensor, Submodule.coe_zero, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

theorem homogeneousProduct_add_left (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s r' s' : ℕ} (first other : canonicalKernels primary body r s)
    (second : canonicalKernels primary body r' s') :
    homogeneousProduct primary body (first + other) second =
      homogeneousProduct primary body first second + homogeneousProduct primary body other second := by
  apply Subtype.ext
  funext colors centers
  simp only [homogeneousProduct, symmetrize_apply, finDisjointTensor, reindexKernel,
    disjointTensor, Submodule.coe_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

theorem homogeneousProduct_add_right (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s r' s' : ℕ} (first : canonicalKernels primary body r s)
    (second other : canonicalKernels primary body r' s') :
    homogeneousProduct primary body first (second + other) =
      homogeneousProduct primary body first second + homogeneousProduct primary body first other := by
  apply Subtype.ext
  funext colors centers
  simp only [homogeneousProduct, symmetrize_apply, finDisjointTensor, reindexKernel,
    disjointTensor, Submodule.coe_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- The actual arity convolution. All summands use disjoint-slot multiplication,
and only output arities of total degree at most the fixed order exist. -/
def familyProduct (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (first second : KernelFamily primary body order) : KernelFamily primary body order :=
  fun output => ∑ left : TruncatedArity order, ∑ right : TruncatedArity order,
    if hmatch : left.val.1.val + right.val.1.val = output.val.1.val ∧
        left.val.2.val + right.val.2.val = output.val.2.val then
      transportKernel primary body hmatch.1 hmatch.2
        (homogeneousProduct primary body (first left) (second right))
    else 0

theorem familyProduct_zero_left (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (second : KernelFamily primary body order) : familyProduct primary body order 0 second = 0 := by
  funext output
  simp only [familyProduct, Pi.zero_apply, homogeneousProduct_zero_left,
    transportKernel_zero, dite_eq_ite, ite_self, Finset.sum_const_zero]

theorem familyProduct_zero_right (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (first : KernelFamily primary body order) : familyProduct primary body order first 0 = 0 := by
  funext output
  simp only [familyProduct, Pi.zero_apply, homogeneousProduct_zero_right,
    transportKernel_zero, dite_eq_ite, ite_self, Finset.sum_const_zero]

theorem familyProduct_add_left (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (first other second : KernelFamily primary body order) :
    familyProduct primary body order (first + other) second =
      familyProduct primary body order first second + familyProduct primary body order other second := by
  funext output
  simp only [familyProduct, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro left _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro right _
  split_ifs with hmatch
  · rw [homogeneousProduct_add_left, transportKernel_add]
  · exact (add_zero 0).symm

theorem familyProduct_add_right (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (first second other : KernelFamily primary body order) :
    familyProduct primary body order first (second + other) =
      familyProduct primary body order first second + familyProduct primary body order first other := by
  funext output
  simp only [familyProduct, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro left _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro right _
  split_ifs with hmatch
  · rw [homogeneousProduct_add_right, transportKernel_add]
  · exact (add_zero 0).symm

theorem familyProduct_comm (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (first second : KernelFamily primary body order) :
    familyProduct primary body order first second = familyProduct primary body order second first := by
  funext output
  unfold familyProduct
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro right _
  apply Finset.sum_congr rfl
  intro left _
  split_ifs with hforward hreverse hreverse
  · exact transport_homogeneousProduct_comm primary body hforward.1 hforward.2 hreverse.1 hreverse.2 _ _
  · exfalso
    apply hreverse
    constructor <;> omega
  · exfalso
    apply hforward
    constructor <;> omega
  · rfl

def familyUnit (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) :
    KernelFamily primary body order := Pi.single (zeroArity order) (scalarUnit primary body)

theorem familyProduct_unit_left (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (family : KernelFamily primary body order) :
    familyProduct primary body order (familyUnit primary body order) family = family := by
  funext output
  unfold familyProduct familyUnit
  rw [Finset.sum_eq_single (zeroArity order)]
  · rw [Pi.single_eq_same, Finset.sum_eq_single output]
    · rw [dif_pos (by constructor <;> exact Nat.zero_add _)]
      exact transport_homogeneousProduct_unit_left primary body (family output)
    · intro other _ hother
      rw [dif_neg]
      · intro hmatch
        apply hother
        apply Subtype.ext
        apply Prod.ext <;> apply Fin.ext
        · have := hmatch.1
          simpa only [zeroArity, Fin.val_zero, zero_add] using this
        · have := hmatch.2
          simpa only [zeroArity, Fin.val_zero, zero_add] using this
    · simp
  · intro other _ hother
    rw [Pi.single_eq_of_ne (M := fun arity : TruncatedArity order =>
      canonicalKernels primary body arity.val.1.val arity.val.2.val) hother (scalarUnit primary body)]
    apply Finset.sum_eq_zero
    intro right _
    split_ifs <;> simp only [homogeneousProduct_zero_left, transportKernel_zero]
  · simp

theorem familyProduct_unit_right (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (family : KernelFamily primary body order) :
    familyProduct primary body order family (familyUnit primary body order) = family := by
  rw [familyProduct_comm, familyProduct_unit_left]

theorem familyProduct_single (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (left right output : TruncatedArity order)
    (first : canonicalKernels primary body left.val.1.val left.val.2.val)
    (second : canonicalKernels primary body right.val.1.val right.val.2.val) :
    familyProduct primary body order (Pi.single left first) (Pi.single right second) output =
      if hmatch : left.val.1.val + right.val.1.val = output.val.1.val ∧
          left.val.2.val + right.val.2.val = output.val.2.val then
        transportKernel primary body hmatch.1 hmatch.2 (homogeneousProduct primary body first second)
      else 0 := by
  unfold familyProduct
  rw [Finset.sum_eq_single left]
  · rw [Pi.single_eq_same, Finset.sum_eq_single right]
    · rw [Pi.single_eq_same]
    · intro other _ hother
      rw [Pi.single_eq_of_ne (M := fun arity : TruncatedArity order =>
        canonicalKernels primary body arity.val.1.val arity.val.2.val) hother second]
      split_ifs <;> simp only [homogeneousProduct_zero_right, transportKernel_zero]
    · simp
  · intro other _ hother
    rw [Pi.single_eq_of_ne (M := fun arity : TruncatedArity order =>
      canonicalKernels primary body arity.val.1.val arity.val.2.val) hother first]
    apply Finset.sum_eq_zero
    intro otherRight _
    split_ifs <;> simp only [homogeneousProduct_zero_left, transportKernel_zero]
  · simp

def sumArity (order : ℕ) (left right : TruncatedArity order)
    (hdegree : (left.val.1.val + right.val.1.val) + (left.val.2.val + right.val.2.val) ≤ order) :
    TruncatedArity order :=
  ⟨(⟨left.val.1.val + right.val.1.val, by omega⟩,
    ⟨left.val.2.val + right.val.2.val, by omega⟩), hdegree⟩

theorem familyProduct_single_retained (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (left right : TruncatedArity order)
    (first : canonicalKernels primary body left.val.1.val left.val.2.val)
    (second : canonicalKernels primary body right.val.1.val right.val.2.val)
    (hdegree : (left.val.1.val + right.val.1.val) + (left.val.2.val + right.val.2.val) ≤ order) :
    familyProduct primary body order (Pi.single left first) (Pi.single right second) =
      Pi.single (sumArity order left right hdegree) (homogeneousProduct primary body first second) := by
  funext output
  rw [familyProduct_single]
  by_cases hequal : output = sumArity order left right hdegree
  · subst output
    rw [Pi.single_eq_same, dif_pos ⟨rfl, rfl⟩]
    rfl
  · rw [Pi.single_eq_of_ne (M := fun arity : TruncatedArity order =>
      canonicalKernels primary body arity.val.1.val arity.val.2.val) hequal]
    rw [dif_neg]
    intro hmatch
    apply hequal
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · exact hmatch.1.symm
    · exact hmatch.2.symm

theorem familyProduct_single_dropped (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (left right : TruncatedArity order)
    (first : canonicalKernels primary body left.val.1.val left.val.2.val)
    (second : canonicalKernels primary body right.val.1.val right.val.2.val)
    (hdegree : order < (left.val.1.val + right.val.1.val) + (left.val.2.val + right.val.2.val)) :
    familyProduct primary body order (Pi.single left first) (Pi.single right second) = 0 := by
  funext output
  rw [familyProduct_single]
  rw [dif_neg (by
    intro hmatch
    have houtput := output.property
    omega)]
  rfl

private theorem single_eq_of_transport (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    {left right : TruncatedArity order}
    (hr : left.val.1.val = right.val.1.val) (hs : left.val.2.val = right.val.2.val)
    (first : canonicalKernels primary body left.val.1.val left.val.2.val)
    (second : canonicalKernels primary body right.val.1.val right.val.2.val)
    (hequal : transportKernel primary body hr hs first = second) :
    (Pi.single left first : KernelFamily primary body order) = Pi.single right second := by
  have harity : left = right := by
    apply Subtype.ext
    exact Prod.ext (Fin.ext hr) (Fin.ext hs)
  subst right
  have hkernel : first = second := hequal
  rw [hkernel]

theorem familyProduct_single_assoc (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (left middle right : TruncatedArity order)
    (first : canonicalKernels primary body left.val.1.val left.val.2.val)
    (second : canonicalKernels primary body middle.val.1.val middle.val.2.val)
    (third : canonicalKernels primary body right.val.1.val right.val.2.val) :
    familyProduct primary body order
        (familyProduct primary body order (Pi.single left first) (Pi.single middle second)) (Pi.single right third) =
      familyProduct primary body order (Pi.single left first)
        (familyProduct primary body order (Pi.single middle second) (Pi.single right third)) := by
  by_cases htotal : (left.val.1.val + middle.val.1.val + right.val.1.val) +
      (left.val.2.val + middle.val.2.val + right.val.2.val) ≤ order
  · have hleft : (left.val.1.val + middle.val.1.val) + (left.val.2.val + middle.val.2.val) ≤ order := by omega
    have hright : (middle.val.1.val + right.val.1.val) + (middle.val.2.val + right.val.2.val) ≤ order := by omega
    have hlaterLeft : ((sumArity order left middle hleft).val.1.val + right.val.1.val) +
        ((sumArity order left middle hleft).val.2.val + right.val.2.val) ≤ order := htotal
    have hlaterRight : (left.val.1.val + (sumArity order middle right hright).val.1.val) +
        (left.val.2.val + (sumArity order middle right hright).val.2.val) ≤ order := by
      dsimp only [sumArity]
      omega
    rw [familyProduct_single_retained primary body order left middle first second hleft,
      familyProduct_single_retained primary body order middle right second third hright,
      familyProduct_single_retained primary body order _ right _ third hlaterLeft,
      familyProduct_single_retained primary body order left _ first _ hlaterRight]
    apply single_eq_of_transport primary body order
      (Nat.add_assoc _ _ _) (Nat.add_assoc _ _ _)
    apply Subtype.ext
    rw [transportKernel_val]
    exact ControlCoherence.homogeneousProduct_assoc primary body first second third
  · have hleftZero : familyProduct primary body order
        (familyProduct primary body order (Pi.single left first) (Pi.single middle second)) (Pi.single right third) = 0 := by
      by_cases hleft : (left.val.1.val + middle.val.1.val) + (left.val.2.val + middle.val.2.val) ≤ order
      · rw [familyProduct_single_retained primary body order left middle first second hleft]
        apply familyProduct_single_dropped
        dsimp only [sumArity]
        omega
      · rw [familyProduct_single_dropped primary body order left middle first second (by omega), familyProduct_zero_left]
    have hrightZero : familyProduct primary body order (Pi.single left first)
        (familyProduct primary body order (Pi.single middle second) (Pi.single right third)) = 0 := by
      by_cases hright : (middle.val.1.val + right.val.1.val) + (middle.val.2.val + right.val.2.val) ≤ order
      · rw [familyProduct_single_retained primary body order middle right second third hright]
        apply familyProduct_single_dropped
        dsimp only [sumArity]
        omega
      · rw [familyProduct_single_dropped primary body order middle right second third (by omega), familyProduct_zero_right]
    rw [hleftZero, hrightZero]

theorem familyProduct_sum_left {Index : Type*} (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (terms : Finset Index) (family : Index → KernelFamily primary body order)
    (second : KernelFamily primary body order) :
    familyProduct primary body order (∑ index ∈ terms, family index) second =
      ∑ index ∈ terms, familyProduct primary body order (family index) second := by
  induction terms using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, familyProduct_zero_left]
  | @insert index terms hnot ih =>
    rw [Finset.sum_insert hnot, familyProduct_add_left, ih, Finset.sum_insert hnot]

theorem familyProduct_sum_right {Index : Type*} (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (terms : Finset Index) (family : Index → KernelFamily primary body order)
    (first : KernelFamily primary body order) :
    familyProduct primary body order first (∑ index ∈ terms, family index) =
      ∑ index ∈ terms, familyProduct primary body order first (family index) := by
  rw [familyProduct_comm, familyProduct_sum_left]
  apply Finset.sum_congr rfl
  intro index _
  exact familyProduct_comm primary body order _ _

def familyLeftAddHom (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (second : KernelFamily primary body order) : KernelFamily primary body order →+ KernelFamily primary body order where
  toFun first := familyProduct primary body order first second
  map_zero' := familyProduct_zero_left primary body order second
  map_add' first other := familyProduct_add_left primary body order first other second

def familyRightAddHom (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (first : KernelFamily primary body order) : KernelFamily primary body order →+ KernelFamily primary body order where
  toFun second := familyProduct primary body order first second
  map_zero' := familyProduct_zero_right primary body order first
  map_add' second other := familyProduct_add_right primary body order first second other

private theorem familyAddHom_ext_single (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (first second : KernelFamily primary body order →+ KernelFamily primary body order)
    (hsingle : ∀ (arity : TruncatedArity order)
      (kernel : canonicalKernels primary body arity.val.1.val arity.val.2.val),
      first (Pi.single arity kernel) = second (Pi.single arity kernel)) : first = second := by
  apply AddMonoidHom.ext
  intro family
  rw [← Finset.univ_sum_single family, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro arity _
  exact hsingle arity (family arity)

/-- Associativity of the actual finite truncated convolution. Expansion into
single-arity families reduces it to the proved homogeneous associativity;
when total degree is too large, both bracketings vanish. -/
theorem familyProduct_assoc (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (first second third : KernelFamily primary body order) :
    familyProduct primary body order (familyProduct primary body order first second) third =
      familyProduct primary body order first (familyProduct primary body order second third) := by
  have hthird (left middle : TruncatedArity order)
      (f : canonicalKernels primary body left.val.1.val left.val.2.val)
      (g : canonicalKernels primary body middle.val.1.val middle.val.2.val)
      (third : KernelFamily primary body order) :
      familyProduct primary body order
        (familyProduct primary body order (Pi.single left f) (Pi.single middle g)) third =
      familyProduct primary body order (Pi.single left f)
        (familyProduct primary body order (Pi.single middle g) third) := by
    let lhs := familyRightAddHom primary body order
      (familyProduct primary body order (Pi.single left f) (Pi.single middle g))
    let rhs := (familyRightAddHom primary body order (Pi.single left f)).comp
      (familyRightAddHom primary body order (Pi.single middle g))
    have hequal : lhs = rhs := familyAddHom_ext_single primary body order lhs rhs
      (fun right h => familyProduct_single_assoc primary body order left middle right f g h)
    exact DFunLike.congr_fun hequal third
  have hsecond (left : TruncatedArity order)
      (f : canonicalKernels primary body left.val.1.val left.val.2.val)
      (second third : KernelFamily primary body order) :
      familyProduct primary body order (familyProduct primary body order (Pi.single left f) second) third =
      familyProduct primary body order (Pi.single left f) (familyProduct primary body order second third) := by
    let lhs := (familyLeftAddHom primary body order third).comp
      (familyRightAddHom primary body order (Pi.single left f))
    let rhs := (familyRightAddHom primary body order (Pi.single left f)).comp
      (familyLeftAddHom primary body order third)
    have hequal : lhs = rhs := familyAddHom_ext_single primary body order lhs rhs
      (fun middle g => hthird left middle f g third)
    exact DFunLike.congr_fun hequal second
  let lhs := (familyLeftAddHom primary body order third).comp (familyLeftAddHom primary body order second)
  let rhs := familyLeftAddHom primary body order (familyProduct primary body order second third)
  have hequal : lhs = rhs := familyAddHom_ext_single primary body order lhs rhs
    (fun left f => hsecond left f second third)
  exact DFunLike.congr_fun hequal first

instance familyOne (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) :
    One (KernelFamily primary body order) := ⟨familyUnit primary body order⟩

instance familyMul (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) :
    Mul (KernelFamily primary body order) := ⟨familyProduct primary body order⟩

instance familyNatCast (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) :
    NatCast (KernelFamily primary body order) := ⟨fun natural => natural • familyUnit primary body order⟩

instance familyIntCast (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) :
    IntCast (KernelFamily primary body order) := ⟨fun integer => integer • familyUnit primary body order⟩

/-- The ring operations are the actual finite kernel convolution proved
above. The existing pointwise additive-group structure is preserved. -/
instance familyCommRing (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) :
    CommRing (KernelFamily primary body order) where
  __ := inferInstanceAs (AddCommGroup (KernelFamily primary body order))
  mul := familyProduct primary body order
  one := familyUnit primary body order
  mul_assoc := familyProduct_assoc primary body order
  mul_comm := familyProduct_comm primary body order
  one_mul := familyProduct_unit_left primary body order
  mul_one := familyProduct_unit_right primary body order
  zero_mul := familyProduct_zero_left primary body order
  mul_zero := familyProduct_zero_right primary body order
  left_distrib := familyProduct_add_right primary body order
  right_distrib := familyProduct_add_left primary body order
  natCast natural := natural • familyUnit primary body order
  natCast_zero := zero_nsmul _
  natCast_succ natural := by
    change (natural + 1) • familyUnit primary body order =
      natural • familyUnit primary body order + familyUnit primary body order
    rw [add_nsmul, one_nsmul]
  intCast integer := integer • familyUnit primary body order
  intCast_ofNat natural := by
    change (natural : ℤ) • familyUnit primary body order = natural • familyUnit primary body order
    simp
  intCast_negSucc natural := by
    change (Int.negSucc natural) • familyUnit primary body order = -((natural + 1) • familyUnit primary body order)
    simp

/-- Convolution on the manuscript's original coefficient space, transported by
the proved finite-family equivalence. -/
def coefficientProduct (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (first second : CoefficientSpace primary body order) : CoefficientSpace primary body order :=
  familyCoefficientEquiv primary body order
    (familyProduct primary body order
      ((familyCoefficientEquiv primary body order).symm first)
      ((familyCoefficientEquiv primary body order).symm second))

def coefficientUnit (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) :
    CoefficientSpace primary body order :=
  familyCoefficientEquiv primary body order (familyUnit primary body order)

theorem coefficientProduct_comm (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (first second : CoefficientSpace primary body order) :
    coefficientProduct primary body order first second = coefficientProduct primary body order second first := by
  unfold coefficientProduct
  rw [familyProduct_comm]

theorem coefficientProduct_assoc (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (first second third : CoefficientSpace primary body order) :
    coefficientProduct primary body order (coefficientProduct primary body order first second) third =
      coefficientProduct primary body order first (coefficientProduct primary body order second third) := by
  unfold coefficientProduct
  simp only [LinearEquiv.symm_apply_apply]
  rw [familyProduct_assoc]

theorem coefficientProduct_unit_left (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (coefficient : CoefficientSpace primary body order) :
    coefficientProduct primary body order (coefficientUnit primary body order) coefficient = coefficient := by
  unfold coefficientProduct coefficientUnit
  rw [LinearEquiv.symm_apply_apply, familyProduct_unit_left, LinearEquiv.apply_symm_apply]

theorem coefficientProduct_unit_right (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (coefficient : CoefficientSpace primary body order) :
    coefficientProduct primary body order coefficient (coefficientUnit primary body order) = coefficient := by
  rw [coefficientProduct_comm, coefficientProduct_unit_left]

end

end CurrentAFT.GradedControlAlgebra
