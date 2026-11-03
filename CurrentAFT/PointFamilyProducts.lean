import CurrentAFT.CompleteRaisingEvaluation
import CurrentAFT.CanonicalReconstruction

/-! Exact canonical-family products of centered point atoms. These are
identities of coefficient data, prior to any physical polynomial evaluation. -/
namespace CurrentAFT.PointFamilyProducts
open AFT ControlCoordinates ControlProduct CanonicalReconstruction GradedControlAlgebra BackgroundFamilies
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance finDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

def append {Color : Type*} {first second : ℕ} (left : Fin first → Color) (right : Fin second → Color) :
    Fin (first+second) → Color := fun index => Sum.elim left right (finSumFinEquiv.symm index)

theorem tensor_append (primary : FiniteDist Primary) (body : FiniteDist Body) {r s r' s' : ℕ}
    (first : Fin r → Primary) (second : Fin r' → Primary)
    (left : Fin s → Body) (right : Fin s' → Body) :
    finDisjointTensor (pointTensor primary body first left) (pointTensor primary body second right) =
      pointTensor primary body (append first second) (append left right) := by
  funext colors centers
  have hp := (finSumFinEquiv : (Fin r ⊕ Fin r') ≃ Fin (r+r')).prod_comp
    (fun index => Hoeffding.centeredAtom primary (append first second index) (colors index))
  have hb := (finSumFinEquiv : (Fin s ⊕ Fin s') ≃ Fin (s+s')).prod_comp
    (fun index => Hoeffding.centeredAtom body (append left right index) (centers index))
  simp only [append, Equiv.symm_apply_apply, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr] at hp hb
  simp only [pointTensor, append, ← hp, ← hb, finDisjointTensor, reindexKernel, disjointTensor,
    Function.comp_apply]
  ring

theorem kernel_append (primary : FiniteDist Primary) (body : FiniteDist Body)
    (hp : ∀ color, 0 < primary.weight color) (hb : ∀ color, 0 < body.weight color) {r s r' s' : ℕ}
    (first : Fin r → Primary) (second : Fin r' → Primary)
    (left : Fin s → Body) (right : Fin s' → Body) :
    homogeneousProduct primary body (pointKernel primary body hp hb first left)
      (pointKernel primary body hp hb second right) =
      pointKernel primary body hp hb (append first second) (append left right) := by
  apply Subtype.ext
  change symmetrize (finDisjointTensor (symmetrize (pointTensor primary body first left))
    (symmetrize (pointTensor primary body second right))) = _
  rw [finDisjointTensor, ← reindexKernel_symmetrize, symmetrizedTensor_first_symmetrize,
    symmetrizedTensor_second_symmetrize, reindexKernel_symmetrize]
  change symmetrize (finDisjointTensor (pointTensor primary body first left) (pointTensor primary body second right)) = _
  rw [tensor_append]
  rfl

def arity (order r s : ℕ) (h : r+s ≤ order) : TruncatedArity order :=
  ⟨(⟨r, by omega⟩, ⟨s, by omega⟩),h⟩

def pointFamily (primary : FiniteDist Primary) (body : FiniteDist Body)
    (hp : ∀ color, 0 < primary.weight color) (hb : ∀ color, 0 < body.weight color)
    (order : ℕ) {r s : ℕ} (h : r+s ≤ order) (colors : Fin r → Primary) (centers : Fin s → Body) :
    KernelFamily primary body order :=
  Pi.single (arity order r s h) (pointKernel primary body hp hb colors centers)

theorem pointFamily_mul (primary : FiniteDist Primary) (body : FiniteDist Body)
    (hp : ∀ color, 0 < primary.weight color) (hb : ∀ color, 0 < body.weight color)
    (order : ℕ) {r s r' s' : ℕ} (h : r+s ≤ order) (h' : r'+s' ≤ order)
    (htotal : (r+r')+(s+s') ≤ order)
    (first : Fin r → Primary) (second : Fin r' → Primary)
    (left : Fin s → Body) (right : Fin s' → Body) :
    pointFamily primary body hp hb order h first left * pointFamily primary body hp hb order h' second right =
      pointFamily primary body hp hb order htotal (append first second) (append left right) := by
  change familyProduct primary body order (pointFamily primary body hp hb order h first left)
    (pointFamily primary body hp hb order h' second right) = _
  unfold pointFamily
  rw [familyProduct_single_retained primary body order _ _ _ _ htotal, kernel_append]
  rfl

theorem pointFamily_zero (primary : FiniteDist Primary) (body : FiniteDist Body)
    (hp : ∀ color, 0 < primary.weight color) (hb : ∀ color, 0 < body.weight color) (order : ℕ)
    (h : 0+0 ≤ order) : pointFamily primary body hp hb order h Fin.elim0 Fin.elim0 = 1 := by
  have hk : pointKernel primary body hp hb (Fin.elim0 : Fin 0 → Primary) (Fin.elim0 : Fin 0 → Body) =
      scalarUnit primary body := by
    apply Subtype.ext
    change ControlProduct.symmetrize _ = _
    have ht : pointTensor primary body (Fin.elim0 : Fin 0 → Primary) (Fin.elim0 : Fin 0 → Body) =
        (scalarUnit primary body).val := by funext colors centers; simp [pointTensor, scalarUnit]
    rw [ht, symmetrize_of_symmetric _ (scalarUnit primary body).property.2.2]
  unfold pointFamily
  rw [hk]
  rfl

theorem primary_single (primary : FiniteDist Primary) (body : FiniteDist Body)
    (hp : ∀ color, 0 < primary.weight color) (hb : ∀ color, 0 < body.weight color)
    (order : ℕ) (horder : 1 ≤ order) (color : Primary) :
    primaryFamily primary body order horder (Hoeffding.centeredAtom primary color)
      (Hoeffding.centeredAtom_mean primary hp color) =
      pointFamily primary body hp hb order (by omega) (fun _ : Fin 1 => color) Fin.elim0 := by
  have hk : pointKernel primary body hp hb (fun _ : Fin 1 => color) (Fin.elim0 : Fin 0 → Body) =
      primaryKernel primary body (Hoeffding.centeredAtom primary color) (Hoeffding.centeredAtom_mean primary hp color) := by
    apply Subtype.ext
    have ht : pointTensor primary body (fun _ : Fin 1 => color) (Fin.elim0 : Fin 0 → Body) =
        (primaryKernel primary body (Hoeffding.centeredAtom primary color) (Hoeffding.centeredAtom_mean primary hp color)).val := by
      funext colors centers
      simp only [pointTensor, Fin.prod_univ_one, Fin.prod_univ_zero, mul_one, primaryKernel]
    change ControlProduct.symmetrize _ = _
    rw [ht, symmetrize_of_symmetric _ (primaryKernel primary body _ _).property.2.2]
  unfold primaryFamily pointFamily
  rw [hk]
  rfl

theorem body_single (primary : FiniteDist Primary) (body : FiniteDist Body)
    (hp : ∀ color, 0 < primary.weight color) (hb : ∀ color, 0 < body.weight color)
    (order : ℕ) (horder : 1 ≤ order) (color : Body) :
    bodyFamily primary body order horder (Hoeffding.centeredAtom body color)
      (Hoeffding.centeredAtom_mean body hb color) =
      pointFamily primary body hp hb order (by omega) Fin.elim0 (fun _ : Fin 1 => color) := by
  have hk : pointKernel primary body hp hb (Fin.elim0 : Fin 0 → Primary) (fun _ : Fin 1 => color) =
      bodyKernel primary body (Hoeffding.centeredAtom body color) (Hoeffding.centeredAtom_mean body hb color) := by
    apply Subtype.ext
    have ht : pointTensor primary body (Fin.elim0 : Fin 0 → Primary) (fun _ : Fin 1 => color) =
        (bodyKernel primary body (Hoeffding.centeredAtom body color) (Hoeffding.centeredAtom_mean body hb color)).val := by
      funext colors centers
      simp only [pointTensor, Fin.prod_univ_one, Fin.prod_univ_zero, one_mul, bodyKernel]
    change ControlProduct.symmetrize _ = _
    rw [ht, symmetrize_of_symmetric _ (bodyKernel primary body _ _).property.2.2]
  unfold bodyFamily pointFamily
  rw [hk]
  rfl

theorem append_last {Color : Type*} {count : ℕ} (word : Fin (count+1) → Color) :
    append (fun index => word index.castSucc) (fun _ : Fin 1 => word (Fin.last count)) = word := by
  funext index
  obtain ⟨left | right, rfl⟩ := (finSumFinEquiv : (Fin count ⊕ Fin 1) ≃ Fin (count+1)).surjective index
  · simp only [append, Equiv.symm_apply_apply, Sum.elim_inl]
    congr 1
  · have hr : right = 0 := Subsingleton.elim _ _
    subst right
    simp only [append, Equiv.symm_apply_apply, Sum.elim_inr]
    congr 1

theorem primary_prod (primary : FiniteDist Primary) (body : FiniteDist Body)
    (hp : ∀ color, 0 < primary.weight color) (hb : ∀ color, 0 < body.weight color)
    (order : ℕ) (horder : 1 ≤ order) (count : ℕ) (hcount : count ≤ order) (word : Fin count → Primary) :
    (∏ index, primaryFamily primary body order horder (Hoeffding.centeredAtom primary (word index))
      (Hoeffding.centeredAtom_mean primary hp (word index))) =
      pointFamily primary body hp hb order (by omega) word Fin.elim0 := by
  induction count with
  | zero =>
    have hw : word = Fin.elim0 := Subsingleton.elim _ _
    subst word
    rw [Fin.prod_univ_zero, pointFamily_zero]
  | succ count ih =>
    rw [Fin.prod_univ_castSucc, ih (by omega), primary_single primary body hp hb]
    rw [pointFamily_mul primary body hp hb order _ _ (by omega), append_last]
    congr 1
    funext index
    exact Fin.elim0 (show Fin 0 from index)

theorem body_prod (primary : FiniteDist Primary) (body : FiniteDist Body)
    (hp : ∀ color, 0 < primary.weight color) (hb : ∀ color, 0 < body.weight color)
    (order : ℕ) (horder : 1 ≤ order) (count : ℕ) (hcount : count ≤ order) (word : Fin count → Body) :
    (∏ index, bodyFamily primary body order horder (Hoeffding.centeredAtom body (word index))
      (Hoeffding.centeredAtom_mean body hb (word index))) =
      pointFamily primary body hp hb order (by omega) Fin.elim0 word := by
  induction count with
  | zero =>
    have hw : word = Fin.elim0 := Subsingleton.elim _ _
    subst word
    rw [Fin.prod_univ_zero, pointFamily_zero]
  | succ count ih =>
    rw [Fin.prod_univ_castSucc, ih (by omega), body_single primary body hp hb]
    rw [pointFamily_mul primary body hp hb order _ _ (by omega), append_last]
    congr 1
    funext index
    exact Fin.elim0 (show Fin 0 from index)

theorem pointFamily_cast (primary : FiniteDist Primary) (body : FiniteDist Body)
    (hp : ∀ color, 0 < primary.weight color) (hb : ∀ color, 0 < body.weight color)
    (order : ℕ) {r s r' s' : ℕ} (h' : r'+s' ≤ order) (hr : r'=r) (hs : s'=s) (h : r+s ≤ order)
    (colors : Fin r' → Primary) (centers : Fin s' → Body) :
    pointFamily primary body hp hb order h' colors centers =
      pointFamily primary body hp hb order h (fun index => colors (index.cast hr.symm))
        (fun index => centers (index.cast hs.symm)) := by
  subst r'
  subst s'
  rfl

theorem append_empty_right {Color : Type*} {count : ℕ} (word : Fin count → Color) (index : Fin count) :
    append word (Fin.elim0 : Fin 0 → Color) (index.cast (Nat.add_zero count).symm) = word index := by
  have he : index.cast (Nat.add_zero count).symm = finSumFinEquiv (.inl index : Fin count ⊕ Fin 0) := by
    apply Fin.ext
    rfl
  rw [he]
  simp only [append, Equiv.symm_apply_apply, Sum.elim_inl]

theorem append_empty_left {Color : Type*} {count : ℕ} (word : Fin count → Color) (index : Fin count) :
    append (Fin.elim0 : Fin 0 → Color) word (index.cast (Nat.zero_add count).symm) = word index := by
  have he : index.cast (Nat.zero_add count).symm = finSumFinEquiv (.inr index : Fin 0 ⊕ Fin count) := by
    apply Fin.ext
    simp
  rw [he]
  simp only [append, Equiv.symm_apply_apply, Sum.elim_inr]

theorem two_pool_prod (primary : FiniteDist Primary) (body : FiniteDist Body)
    (hp : ∀ color, 0 < primary.weight color) (hb : ∀ color, 0 < body.weight color)
    (order : ℕ) (horder : 1 ≤ order) {r s : ℕ} (hdegree : r+s ≤ order)
    (colors : Fin r → Primary) (centers : Fin s → Body) :
    (∏ index, primaryFamily primary body order horder (Hoeffding.centeredAtom primary (colors index))
      (Hoeffding.centeredAtom_mean primary hp (colors index))) *
    (∏ index, bodyFamily primary body order horder (Hoeffding.centeredAtom body (centers index))
      (Hoeffding.centeredAtom_mean body hb (centers index))) =
      pointFamily primary body hp hb order hdegree colors centers := by
  rw [primary_prod primary body hp hb order horder r (by omega),
    body_prod primary body hp hb order horder s (by omega)]
  rw [pointFamily_mul primary body hp hb order _ _ (by omega),
    pointFamily_cast primary body hp hb order _ (Nat.add_zero r) (Nat.zero_add s) hdegree]
  simp only [append_empty_right, append_empty_left]

end
end CurrentAFT.PointFamilyProducts
