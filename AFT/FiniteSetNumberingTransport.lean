import AFT.FiniteSetNumbering
import Mathlib.Order.Hom.Set

/-! # The sorted coordinate numbering commutes with explicit coordinate codes -/
namespace AFT

theorem finiteSetNumbering_refl {size : ℕ} (set : Finset (Fin size)) :
    finiteSetNumbering (Equiv.refl (Fin size)) set = (set.orderIsoOfFin rfl).toEquiv := by
  have he : LinearOrder.lift' (Equiv.refl (Fin size)) (Equiv.refl (Fin size)).injective =
      (inferInstance : LinearOrder (Fin size)) := LinearOrder.ext (fun _ _ => Iff.rfl)
  unfold finiteSetNumbering
  rw [he]

theorem finiteSetNumbering_eq_of_val {State : Type*} {firstSize secondSize : ℕ}
    (first : State ≃ Fin firstSize) (second : State ≃ Fin secondSize)
    (heq : ∀ point, (first point).val = (second point).val) (set : Finset State) :
    finiteSetNumbering first set = finiteSetNumbering second set := by
  have hord : LinearOrder.lift' first first.injective = LinearOrder.lift' second second.injective := by
    apply LinearOrder.ext
    intro left right
    change (first left).val ≤ (first right).val ↔ (second left).val ≤ (second right).val
    rw [heq left, heq right]
  unfold finiteSetNumbering
  rw [hord]

def finiteSetCodeEquiv {State : Type*} {size : ℕ}
    (index : State ≃ Fin size) (set : Finset State) :
    set ≃ set.map index.toEmbedding where
  toFun point := ⟨index point, Finset.mem_map.mpr ⟨point, point.property, rfl⟩⟩
  invFun point := ⟨index.symm point, by
    obtain ⟨source, hs, he⟩ := Finset.mem_map.mp point.property
    simpa only [← he, Equiv.toEmbedding_apply, Equiv.symm_apply_apply] using hs⟩
  left_inv point := by ext; exact index.symm_apply_apply point
  right_inv point := by apply Subtype.ext; exact index.apply_symm_apply point

theorem finiteSetNumbering_code {State : Type*} {size : ℕ}
    (index : State ≃ Fin size) (set : Finset State) (position : Fin set.card) :
    index (finiteSetNumbering index set position) =
      (finiteSetNumbering (Equiv.refl (Fin size)) (set.map index.toEmbedding)
        (Fin.cast (Finset.card_map index.toEmbedding).symm position)).val := by
  letI : LinearOrder State := LinearOrder.lift' index index.injective
  let code : set ≃o set.map index.toEmbedding :=
    { toEquiv := finiteSetCodeEquiv index set
      map_rel_iff' := by intro first second; rfl }
  let first : Fin set.card ≃o set.map index.toEmbedding :=
    (set.orderIsoOfFin rfl).trans code
  let second : Fin set.card ≃o set.map index.toEmbedding :=
    ((set.map index.toEmbedding).orderIsoOfFin (Finset.card_map index.toEmbedding))
  have he : first = second := Subsingleton.elim _ _
  exact congrArg (fun iso : Fin set.card ≃o set.map index.toEmbedding => (iso position).val) he

theorem finiteSetNumbering_code_of_eq {State : Type*} {size : ℕ}
    (index : State ≃ Fin size) (set : Finset State) (target : Finset (Fin size))
    (heq : set.map index.toEmbedding = target) (position : Fin set.card) :
    index (finiteSetNumbering index set position) =
      (finiteSetNumbering (Equiv.refl (Fin size)) target
        (Fin.cast (by rw [←heq, Finset.card_map]) position)).val := by
  subst target
  exact finiteSetNumbering_code index set position

@[simp] theorem finiteSetMatching_numbering {State : Type*} {size : ℕ}
    (index : State ≃ Fin size) (first second : Finset State)
    (hcard : first.card ≤ second.card) (position : Fin first.card) :
    finiteSetMatching index first second hcard (finiteSetNumbering index first position) =
      finiteSetNumbering index second (Fin.castLE hcard position) := by
  simp [finiteSetMatching]

theorem finiteSetMatching_code {State : Type*} {size : ℕ}
    (index : State ≃ Fin size) (first second : Finset State)
    (targetFirst targetSecond : Finset (Fin size))
    (hfirst : first.map index.toEmbedding = targetFirst)
    (hsecond : second.map index.toEmbedding = targetSecond)
    (hcard : first.card ≤ second.card) (htarget : targetFirst.card ≤ targetSecond.card)
    (point : first) :
    index (finiteSetMatching index first second hcard point) =
      (finiteSetMatching (Equiv.refl _) targetFirst targetSecond htarget
        ⟨index point, by rw [←hfirst]; exact Finset.mem_map.mpr ⟨point,point.property,rfl⟩⟩).val := by
  obtain ⟨position,rfl⟩ := (finiteSetNumbering index first).surjective point
  have hpoint : (⟨index (finiteSetNumbering index first position), by
      rw [←hfirst]; exact Finset.mem_map.mpr
        ⟨finiteSetNumbering index first position,(finiteSetNumbering index first position).property,rfl⟩⟩ : targetFirst) =
      finiteSetNumbering (Equiv.refl _) targetFirst
        (Fin.cast (by rw [←hfirst,Finset.card_map]) position) :=
    Subtype.ext (finiteSetNumbering_code_of_eq index first targetFirst hfirst position)
  rw [hpoint, finiteSetMatching_numbering, finiteSetMatching_numbering,
    finiteSetNumbering_code_of_eq index second targetSecond hsecond]
  rfl

/-- A linear scan in arithmetic order computes the same numbering as the
semantic finite-set sorting operation. -/
def finiteSetScan {size : ℕ} (set : Finset (Fin size)) : List (Fin size) :=
  (List.finRange size).filter (fun point => point ∈ set)

theorem finiteSetScan_eq_sort {size : ℕ} (set : Finset (Fin size)) :
    finiteSetScan set = set.sort := by
  apply ((List.sortedLT_finRange size).pairwise.filter _).sortedLT.eq_of_mem_iff set.sortedLT_sort
  simp

@[simp] theorem finiteSetScan_length {size : ℕ} (set : Finset (Fin size)) :
    (finiteSetScan set).length = set.card := by
  rw [finiteSetScan_eq_sort, Finset.length_sort]

theorem finiteSetNumbering_scan {size : ℕ} (set : Finset (Fin size))
    (position : Fin set.card) :
    (finiteSetNumbering (Equiv.refl (Fin size)) set position).val =
      (finiteSetScan set).get (Fin.cast (finiteSetScan_length set).symm position) := by
  simp only [List.get_eq_getElem, Fin.val_cast, finiteSetScan_eq_sort]
  rfl

end AFT
