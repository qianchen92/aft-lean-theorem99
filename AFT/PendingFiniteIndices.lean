import AFT.PendingExpansionProgram

/-! # Natural-index storage for finite pending-coordinate sets -/
namespace AFT.RationalNumerics
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Restrict a stored set of natural indices to the current finite order. -/
def finitePending (order : ℕ) (pending : Finset ℕ) : Finset (Fin order) :=
  Finset.univ.filter (fun point => point.val∈pending)

@[simp] theorem mem_finitePending {order : ℕ} {pending : Finset ℕ} {point : Fin order} :
    point∈finitePending order pending ↔ point.val∈pending := by
  simp only [finitePending,Finset.mem_filter,Finset.mem_univ,true_and]

theorem finitePending_image (order : ℕ) (pending : Finset ℕ)
    (hp : ∀ point∈pending,point<order) :
    (finitePending order pending).image Fin.val=pending := by
  ext point
  simp only [Finset.mem_image,mem_finitePending]
  constructor
  · rintro ⟨point,hpoint,rfl⟩;exact hpoint
  · intro hpoint;exact ⟨⟨point,hp point hpoint⟩,hpoint,rfl⟩

theorem finitePending_card (order : ℕ) (pending : Finset ℕ)
    (hp : ∀ point∈pending,point<order) :
    (finitePending order pending).card=pending.card := by
  have hh := congrArg Finset.card (finitePending_image order pending hp)
  simpa only [Finset.card_image_of_injective _ Fin.val_injective] using hh

theorem finitePending_nonempty (order : ℕ) (pending : Finset ℕ)
    (hp : ∀ point∈pending,point<order) :
    (finitePending order pending).Nonempty ↔ pending.Nonempty := by
  constructor
  · rintro ⟨point,hpoint⟩;exact ⟨point.val,mem_finitePending.mp hpoint⟩
  · rintro ⟨point,hpoint⟩;exact ⟨⟨point,hp point hpoint⟩,mem_finitePending.mpr hpoint⟩

theorem finitePending_min (order : ℕ) (pending : Finset ℕ)
    (hp : ∀ point∈pending,point<order) (hn : pending.Nonempty)
    (hf : (finitePending order pending).Nonempty) :
    ((finitePending order pending).min' hf).val=pending.min' hn := by
  apply Nat.le_antisymm
  · have hm := Finset.min'_le (finitePending order pending)
      (⟨pending.min' hn,hp _ (Finset.min'_mem pending hn)⟩ : Fin order)
      (mem_finitePending.mpr (Finset.min'_mem pending hn))
    exact hm
  · exact Finset.min'_le _ _ (mem_finitePending.mp (Finset.min'_mem _ hf))

theorem finitePending_erase (order : ℕ) (pending : Finset ℕ) (point : Fin order) :
    finitePending order (pending.erase point.val)=(finitePending order pending).erase point := by
  ext other
  simp only [mem_finitePending,Finset.mem_erase]
  exact and_congr (not_congr Fin.val_inj) Iff.rfl

@[simp] theorem finitePending_range (order : ℕ) : finitePending order (Finset.range order)=Finset.univ := by
  ext point
  simp only [mem_finitePending,Finset.mem_range,point.isLt,Finset.mem_univ]

end
end AFT.RationalNumerics
