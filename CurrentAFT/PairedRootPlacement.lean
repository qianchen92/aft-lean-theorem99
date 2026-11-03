import CurrentAFT.PairedOutputPlacement

/-! # The actual two root slots of each selected primary control -/
namespace CurrentAFT.PairedRootPlacement
open AFT ActualBlockFock TaggedSelection PairedOutputPlacement
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def selectedRootSlots (r s : ℕ) : Fin r ⊕ Fin s → Type
  | .inl _ => Fin 2
  | .inr _ => Fin 1

instance selectedRootSlotsFintype (r s : ℕ) (index : Fin r ⊕ Fin s) :
    Fintype (selectedRootSlots r s index) := by
  cases index with
  | inl _ => exact inferInstanceAs (Fintype (Fin 2))
  | inr _ => exact inferInstanceAs (Fintype (Fin 1))

/-- Primary root zero belongs to its compensator, and root one belongs
to its own leg attachment. The paired control is kept as one group. -/
def selectedRootEquiv (r s : ℕ) : Sigma (selectedRootSlots r s) ≃ RemovedLabel r s where
  toFun
    | ⟨.inl index, slot⟩ => Fin.cases (.inr (.inl index)) (fun _ => .inl index) slot
    | ⟨.inr index, _⟩ => .inr (.inr index)
  invFun
    | .inl index => ⟨.inl index, (1 : Fin 2)⟩
    | .inr (.inl index) => ⟨.inl index, (0 : Fin 2)⟩
    | .inr (.inr index) => ⟨.inr index, (0 : Fin 1)⟩
  left_inv := by
    rintro ⟨index | index, slot⟩
    · change Fin 2 at slot
      fin_cases slot <;> rfl
    · have hequal : slot = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
      subst slot
      rfl
  right_inv := by rintro (index | (index | index)) <;> rfl

def allRootEquiv {security r s : ℕ} (selection : Selection security r s) :
    (Sigma (selectedRootSlots r s) ⊕ selection.kept) ≃ BlockIndex security :=
  (Equiv.sumCongr (selectedRootEquiv r s) (Equiv.refl _)).trans (blockEquiv selection)

@[simp] theorem allRoot_compensator {security r s : ℕ} (selection : Selection security r s) (index : Fin r) :
    allRootEquiv selection (.inl ⟨.inl index, (0 : Fin 2)⟩) = .inr (.inl (selection.compensator index)) := rfl

@[simp] theorem allRoot_attachment {security r s : ℕ} (selection : Selection security r s) (index : Fin r) :
    allRootEquiv selection (.inl ⟨.inl index, (1 : Fin 2)⟩) = .inl (selection.primary index) := rfl

@[simp] theorem allRoot_body {security r s : ℕ} (selection : Selection security r s) (index : Fin s) :
    allRootEquiv selection (.inl ⟨.inr index, (0 : Fin 1)⟩) = .inr (.inl (selection.body index)) := rfl

@[simp] theorem allRoot_kept {security r s : ℕ} (selection : Selection security r s) (index : selection.kept) :
    allRootEquiv selection (.inr index) = index.val := rfl

abbrev HitKept {security r s : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security)) :=
  {index : selection.kept // index.val ∈ tagged}

def activeRootEmbedding {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) :
    (Sigma (selectedRootSlots r s) ⊕ HitKept selection tagged) ↪ BlockIndex security :=
  (Function.Embedding.sumMap (Function.Embedding.refl _) (Function.Embedding.subtype _)).trans
    (allRootEquiv selection).toEmbedding

theorem tagged_in_active_range {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : BlockIndex security) (hindex : index ∈ tagged) :
    index ∈ Set.range (activeRootEmbedding selection tagged) := by
  obtain ⟨source, hsource⟩ := (allRootEquiv selection).surjective index
  cases source with
  | inl source => exact ⟨.inl source, hsource⟩
  | inr source =>
    have hsourceval : source.val = index := hsource
    exact ⟨.inr ⟨source, by rw [hsourceval]; exact hindex⟩, hsource⟩

def activeTagEmbedding {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) :
    tagged ↪ (Sigma (selectedRootSlots r s) ⊕ HitKept selection tagged) where
  toFun index := Classical.choose (tagged_in_active_range selection tagged index.val index.property)
  inj' := by
    intro first second hequal
    have hfirst := Classical.choose_spec (tagged_in_active_range selection tagged first.val first.property)
    have hsecond := Classical.choose_spec (tagged_in_active_range selection tagged second.val second.property)
    apply Subtype.ext
    dsimp only at hequal
    rw [← hfirst, ← hsecond, hequal]

@[simp] theorem activeTag_image {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : tagged) :
    activeRootEmbedding selection tagged (activeTagEmbedding selection tagged index) = index.val :=
  Classical.choose_spec (tagged_in_active_range selection tagged index.val index.property)

abbrev ActiveGroup {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) := (Fin r ⊕ Fin s) ⊕ HitKept selection tagged

def groupRootSlots {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) : ActiveGroup selection tagged → Type
  | .inl index => selectedRootSlots r s index
  | .inr _ => Fin 1

instance groupRootSlotsFintype {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : ActiveGroup selection tagged) :
    Fintype (groupRootSlots selection tagged index) := by
  cases index with
  | inl index => exact selectedRootSlotsFintype r s index
  | inr _ => exact inferInstanceAs (Fintype (Fin 1))

def singletonSlotsEquiv (Index : Type*) : Sigma (fun _ : Index => Fin 1) ≃ Index where
  toFun := Sigma.fst
  invFun index := ⟨index, 0⟩
  left_inv := by
    rintro ⟨index, slot⟩
    have hequal : slot = 0 := Subsingleton.elim _ _
    subst slot
    rfl
  right_inv _ := rfl

def activeSlotsEquiv {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) :
    Sigma (groupRootSlots selection tagged) ≃
      (Sigma (selectedRootSlots r s) ⊕ HitKept selection tagged) :=
  (Equiv.sumSigmaDistrib (groupRootSlots selection tagged)).trans
    (Equiv.sumCongr (Equiv.refl _) (singletonSlotsEquiv (HitKept selection tagged)))

def rootEmbedding {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) : Sigma (groupRootSlots selection tagged) ↪ BlockIndex security :=
  (activeSlotsEquiv selection tagged).toEmbedding.trans (activeRootEmbedding selection tagged)

def tagEmbedding {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) : tagged ↪ Sigma (groupRootSlots selection tagged) :=
  (activeTagEmbedding selection tagged).trans (activeSlotsEquiv selection tagged).symm.toEmbedding

@[simp] theorem tag_image {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : tagged) :
    rootEmbedding selection tagged (tagEmbedding selection tagged index) = index.val := by
  change activeRootEmbedding selection tagged
    ((activeSlotsEquiv selection tagged) ((activeSlotsEquiv selection tagged).symm _)) = _
  rw [Equiv.apply_symm_apply, activeTag_image]

theorem hitKept_card_le {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) : Fintype.card (HitKept selection tagged) ≤ tagged.card := by
  have h := Fintype.card_le_of_injective
    (fun index : HitKept selection tagged => (⟨index.val.val, index.property⟩ : tagged)) (by
      intro first second hequal
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun index : tagged => index.val) hequal)
  simpa only [Fintype.card_coe] using h

theorem activeGroup_card_le {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) :
    Fintype.card (ActiveGroup selection tagged) ≤ r + s + tagged.card := by
  simp only [ActiveGroup, Fintype.card_sum, Fintype.card_fin]
  exact Nat.add_le_add_left (hitKept_card_le selection tagged) _

end
end CurrentAFT.PairedRootPlacement
