import CurrentAFT.CurrentRootOrdering

/-! Bounded native lookup of each tagged root in the active groups.
There are two candidate root slots per group; the second slot of an
ordinary or retained group is explicitly rejected. -/
namespace CurrentAFT.CurrentRootSlotIndex
open AFT ActualBlockFock TaggedSelection PairedRootPlacement
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

abbrev Slot {security r s : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security)) :=
  Sigma (groupRootSlots selection tagged)

def within {security r s : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security)) :
    (group : ActiveGroup selection tagged) → Fin 2 → Option (Slot selection tagged)
  | .inl (.inl primary), slot => some ⟨.inl (.inl primary), slot⟩
  | .inl (.inr ordinary), slot => if slot.val=0 then some ⟨.inl (.inr ordinary), (0 : Fin 1)⟩ else none
  | .inr kept, slot => if slot.val=0 then some ⟨.inr kept, (0 : Fin 1)⟩ else none

def slotNumber {security r s : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security)) :
    Slot selection tagged → Fin 2
  | ⟨.inl (.inl _), slot⟩ => slot
  | ⟨.inl (.inr _), _⟩ => 0
  | ⟨.inr _, _⟩ => 0

def encode {security r s count : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (ordering : Fin count ≃ ActiveGroup selection tagged) (root : Slot selection tagged) : Fin (count*2) :=
  finProdFinEquiv (ordering.symm root.fst, slotNumber selection tagged root)

def decode {security r s count : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (ordering : Fin count ≃ ActiveGroup selection tagged) (index : Fin (count*2)) : Option (Slot selection tagged) :=
  within selection tagged (ordering (finProdFinEquiv.symm index).1) (finProdFinEquiv.symm index).2

theorem decode_encode {security r s count : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (ordering : Fin count ≃ ActiveGroup selection tagged) (root : Slot selection tagged) :
    decode selection tagged ordering (encode selection tagged ordering root) = some root := by
  rcases root with ⟨(primary | ordinary) | kept, slot⟩
  · simp only [decode, encode, Equiv.symm_apply_apply, Equiv.apply_symm_apply, slotNumber, within]
  · change Fin 1 at slot
    have hs : slot=0 := Subsingleton.elim _ _
    subst slot
    simp only [decode, encode, Equiv.symm_apply_apply, Equiv.apply_symm_apply, slotNumber, within,
      Fin.val_zero, ite_true]
  · change Fin 1 at slot
    have hs : slot=0 := Subsingleton.elim _ _
    subst slot
    simp only [decode, encode, Equiv.symm_apply_apply, Equiv.apply_symm_apply, slotNumber, within,
      Fin.val_zero, ite_true]

theorem decode_eq_some {security r s count : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (ordering : Fin count ≃ ActiveGroup selection tagged) (index : Fin (count*2)) (root : Slot selection tagged) :
    decode selection tagged ordering index = some root ↔ index=encode selection tagged ordering root := by
  constructor
  · intro h
    obtain ⟨⟨group, slot⟩, rfl⟩ := finProdFinEquiv.surjective index
    obtain ⟨group, rfl⟩ := ordering.symm.surjective group
    simp only [decode, Equiv.symm_apply_apply, Equiv.apply_symm_apply] at h
    rcases group with (primary | ordinary) | kept
    · simp only [within, Option.some.injEq] at h
      subst root
      rfl
    · fin_cases slot <;> simp [within] at h
      subst root
      rfl
    · fin_cases slot <;> simp [within] at h
      subst root
      rfl
  · rintro rfl
    exact decode_encode selection tagged ordering root

def rootBlock {security r s : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security)) :
    Slot selection tagged → BlockIndex security
  | ⟨.inl (.inl primary), slot⟩ => if slot.val=0 then .inr (.inl (selection.compensator primary)) else .inl (selection.primary primary)
  | ⟨.inl (.inr ordinary), _⟩ => .inr (.inl (selection.body ordinary))
  | ⟨.inr kept, _⟩ => kept.val.val

theorem rootBlock_eq {security r s : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (root : Slot selection tagged) : rootBlock selection tagged root = rootEmbedding selection tagged root := by
  rcases root with ⟨(primary | ordinary) | kept, slot⟩
  · change Fin 2 at slot
    fin_cases slot <;> rfl
  · change Fin 1 at slot
    have hs : slot=0 := Subsingleton.elim _ _
    subst slot
    rfl
  · change Fin 1 at slot
    have hs : slot=0 := Subsingleton.elim _ _
    subst slot
    rfl

def test {security r s count : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (ordering : Fin count ≃ ActiveGroup selection tagged) (block : BlockIndex security) (index : Fin (count*2)) : Bool :=
  (decode selection tagged ordering index).any (fun root => decide (rootBlock selection tagged root=block))

def position {security r s count : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (ordering : Fin count ≃ ActiveGroup selection tagged) (block : BlockIndex security) : Option (Fin (count*2)) :=
  (List.ofFn (id : Fin (count*2) → Fin (count*2))).find? (test selection tagged ordering block)

theorem matches_root {security r s count : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (ordering : Fin count ≃ ActiveGroup selection tagged) (root : Slot selection tagged) (index : Fin (count*2)) :
    test selection tagged ordering (rootBlock selection tagged root) index=true ↔
      index=encode selection tagged ordering root := by
  unfold test
  cases hd : decode selection tagged ordering index with
  | none =>
    simp only [Option.any_none, Bool.false_eq_true, false_iff]
    intro h
    have hh := (decode_eq_some selection tagged ordering index root).mpr h
    rw [hd] at hh
    cases hh
  | some other =>
    simp only [Option.any_some, decide_eq_true_eq]
    constructor
    · intro h
      have he : other=root := (rootEmbedding selection tagged).injective (by simpa only [rootBlock_eq] using h)
      subst other
      exact (decode_eq_some selection tagged ordering index root).mp hd
    · intro h
      have hh := (decode_eq_some selection tagged ordering index root).mpr h
      rw [hd] at hh
      exact congrArg (rootBlock selection tagged) (Option.some.inj hh)

theorem position_root {security r s count : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (ordering : Fin count ≃ ActiveGroup selection tagged) (root : Slot selection tagged) :
    position selection tagged ordering (rootBlock selection tagged root) = some (encode selection tagged ordering root) := by
  unfold position
  apply (List.find?_ofFn_eq_some_of_injective (f := id) Function.injective_id).mpr
  constructor
  · exact (matches_root selection tagged ordering root _).mpr rfl
  · intro earlier hlt hmatch
    have he := (matches_root selection tagged ordering root earlier).mp hmatch
    subst earlier
    exact lt_irrefl _ hlt

theorem position_tag {security r s count : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (ordering : Fin count ≃ ActiveGroup selection tagged) (tag : tagged) :
    position selection tagged ordering tag.val =
      some (encode selection tagged ordering (tagEmbedding selection tagged tag)) := by
  have he : rootBlock selection tagged (tagEmbedding selection tagged tag)=tag.val := by
    rw [rootBlock_eq, tag_image]
  rw [← he]
  exact position_root selection tagged ordering _

def tagPosition {security r s count : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (ordering : Fin count ≃ ActiveGroup selection tagged) (tag : tagged) : Fin count × Fin 2 :=
  finProdFinEquiv.symm ((position selection tagged ordering tag.val).get (by rw [position_tag]; rfl))

theorem tagPosition_eq {security r s count : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (ordering : Fin count ≃ ActiveGroup selection tagged) (tag : tagged) :
    tagPosition selection tagged ordering tag =
      (ordering.symm (tagEmbedding selection tagged tag).fst,
        slotNumber selection tagged (tagEmbedding selection tagged tag)) := by
  unfold tagPosition
  simp only [position_tag, Option.get_some, encode, Equiv.symm_apply_apply]

def taggedSlots {security r s count : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (ordering : Fin count ≃ ActiveGroup selection tagged) : Fin tagged.card → Fin count × Fin 2 :=
  fun index => tagPosition selection tagged ordering (CurrentRootOrdering.tagOrdering tagged index)

end CurrentAFT.CurrentRootSlotIndex
