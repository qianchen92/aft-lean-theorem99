import CurrentAFT.BinaryRootMetadataSerializer

/-! Exact ordinal meaning of the bounded root metadata serialization. -/
namespace CurrentAFT.BinaryRootMetadataSerializer
open AFT ActualBlockFock TaggedSelection PairedRootPlacement CurrentRootOrdering
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize

def numbering (security : ℕ) : BlockIndex security ≃ Fin (population (Parameters.legCount security)
    (BackgroundRates.ordinaryPool security) (Parameters.modulus security)) :=
  (CurrentRootOrdering.blockNumbering security).trans (finCongr (by
    have h := UniformTaggedOutput.centerCount_split security
    unfold population
    omega))

def primaryInput {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s) :
    Vector (Fin (Parameters.legCount security)) r := Vector.ofFn choice.1
def ordinaryInput {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s) :
    Vector (Fin (BackgroundRates.ordinaryPool security)) s := Vector.ofFn choice.2
def tagsInput {security : ℕ} (tagged : Finset (BlockIndex security)) :
    Vector (Fin (population (Parameters.legCount security) (BackgroundRates.ordinaryPool security)
      (Parameters.modulus security))) tagged.card :=
  Vector.ofFn (fun index => numbering security (CurrentRootOrdering.tagOrdering tagged index).val)

 theorem tagsInput_get {security : ℕ} (tagged : Finset (BlockIndex security)) (index : Fin tagged.card) :
    (tagsInput tagged).get index=numbering security (CurrentRootOrdering.tagOrdering tagged index).val :=
  Vector.get_ofFn _ _

theorem numbering_primary (security : ℕ) (index : Fin (Parameters.legCount security)) :
    (numbering security (.inl index)).val=index.val := rfl

theorem numbering_compensator {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s) (index : Fin r) :
    (numbering security (.inr (.inl ((RationalFullResponseProgram.selection security r s choice).compensator index)))).val=
      Parameters.legCount security+(choice.1 index).val := rfl

theorem numbering_ordinary {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s) (index : Fin s) :
    (numbering security (.inr (.inl ((RationalFullResponseProgram.selection security r s choice).body index)))).val=
      Parameters.legCount security+Parameters.legCount security+(choice.2 index).val := by
  change Parameters.legCount security+(Parameters.legCount security+(choice.2 index).val)=_
  omega

theorem isKept_actual {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s) (block : BlockIndex security) :
    (isKept (primaryInput choice) (ordinaryInput choice) (numbering security block)).value=true ↔
      CurrentRootOrdering.isKept (RationalFullResponseProgram.selection security r s choice) block := by
  rw [isKept_value]
  simp only [primaryInput,ordinaryInput,Vector.get_ofFn,CurrentRootOrdering.isKept]
  constructor
  · rintro ⟨hp,hb⟩
    refine ⟨fun index he => ?_,fun index he => ?_,fun index he => ?_⟩
    · apply (hp index).1
      rw [he]
      exact numbering_primary _ _
    · apply (hp index).2
      rw [he]
      exact numbering_compensator choice index
    · apply hb index
      rw [he]
      exact numbering_ordinary choice index
  · rintro ⟨hp,hc,hb⟩
    constructor
    · intro index
      constructor
      · intro he
        apply hp index
        apply (numbering security).injective
        apply Fin.ext
        simpa only [numbering_primary,RationalFullResponseProgram.selection] using he
      · intro he
        apply hc index
        apply (numbering security).injective
        apply Fin.ext
        simpa only [numbering_compensator] using he
    · intro index he
      apply hb index
      apply (numbering security).injective
      apply Fin.ext
      simpa only [numbering_ordinary] using he

theorem tagsInput_increasing {security : ℕ} (tagged : Finset (BlockIndex security)) :
    StrictMono (tagsInput tagged).get := by
  intro i j hij
  simp only [tagsInput,Vector.get_ofFn]
  change (numbering security (CurrentRootOrdering.tagOrdering tagged i).val).val<
    (numbering security (CurrentRootOrdering.tagOrdering tagged j).val).val
  change (CurrentRootOrdering.blockNumbering security (CurrentRootOrdering.tagOrdering tagged i).val).val<
    (CurrentRootOrdering.blockNumbering security (CurrentRootOrdering.tagOrdering tagged j).val).val
  rw [CurrentRootOrdering.tagOrdering_number,CurrentRootOrdering.tagOrdering_number]
  exact (Finset.orderIsoOfFin (CurrentRootOrdering.tagIndices tagged) (Finset.card_map _)).strictMono hij

theorem tagsInput_range {security : ℕ} (tagged : Finset (BlockIndex security))
    (block : Fin (population (Parameters.legCount security) (BackgroundRates.ordinaryPool security) (Parameters.modulus security))) :
    block∈(tagsInput tagged).toList ↔ (numbering security).symm block∈tagged := by
  simp only [tagsInput,Vector.toList_ofFn,List.mem_ofFn]
  constructor
  · rintro ⟨index,he⟩
    rw [← he,Equiv.symm_apply_apply]
    exact (CurrentRootOrdering.tagOrdering tagged index).property
  · intro h
    obtain ⟨index,he⟩ := (CurrentRootOrdering.tagOrdering tagged).surjective ⟨(numbering security).symm block,h⟩
    refine ⟨index,?_⟩
    rw [he]
    exact (numbering security).apply_symm_apply block

def retainedInput {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security)) := (kept (primaryInput choice) (ordinaryInput choice) (tagsInput tagged)).value

theorem retainedInput_membership {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security))
    (block : Fin (population (Parameters.legCount security) (BackgroundRates.ordinaryPool security) (Parameters.modulus security))) :
    block∈retainedInput choice tagged ↔
      (numbering security).symm block∈CurrentRootOrdering.keptTags (RationalFullResponseProgram.selection security r s choice) tagged := by
  simp only [retainedInput,kept_value,List.mem_filter,tagsInput_range,CurrentRootOrdering.keptTags,Finset.mem_filter]
  rw [← isKept_actual choice ((numbering security).symm block),Equiv.apply_symm_apply]

theorem retainedInput_increasing {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security)) : (retainedInput choice tagged).Pairwise (·<·) := by
  rw [retainedInput,kept_value]
  apply List.Pairwise.filter
  have h := tagsInput_increasing tagged
  have he : (tagsInput tagged).toList=List.ofFn (tagsInput tagged).get := by
    simp only [tagsInput,Vector.toList_ofFn]
    congr 1
    funext index
    exact (Vector.get_ofFn (fun index => numbering security (CurrentRootOrdering.tagOrdering tagged index).val) index).symm
  rw [he,List.pairwise_ofFn]
  exact h


theorem retainedInput_nodup {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security)) : (retainedInput choice tagged).Nodup :=
  (retainedInput_increasing choice tagged).nodup

theorem retainedInput_finset {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security)) :
    (retainedInput choice tagged).toFinset=
      (CurrentRootOrdering.keptTags (RationalFullResponseProgram.selection security r s choice) tagged).map (numbering security).toEmbedding := by
  classical
  ext color
  rw [List.mem_toFinset,retainedInput_membership,Finset.mem_map]
  constructor
  · intro h
    exact ⟨(numbering security).symm color,h,(numbering security).apply_symm_apply color⟩
  · rintro ⟨block,h,he⟩
    rw [← he]
    simpa only [Equiv.toEmbedding_apply,Equiv.symm_apply_apply] using h

theorem retainedInput_length {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security)) :
    (retainedInput choice tagged).length=
      (CurrentRootOrdering.keptIndices (RationalFullResponseProgram.selection security r s choice) tagged).card := by
  classical
  have h := congrArg Finset.card (retainedInput_finset choice tagged)
  rw [List.toFinset_card_of_nodup (retainedInput_nodup choice tagged),Finset.card_map] at h
  simpa only [CurrentRootOrdering.keptIndices,CurrentRootOrdering.tagIndices,Finset.card_map] using h

theorem keptOrdering_number {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : Fin (CurrentRootOrdering.keptIndices selection tagged).card) :
    CurrentRootOrdering.blockNumbering security (CurrentRootOrdering.keptOrdering selection tagged index).val.val=
      (Finset.orderIsoOfFin (CurrentRootOrdering.keptIndices selection tagged) rfl index).val := by
  exact (CurrentRootOrdering.blockNumbering security).apply_symm_apply _

theorem retainedInput_get {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security)) (index : Fin (retainedInput choice tagged).length) :
    (retainedInput choice tagged).get index=
      numbering security (CurrentRootOrdering.keptOrdering (RationalFullResponseProgram.selection security r s choice) tagged
        (finCongr (retainedInput_length choice tagged) index)).val.val := by
  classical
  let selection := RationalFullResponseProgram.selection security r s choice
  let items := retainedInput choice tagged
  let output : Fin items.length → Fin (population (Parameters.legCount security) (BackgroundRates.ordinaryPool security) (Parameters.modulus security)) :=
    fun index => numbering security (CurrentRootOrdering.keptOrdering selection tagged (finCongr (retainedInput_length choice tagged) index)).val.val
  have hc : items.toFinset.card=items.length := List.toFinset_card_of_nodup (retainedInput_nodup choice tagged)
  have hm : StrictMono items.get := List.pairwise_iff_get.mp (retainedInput_increasing choice tagged)
  have ho : StrictMono output := by
    intro i j hij
    change (CurrentRootOrdering.blockNumbering security
      (CurrentRootOrdering.keptOrdering selection tagged (finCongr (retainedInput_length choice tagged) i)).val.val).val<
      (CurrentRootOrdering.blockNumbering security
      (CurrentRootOrdering.keptOrdering selection tagged (finCongr (retainedInput_length choice tagged) j)).val.val).val
    rw [keptOrdering_number,keptOrdering_number]
    exact (Finset.orderIsoOfFin (CurrentRootOrdering.keptIndices selection tagged) rfl).strictMono hij
  have hg (i : Fin items.length) : output i∈items.toFinset := by
    rw [List.mem_toFinset]
    apply (retainedInput_membership choice tagged _).mpr
    change (numbering security).symm (numbering security _ )∈_
    rw [Equiv.symm_apply_apply]
    exact ((CurrentRootOrdering.keptTagsEquiv selection tagged).symm
      (CurrentRootOrdering.keptOrdering selection tagged (finCongr (retainedInput_length choice tagged) i))).property
  have hget := Finset.orderEmbOfFin_unique hc (fun i => List.mem_toFinset.mpr (List.get_mem items i)) hm
  have hout := Finset.orderEmbOfFin_unique hc hg ho
  exact congrFun (hget.trans hout.symm) index

end CurrentAFT.BinaryRootMetadataSerializer
