import CurrentAFT.BinaryRootMetadataMeaning
import CurrentAFT.BinaryFullResponseCounts
import CurrentAFT.CountedBoundedRootTags

/-! Runtime count and input casts for root metadata are proof transports.
All index values, and hence all executed comparisons, are preserved. -/
namespace CurrentAFT.BinaryRootMetadataSerializer
open AFT ActualBlockFock TaggedSelection
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize

theorem population_counts (security : ℕ) :
    population (BinaryFullResponseCounts.current security).leg (BinaryFullResponseCounts.current security).ordinary
      (BinaryFullResponseCounts.current security).queue=
    population (Parameters.legCount security) (BackgroundRates.ordinaryPool security) (Parameters.modulus security) := by
  rcases BinaryFullResponseCounts.current_value security with ⟨hl,ho,hq,_⟩
  rw [hl,ho,hq]

def countEquiv (security : ℕ) :
    Fin (population (BinaryFullResponseCounts.current security).leg (BinaryFullResponseCounts.current security).ordinary
      (BinaryFullResponseCounts.current security).queue) ≃
    Fin (population (Parameters.legCount security) (BackgroundRates.ordinaryPool security) (Parameters.modulus security)) :=
  finCongr (population_counts security)

def tagBlockEquiv (security : ℕ) : Fin (BinaryFullResponseCounts.current security).body ≃ BlockIndex security :=
  (finCongr (BinaryFullResponseCounts.body_decomposition security).symm).trans
    ((countEquiv security).trans (numbering security).symm)

def tagBlocks {security order : ℕ}
    (tag : CountedBoundedRootTags.Tag (BinaryFullResponseCounts.current security).body order) : Finset (BlockIndex security) :=
  tag.set.map (tagBlockEquiv security).toEmbedding

theorem tagBlocks_card {security order : ℕ}
    (tag : CountedBoundedRootTags.Tag (BinaryFullResponseCounts.current security).body order) :
    (tagBlocks tag).card=tag.values.length := by
  rw [tagBlocks,Finset.card_map,CountedBoundedRootTags.Tag.card]

def actualChoice {security r s : ℕ}
    (primary : Vector (Fin (BinaryFullResponseCounts.current security).leg) r)
    (body : Vector (Fin (BinaryFullResponseCounts.current security).ordinary) s)
    (hp : Function.Injective primary.get) (hb : Function.Injective body.get) : UniformTaggedOutput.Choice security r s :=
  (⟨fun index => Fin.cast (BinaryFullResponseCounts.current_value security).1 (primary.get index),by
      intro i j he
      apply hp
      exact Fin.cast_injective _ he⟩,
    ⟨fun index => Fin.cast (BinaryFullResponseCounts.current_value security).2.1 (body.get index),by
      intro i j he
      apply hb
      exact Fin.cast_injective _ he⟩)

theorem actualChoice_primary {security r s : ℕ}
    (primary : Vector (Fin (BinaryFullResponseCounts.current security).leg) r)
    (body : Vector (Fin (BinaryFullResponseCounts.current security).ordinary) s)
    (hp : Function.Injective primary.get) (hb : Function.Injective body.get) :
    primary.map (Fin.cast (BinaryFullResponseCounts.current_value security).1)=primaryInput (actualChoice primary body hp hb) := by
  apply Vector.ext
  intro index hi
  change (primary.map (Fin.cast (BinaryFullResponseCounts.current_value security).1)).get ⟨index,hi⟩=
    (primaryInput (actualChoice primary body hp hb)).get ⟨index,hi⟩
  simp only [Vector.get_map,primaryInput,Vector.get_ofFn]
  rfl

theorem actualChoice_ordinary {security r s : ℕ}
    (primary : Vector (Fin (BinaryFullResponseCounts.current security).leg) r)
    (body : Vector (Fin (BinaryFullResponseCounts.current security).ordinary) s)
    (hp : Function.Injective primary.get) (hb : Function.Injective body.get) :
    body.map (Fin.cast (BinaryFullResponseCounts.current_value security).2.1)=ordinaryInput (actualChoice primary body hp hb) := by
  apply Vector.ext
  intro index hi
  change (body.map (Fin.cast (BinaryFullResponseCounts.current_value security).2.1)).get ⟨index,hi⟩=
    (ordinaryInput (actualChoice primary body hp hb)).get ⟨index,hi⟩
  simp only [Vector.get_map,ordinaryInput,Vector.get_ofFn]
  rfl

def nativeTag {security order : ℕ}
    (tag : CountedBoundedRootTags.Tag (BinaryFullResponseCounts.current security).body order) :
    Vector (Fin (population (BinaryFullResponseCounts.current security).leg (BinaryFullResponseCounts.current security).ordinary
      (BinaryFullResponseCounts.current security).queue)) tag.values.length :=
  Eq.mpr (congrArg (fun count => Vector (Fin count) tag.values.length)
    (BinaryFullResponseCounts.body_decomposition security)) tag.store.value

theorem vector_count_cast_get {first second count : ℕ} (h : first=second) (values : Vector (Fin second) count)
    (index : Fin count) :
    (Eq.mpr (congrArg (fun bound => Vector (Fin bound) count) h) values).get index=Fin.cast h.symm (values.get index) := by
  cases h
  rfl

theorem nativeTag_get {security order : ℕ}
    (tag : CountedBoundedRootTags.Tag (BinaryFullResponseCounts.current security).body order) (index : Fin tag.values.length) :
    (nativeTag tag).get index=Fin.cast (BinaryFullResponseCounts.body_decomposition security).symm (tag.vector.get index) := by
  have h := vector_count_cast_get (BinaryFullResponseCounts.body_decomposition security) tag.store.value index
  simpa only [nativeTag,CountedBoundedRootTags.Tag.store_value] using h

theorem nativeTag_value {security order : ℕ}
    (tag : CountedBoundedRootTags.Tag (BinaryFullResponseCounts.current security).body order) (index : Fin tag.values.length) :
    ((countEquiv security) ((nativeTag tag).get index)).val=(tag.vector.get index).val := by
  rw [nativeTag_get]
  rfl

theorem current_congr_counts {legs ordinary queues legs' ordinary' queues' r s tags : ℕ}
    (hl : legs=legs') (ho : ordinary=ordinary') (hq : queues=queues')
    (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (tagged : Vector (Fin (population legs ordinary queues)) tags) :
    current (legs:=legs') (ordinary:=ordinary') (queues:=queues') (primary.map (Fin.cast hl)) (body.map (Fin.cast ho))
      (tagged.map (Fin.cast (by cases hl;cases ho;cases hq;rfl)))=current primary body tagged := by
  subst legs'
  subst ordinary'
  subst queues'
  simp only [Fin.cast_refl,Vector.map_id_fun,id_eq]

theorem current_native_counts {security r s order : ℕ}
    (primary : Vector (Fin (BinaryFullResponseCounts.current security).leg) r)
    (body : Vector (Fin (BinaryFullResponseCounts.current security).ordinary) s)
    (tag : CountedBoundedRootTags.Tag (BinaryFullResponseCounts.current security).body order) :
    current (primary.map (Fin.cast (BinaryFullResponseCounts.current_value security).1))
      (body.map (Fin.cast (BinaryFullResponseCounts.current_value security).2.1))
      ((nativeTag tag).map (countEquiv security))=current primary body (nativeTag tag) := by
  have he : (countEquiv security : _ → _)=Fin.cast (population_counts security) := by
    funext value
    apply Fin.ext
    rfl
  rw [he]
  exact current_congr_counts (BinaryFullResponseCounts.current_value security).1
    (BinaryFullResponseCounts.current_value security).2.1 (BinaryFullResponseCounts.current_value security).2.2.1 primary body (nativeTag tag)

theorem vector_mem_toList {α : Type*} {count : ℕ} (values : Vector α count) (value : α) :
    value∈values.toList ↔ ∃ index,values.get index=value := by
  simp only [Vector.mem_toList_iff,Vector.mem_iff_getElem]
  constructor
  · rintro ⟨index,hi,he⟩
    exact ⟨⟨index,hi⟩,he⟩
  · rintro ⟨index,he⟩
    exact ⟨index.val,index.isLt,he⟩

theorem nativeTag_membership {security order : ℕ}
    (tag : CountedBoundedRootTags.Tag (BinaryFullResponseCounts.current security).body order)
    (value : Fin (population (Parameters.legCount security) (BackgroundRates.ordinaryPool security) (Parameters.modulus security))) :
    value∈((nativeTag tag).map (countEquiv security)).toList ↔ (numbering security).symm value∈tagBlocks tag := by
  rw [vector_mem_toList]
  simp only [Vector.get_map,tagBlocks,Finset.mem_map,CountedBoundedRootTags.Tag.set,List.mem_toFinset]
  constructor
  · rintro ⟨index,he⟩
    refine ⟨tag.vector.get index,?_,?_⟩
    · simp only [CountedBoundedRootTags.Tag.vector,Vector.get_ofFn]
      exact List.get_mem _ _
    · rw [← he,nativeTag_get]
      rfl
  · rintro ⟨number,hnumber,he⟩
    obtain ⟨index,hi⟩ := List.mem_iff_get.mp hnumber
    refine ⟨index,?_⟩
    have hv : tag.vector.get index=number := by simpa only [CountedBoundedRootTags.Tag.vector,Vector.get_ofFn] using hi
    apply (numbering security).symm.injective
    rw [nativeTag_get,hv]
    exact he

theorem nativeTag_increasing {security order : ℕ}
    (tag : CountedBoundedRootTags.Tag (BinaryFullResponseCounts.current security).body order) :
    StrictMono (((nativeTag tag).map (countEquiv security)).get) := by
  intro first second hlt
  simp only [Vector.get_map]
  change ((countEquiv security) ((nativeTag tag).get first)).val<((countEquiv security) ((nativeTag tag).get second)).val
  rw [nativeTag_value,nativeTag_value]
  exact tag.vector_increasing hlt

theorem nativeTag_tagsInput {security order : ℕ}
    (tag : CountedBoundedRootTags.Tag (BinaryFullResponseCounts.current security).body order) (index : Fin tag.values.length) :
    ((nativeTag tag).map (countEquiv security)).get index=
      (tagsInput (tagBlocks tag)).get (Fin.cast (tagBlocks_card tag).symm index) := by
  let values := ((nativeTag tag).map (countEquiv security))
  let target : Fin tag.values.length → Fin (population (Parameters.legCount security) (BackgroundRates.ordinaryPool security) (Parameters.modulus security)) :=
    fun index => (tagsInput (tagBlocks tag)).get (Fin.cast (tagBlocks_card tag).symm index)
  have hm : StrictMono values.get := nativeTag_increasing tag
  have ht : StrictMono target := by
    intro first second hlt
    exact tagsInput_increasing (tagBlocks tag) hlt
  have he : Set.range values.get=Set.range target := by
    ext value
    constructor
    · rintro ⟨position,hp⟩
      have hm : value∈values.toList := (vector_mem_toList values value).mpr ⟨position,hp⟩
      have hb := (nativeTag_membership tag value).mp hm
      have hn := (tagsInput_range (tagBlocks tag) value).mpr hb
      obtain ⟨position,hp⟩ := (vector_mem_toList _ value).mp hn
      exact ⟨Fin.cast (tagBlocks_card tag) position,hp⟩
    · rintro ⟨position,hp⟩
      have hm : value∈(tagsInput (tagBlocks tag)).toList :=
        (vector_mem_toList _ value).mpr ⟨Fin.cast (tagBlocks_card tag).symm position,hp⟩
      have hb := (tagsInput_range (tagBlocks tag) value).mp hm
      exact (vector_mem_toList values value).mp ((nativeTag_membership tag value).mpr hb)
  exact congrFun ((hm.range_inj ht).mp he) index

theorem vector_length_cast_get {α : Type*} {first second : ℕ} (h : first=second) (values : Vector α first)
    (index : Fin second) : (values.cast h).get index=values.get (Fin.cast h.symm index) := by
  cases h
  rfl

theorem nativeTag_tagsInput_vector {security order : ℕ}
    (tag : CountedBoundedRootTags.Tag (BinaryFullResponseCounts.current security).body order) :
    (nativeTag tag).map (countEquiv security)=(tagsInput (tagBlocks tag)).cast (tagBlocks_card tag) := by
  apply Vector.ext
  intro index hi
  change ((nativeTag tag).map (countEquiv security)).get ⟨index,hi⟩=
    ((tagsInput (tagBlocks tag)).cast (tagBlocks_card tag)).get ⟨index,hi⟩
  rw [vector_length_cast_get]
  exact nativeTag_tagsInput tag _

def Result.castTags {r s first second : ℕ} (h : first=second) (value : Result r s first) : Result r s second :=
  ⟨value.kept,⟨value.data.roles,value.data.tagged.cast h⟩,value.work⟩

theorem current_cast_tags {legs ordinary queues r s first second : ℕ} (h : first=second)
    (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (tagged : Vector (Fin (population legs ordinary queues)) first) :
    current primary body (tagged.cast h)=Result.castTags h (current primary body tagged) := by
  cases h
  simp only [Vector.cast_rfl,Result.castTags]

theorem rational_current_cast_tags {security bits order r s first second : ℕ} (h : first=second)
    (value : Result r s first) (queue : ℤ) (sourcePrimary : Fin r → ℕ) (sourceBody : Fin s → ℕ) :
    RationalPackedRootProgram.current security bits order queue (Result.castTags h value).data.metadata sourcePrimary sourceBody=
      RationalPackedRootProgram.current security bits order queue value.data.metadata sourcePrimary sourceBody := by
  cases h
  rfl

end CurrentAFT.BinaryRootMetadataSerializer
