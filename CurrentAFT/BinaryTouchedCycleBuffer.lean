import CurrentAFT.BinaryTouchedCycle

/-! Materialized touched-edge vectors and executed rank queries. The finite
bijection is used only to verify the Gaussian sum, never as a runtime lookup. -/
namespace CurrentAFT.BinaryTouchedCycleBuffer
open AFT BinaryArithmetic RationalRejectionProgram BinaryTouchedCycle
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

 theorem candidates_work {body count : ℕ} (hb : 0 < body) (sites : Vector (Fin body) count) :
    (candidates hb sites).work ≤ count*(3*count+7*body+19)+3 := by
  have hp := storeData_work count (3*count+7*body+14) (fun slot : Fin count =>
    let selected := readVector (⟨0,hb⟩ : Fin body) sites slot
    let predecessor := previous body hb selected.value
    (⟨(selected.value,predecessor.value),selected.work+predecessor.work+2⟩ : CountedValue (Fin body × Fin body))) (by
      intro slot
      have hr := readVector_work (⟨0,hb⟩ : Fin body) sites slot
      have hv := previous_work body hb (readVector (⟨0,hb⟩ : Fin body) sites slot).value
      change _+_+2 ≤ _
      omega)
  change (storeData _ _).work+3*count+1 ≤ _
  nlinarith

 theorem prepare_work {body count : ℕ} (hb : 0 < body) (sites : Vector (Fin body) count) :
    (prepare hb sites).work ≤ count*(3*count+7*body+19)+3 + (2*count)*(2*count*(6*body+4)+3)+3 := by
  have hc := candidates_work hb sites
  have hu := unique_work (candidates hb sites).value
  rw [candidates_length] at hu
  change (candidates hb sites).work+(unique _).work+2 ≤ _
  omega


def buffer {body count : ℕ} (hb : 0 < body) (sites : Vector (Fin body) count) :
    CountedValue (Vector (Fin body) (prepare hb sites).value.length) :=
  let prepared := prepare hb sites
  let array := storeData prepared.value.length (fun index =>
    let selected := readList prepared.value index.val
    ⟨selected.data.getD ⟨0,hb⟩,selected.work+2⟩)
  ⟨array.value,prepared.work+array.work+2⟩

 theorem buffer_get {body count : ℕ} (hb : 0 < body) (sites : Vector (Fin body) count)
    (index : Fin (prepare hb sites).value.length) :
    (buffer hb sites).value.get index = (prepare hb sites).value.get index := by
  simp only [buffer,storeData_get,readList_value]
  rw [List.getElem?_eq_getElem index.isLt]
  rfl

 theorem buffer_injective {body count : ℕ} (hb : 0 < body) (sites : Vector (Fin body) count) :
    Function.Injective (buffer hb sites).value.get := by
  intro first second he
  rw [buffer_get,buffer_get] at he
  exact (prepare_nodup hb sites).get_inj_iff.mp he

 theorem vector_mem_get {Value : Type*} {size : ℕ} (values : Vector Value size) (point : Value) :
    point ∈ values.toList ↔ ∃ index : Fin size, values.get index = point := by
  rw [Vector.mem_toList_iff,Vector.mem_iff_getElem]
  exact ⟨fun ⟨index,hi,he⟩ => ⟨⟨index,hi⟩,he⟩, fun ⟨index,he⟩ => ⟨index.val,index.isLt,he⟩⟩

 theorem buffer_mem {body count : ℕ} (hb : 0 < body) (sites : Vector (Fin body) count) (point : Fin body) :
    point ∈ (buffer hb sites).value.toList ↔ point ∈ CyclePatternProgram.touched sites.get := by
  rw [vector_mem_get]
  constructor
  · rintro ⟨index,he⟩
    apply (prepare_mem hb sites point).mp
    rw [← he,buffer_get]
    exact List.get_mem (prepare hb sites).value index
  · intro hp
    obtain ⟨index,he⟩ := List.mem_iff_get.mp ((prepare_mem hb sites point).mpr hp)
    exact ⟨index,by rw [buffer_get]; exact he⟩


def rank {body size : ℕ} (values : Vector (Fin body) size) (target : Fin body) :
    (length : ℕ) → length ≤ size → CountedValue (Option (Fin size))
  | 0, _ => ⟨none,1⟩
  | length+1, h =>
    let old := rank values target length (by omega)
    let index : Fin size := ⟨length,by omega⟩
    let vertex := readVector target values index
    let hit := equalCounter vertex.value.val target.val
    ⟨if hit.value then some index else old.value,old.work+vertex.work+hit.work+3⟩

 theorem rank_value {body size : ℕ} (values : Vector (Fin body) size) (hinj : Function.Injective values.get)
    (target : Fin body) (index : Fin size) (hindex : values.get index = target)
    (length : ℕ) (hlength : length ≤ size) (hvisited : index.val < length) :
    (rank values target length hlength).value = some index := by
  induction length with
  | zero => omega
  | succ length ih =>
    let last : Fin size := ⟨length,by omega⟩
    have hh : (equalCounter (readVector target values last).value.val target.val).value = true ↔ values.get last = target := by
      rw [equalCounter_value,readVector_value,Fin.ext_iff]
    change (if (equalCounter (readVector target values last).value.val target.val).value then some last else
      (rank values target length _).value) = _
    by_cases he : values.get last = target
    · rw [if_pos (hh.mpr he)]
      exact congrArg some (hinj (he.trans hindex.symm))
    · rw [if_neg (fun h => he (hh.mp h))]
      apply ih (by omega)
      have hn : index.val ≠ length := by
        intro h
        have hi : index = last := Fin.ext h
        exact he (hi ▸ hindex)
      omega

 theorem rank_work {body size : ℕ} (values : Vector (Fin body) size) (target : Fin body)
    (length : ℕ) (hlength : length ≤ size) :
    (rank values target length hlength).work ≤ length*(3*size+6*body+8)+1 := by
  induction length with
  | zero => simp only [rank,Nat.zero_mul,Nat.zero_add,le_refl]
  | succ length ih =>
    let last : Fin size := ⟨length,by omega⟩
    have ho := ih (by omega)
    have hr := readVector_work target values last
    have he := equalCounter_work (readVector target values last).value.val target.val
    have hv := (readVector target values last).value.isLt
    have ht := target.isLt
    change (rank values target length _).work+(readVector target values last).work+(equalCounter _ _).work+3 ≤ _
    nlinarith


def lookup {body size : ℕ} (values : Vector (Fin body) size) (hinj : Function.Injective values.get)
    (target : Fin body) (hmem : target ∈ values.toList) : CountedValue (Fin size) :=
  let found := rank values target size le_rfl
  have hs : found.value.isSome := by
    obtain ⟨index,he⟩ := (vector_mem_get values target).mp hmem
    have hg : values.get index = target := he
    have hr := rank_value values hinj target index hg size le_rfl index.isLt
    rw [show found.value = some index from hr]
    trivial
  ⟨found.value.get hs,found.work+2⟩

 theorem lookup_value {body size : ℕ} (values : Vector (Fin body) size) (hinj : Function.Injective values.get)
    (target : Fin body) (hmem : target ∈ values.toList) :
    values.get (lookup values hinj target hmem).value = target := by
  obtain ⟨index,he⟩ := (vector_mem_get values target).mp hmem
  have hr := rank_value values hinj target index (show values.get index = target from he) size le_rfl index.isLt
  simp only [lookup,hr,Option.get_some]
  exact he

 theorem lookup_work {body size : ℕ} (values : Vector (Fin body) size) (hinj : Function.Injective values.get)
    (target : Fin body) (hmem : target ∈ values.toList) :
    (lookup values hinj target hmem).work ≤ size*(3*size+6*body+8)+3 := Nat.add_le_add_right (rank_work values target size le_rfl) 2

noncomputable section

def edgeEquiv {body count : ℕ} (hb : 0 < body) (sites : Vector (Fin body) count) :
    Fin (prepare hb sites).value.length ≃ CyclePatternProgram.touched sites.get :=
  Equiv.ofBijective (fun index => ⟨(buffer hb sites).value.get index,
    (buffer_mem hb sites _).mp ((vector_mem_get (buffer hb sites).value _).mpr ⟨index,rfl⟩)⟩) (by
      constructor
      · intro first second he
        exact buffer_injective hb sites (congrArg Subtype.val he)
      · intro vertex
        obtain ⟨index,he⟩ := (vector_mem_get (buffer hb sites).value vertex.val).mp ((buffer_mem hb sites vertex.val).mpr vertex.property)
        exact ⟨index,Subtype.ext he⟩)

end
end CurrentAFT.BinaryTouchedCycleBuffer
