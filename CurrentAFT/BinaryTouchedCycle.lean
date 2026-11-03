import CurrentAFT.CyclePatternProgram
import AFT.BinaryDataArrays
import AFT.BinaryChartMetadata
import AFT.UnaryPolynomialCounters

/-! Explicit touched-edge buffers for selected cycle roots. The candidates
are the selected edge and its cyclic predecessor. Duplicate removal compares
native stored vertex counters; no finite-choice enumeration is executed. -/
namespace CurrentAFT.BinaryTouchedCycle
open AFT BinaryArithmetic RationalRejectionProgram
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false


def previous (body : ℕ) (hb : 0 < body) (point : Fin body) : CountedValue (Fin body) :=
  let last := subtractCounter body 1
  let before := subtractCounter point.val 1
  let first := equalCounter point.val 0
  if h : first.value = true then
    ⟨⟨last.count,by rw [subtractCounter_value]; omega⟩,last.work+before.work+first.work+3⟩
  else
    ⟨⟨before.count,by rw [subtractCounter_value]; exact (Nat.sub_le _ _).trans_lt point.isLt⟩,
      last.work+before.work+first.work+3⟩

 theorem previous_value (body : ℕ) (hb : 0 < body) (point : Fin body) :
    (previous body hb point).value = (finRotate body).symm point := by
  letI : NeZero body := ⟨hb.ne'⟩
  by_cases hp : point.val = 0
  · have he := (equalCounter_value point.val 0).mpr hp
    obtain ⟨count,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
    have hz : point = (0 : Fin (count+1)) := Fin.ext hp
    subst point
    rw [show (finRotate (count+1)).symm 0 = Fin.last count from
      (finRotate (count+1)).symm_apply_eq.mpr (finRotate_last).symm]
    apply Fin.ext
    simp only [previous,dif_pos he,Fin.val_mk,subtractCounter_value,Fin.val_last]
    omega
  · have he : ¬(equalCounter point.val 0).value = true := fun h => hp ((equalCounter_value _ _).mp h)
    apply Fin.ext
    rw [coe_finRotate_symm_of_ne_zero (fun h => hp (congrArg Fin.val h))]
    simp only [previous,dif_neg he,Fin.val_mk,subtractCounter_value]

 theorem previous_work (body : ℕ) (hb : 0 < body) (point : Fin body) :
    (previous body hb point).work ≤ 7*body+9 := by
  have hl := subtractCounter_work_left body 1
  have hp := subtractCounter_work_left point.val 1
  have he := equalCounter_work point.val 0
  have hi := point.isLt
  dsimp only [previous]
  split_ifs <;> dsimp only <;> omega


def contains {body : ℕ} (point : Fin body) : List (Fin body) → CountedValue Bool
  | [] => ⟨false,1⟩
  | head::tail =>
    let hit := equalCounter head.val point.val
    let rest := contains point tail
    ⟨hit.value || rest.value,hit.work+rest.work+2⟩

 theorem contains_value {body : ℕ} (point : Fin body) (items : List (Fin body)) :
    (contains point items).value = true ↔ point ∈ items := by
  induction items with
  | nil => simp only [contains,List.not_mem_nil,Bool.false_eq_true]
  | cons head tail ih =>
    simp only [contains,Bool.or_eq_true,equalCounter_value,ih,List.mem_cons,Fin.ext_iff]
    exact or_congr eq_comm Iff.rfl

 theorem contains_work {body : ℕ} (point : Fin body) (items : List (Fin body)) :
    (contains point items).work ≤ items.length*(6*body+4)+1 := by
  induction items with
  | nil => simp only [contains,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons head tail ih =>
    have h := equalCounter_work head.val point.val
    have hh := head.isLt
    have hp := point.isLt
    simp only [contains,List.length_cons]
    nlinarith


def unique {body : ℕ} : List (Fin body) → CountedValue (List (Fin body))
  | [] => ⟨[],1⟩
  | head::tail =>
    let rest := unique tail
    let hit := contains head rest.value
    ⟨if hit.value then rest.value else head::rest.value,rest.work+hit.work+2⟩

 theorem unique_mem {body : ℕ} (items : List (Fin body)) (point : Fin body) :
    point ∈ (unique items).value ↔ point ∈ items := by
  induction items generalizing point with
  | nil => rfl
  | cons head tail ih =>
    change point ∈ (if (contains head (unique tail).value).value then (unique tail).value else head::(unique tail).value) ↔ _
    by_cases h : (contains head (unique tail).value).value = true
    · rw [if_pos h]
      have hh : head ∈ tail := (ih head).mp ((contains_value head _).mp h)
      rw [ih, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (rfl | hp); exact hh; exact hp
    · rw [if_neg h,List.mem_cons,List.mem_cons,ih]

 theorem unique_nodup {body : ℕ} (items : List (Fin body)) : (unique items).value.Nodup := by
  induction items with
  | nil => exact List.nodup_nil
  | cons head tail ih =>
    change (if (contains head (unique tail).value).value then (unique tail).value else head::(unique tail).value).Nodup
    by_cases h : (contains head (unique tail).value).value = true
    · rw [if_pos h]; exact ih
    · rw [if_neg h,List.nodup_cons]
      exact ⟨fun hh => h ((contains_value head _).mpr hh),ih⟩

 theorem unique_length {body : ℕ} (items : List (Fin body)) : (unique items).value.length ≤ items.length := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
    change (if (contains head (unique tail).value).value then (unique tail).value else head::(unique tail).value).length ≤ _
    split_ifs <;> simp only [List.length_cons] <;> omega

 theorem unique_work {body : ℕ} (items : List (Fin body)) :
    (unique items).work ≤ items.length*(items.length*(6*body+4)+3)+1 := by
  induction items with
  | nil => simp only [unique,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons head tail ih =>
    have hc := contains_work head (unique tail).value
    have hl := unique_length tail
    have hm := Nat.mul_le_mul_right (6*body+4) hl
    change (unique tail).work + (contains head (unique tail).value).work+2 ≤ _
    simp only [List.length_cons]
    nlinarith


def candidates {body count : ℕ} (hb : 0 < body) (sites : Vector (Fin body) count) : CountedValue (List (Fin body)) :=
  let pairs := storeData count (fun slot =>
    let selected := readVector ⟨0,hb⟩ sites slot
    let predecessor := previous body hb selected.value
    ⟨(selected.value,predecessor.value),selected.work+predecessor.work+2⟩)
  ⟨pairs.value.toList.flatMap (fun pair => [pair.1,pair.2]),pairs.work+3*count+1⟩

 theorem candidates_value {body count : ℕ} (hb : 0 < body) (sites : Vector (Fin body) count) :
    (candidates hb sites).value = (List.finRange count).flatMap (fun slot => [sites.get slot,(finRotate body).symm (sites.get slot)]) := by
  simp only [candidates]
  rw [show (storeData count (fun slot =>
    let selected := readVector (⟨0,hb⟩ : Fin body) sites slot
    let predecessor := previous body hb selected.value
    (⟨(selected.value,predecessor.value),selected.work+predecessor.work+2⟩ : CountedValue (Fin body × Fin body)))).value =
      Vector.ofFn (fun slot => (sites.get slot,(finRotate body).symm (sites.get slot))) by
        apply Vector.ext
        intro index hi
        change (storeData _ _).value.get ⟨index,hi⟩ = _
        simp only [storeData_get,readVector_value,previous_value,Vector.getElem_ofFn]]
  rw [Vector.toList_ofFn,List.ofFn_eq_map,List.flatMap_map]

 theorem candidates_length {body count : ℕ} (hb : 0 < body) (sites : Vector (Fin body) count) :
    (candidates hb sites).value.length = 2*count := by
  rw [candidates_value]
  simp only [List.length_flatMap,List.length_cons,List.length_nil]
  simp [Nat.mul_comm]

 theorem candidates_mem {body count : ℕ} (hb : 0 < body) (sites : Vector (Fin body) count) (point : Fin body) :
    point ∈ (candidates hb sites).value ↔ point ∈ CyclePatternProgram.touched sites.get := by
  rw [candidates_value]
  simp only [List.mem_flatMap,List.mem_finRange,true_and,List.mem_cons,List.not_mem_nil,or_false,
    CyclePatternProgram.touched,Finset.mem_union,Finset.mem_image,Finset.mem_univ]
  aesop


def prepare {body count : ℕ} (hb : 0 < body) (sites : Vector (Fin body) count) : CountedValue (List (Fin body)) :=
  let raw := candidates hb sites
  let result := unique raw.value
  ⟨result.value,raw.work+result.work+2⟩

 theorem prepare_nodup {body count : ℕ} (hb : 0 < body) (sites : Vector (Fin body) count) : (prepare hb sites).value.Nodup := unique_nodup _

 theorem prepare_mem {body count : ℕ} (hb : 0 < body) (sites : Vector (Fin body) count) (point : Fin body) :
    point ∈ (prepare hb sites).value ↔ point ∈ CyclePatternProgram.touched sites.get :=
  (unique_mem _ _).trans (candidates_mem hb sites point)

 theorem prepare_length {body count : ℕ} (hb : 0 < body) (sites : Vector (Fin body) count) :
    (prepare hb sites).value.length ≤ 2*count := (unique_length _).trans_eq (candidates_length hb sites)

end CurrentAFT.BinaryTouchedCycle
