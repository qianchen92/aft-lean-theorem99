import AFT.CountedRootSelections
import AFT.BinaryDataArrays
import CurrentAFT.BinaryListSum
import CurrentAFT.FullResponseEnumeration

/-! # Stored, strictly ordered bounded root tags, with no powerset enumeration -/
namespace CurrentAFT.CountedBoundedRootTags
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

structure Tag (population order : ℕ) where
  values : List (Fin population)
  increasing : values.Pairwise (·<·)
  bounded : values.length ≤ order

def Tag.vector {population order : ℕ} (tag : Tag population order) : Vector (Fin population) tag.values.length := Vector.ofFn tag.values.get
def Tag.set {population order : ℕ} (tag : Tag population order) : Finset (Fin population) := tag.values.toFinset

theorem Tag.nodup {population order : ℕ} (tag : Tag population order) : tag.values.Nodup :=
  tag.increasing.imp (fun h => ne_of_lt h)
theorem Tag.card {population order : ℕ} (tag : Tag population order) : tag.set.card=tag.values.length :=
  List.toFinset_card_of_nodup tag.nodup
theorem Tag.vector_increasing {population order : ℕ} (tag : Tag population order) : StrictMono tag.vector.get := by
  intro first second hlt
  simpa only [Tag.vector,Vector.get_ofFn] using List.pairwise_iff_get.mp tag.increasing first second hlt

def Tag.read {population order : ℕ} (tag : Tag population order) (index : Fin tag.values.length) : CountedValue (Fin population) :=
  let result := readList tag.values index.val
  ⟨result.data.get (by rw [readList_value,List.getElem?_eq_getElem index.isLt]; rfl),result.work+1⟩

theorem Tag.read_value {population order : ℕ} (tag : Tag population order) (index : Fin tag.values.length) :
    (tag.read index).value=tag.values.get index := by
  simp only [Tag.read,readList_value,List.getElem?_eq_getElem index.isLt,Option.get_some]
  rfl

def Tag.store {population order : ℕ} (tag : Tag population order) : CountedValue (Vector (Fin population) tag.values.length) :=
  storeData tag.values.length tag.read

theorem Tag.store_value {population order : ℕ} (tag : Tag population order) : tag.store.value=tag.vector := by
  apply Vector.ext
  intro index hi
  change (storeData _ tag.read).value.get ⟨index,hi⟩=tag.vector.get ⟨index,hi⟩
  rw [storeData_get,Tag.read_value,Tag.vector,Vector.get_ofFn]

theorem Tag.store_work {population order : ℕ} (tag : Tag population order) :
    tag.store.work ≤ order*(2*order+4)+2 := by
  have h := storeData_work tag.values.length (2*tag.values.length+2) tag.read (fun index => by
    have hr := readList_work tag.values index.val
    change _+1 ≤ _
    omega)
  exact h.trans (by gcongr <;> exact tag.bounded)

def source (population : ℕ) : CountedValue (List (Fin population)) :=
  let values := storeData population (fun index => (⟨index,1⟩ : CountedValue (Fin population)))
  ⟨values.value.toList,values.work+population+1⟩

theorem source_value (population : ℕ) : (source population).value=List.finRange population := by
  simp only [source,storeData,Vector.map_ofFn,Vector.toList_ofFn]
  rfl

theorem source_work (population : ℕ) : (source population).work ≤ 4*population+3 := by
  have h := storeData_work population 1 (fun index => (⟨index,1⟩ : CountedValue (Fin population))) (fun _ => le_refl _)
  change _+population+1 ≤ _
  omega

def entry (population order : ℕ) (size : Fin (order+1)) : CountedValue (List (Tag population order)) :=
  let base := source population
  let computed := countedSubsequences size.val base.value
  let values := computed.value.attach.map (fun (word : {word : List (Fin population) // word∈computed.value}) =>
    let member : word.val∈(List.finRange population).sublistsLen size.val := by
      have hw : word.val∈(countedSubsequences size.val (source population).value).value := word.property
      simpa only [countedSubsequences_value,source_value] using hw
    let properties := List.mem_sublistsLen.mp member
    (⟨word.val,(List.sortedLT_finRange population).pairwise.sublist properties.1,by rw [properties.2]; have := size.isLt; omega⟩ : Tag population order))
  ⟨values,base.work+computed.work+computed.value.length*(size.val+3)^2+2⟩

theorem entry_sets (population order : ℕ) (size : Fin (order+1)) :
    (entry population order size).value.map Tag.set=
      (countedSubsequences size.val (List.finRange population)).value.map List.toFinset := by
  simp only [entry,List.map_map,Tag.set,Function.comp_def]
  rw [source_value]
  simpa only [List.map_map,Function.comp_def] using congrArg (fun values : List (List (Fin population)) => values.map List.toFinset)
    (List.attach_map_subtype_val _)

def current (population order : ℕ) : CountedValue (List (Tag population order)) :=
  let entries := (List.range (order+1)).attach.map (fun size => entry population order ⟨size.val,List.mem_range.mp size.property⟩)
  let values := entries.flatMap (fun result => result.value)
  ⟨values,(entries.map (fun result => result.work)).sum+3*values.length+4*population+3*(order+1)+5⟩

private theorem flatMap_attach {Input Output : Type*} (inputs : List Input) (function : Input → List Output) :
    inputs.attach.flatMap (fun input => function input.val)=inputs.flatMap function := by
  have h := congrArg (fun values : List Input => values.flatMap function) (List.attach_map_subtype_val inputs)
  simpa only [List.flatMap_map,Function.comp_def] using h

theorem current_sets (population order : ℕ) :
    (current population order).value.map Tag.set=boundedRootList population order := by
  simp only [current,List.map_flatMap,List.flatMap_map,entry_sets,boundedRootList]
  exact flatMap_attach (List.range (order+1)) (fun size => (countedSubsequences size (List.finRange population)).value.map List.toFinset)

theorem current_length (population order : ℕ) :
    (current population order).value.length ≤ (order+1)*(population+1)^order := by
  rw [← List.length_map Tag.set,current_sets]
  exact boundedRootList_length population order

def entryWorkBound (population order : ℕ) :=
  (10*(order+1)+(order+3)^2+9)*(population+1)^(order+2)
def workBound (population order : ℕ) :=
  (order+1)*entryWorkBound population order+3*((order+1)*(population+1)^order)+4*population+3*(order+1)+5

theorem entry_work (population order : ℕ) (size : Fin (order+1)) :
    (entry population order size).work ≤ entryWorkBound population order := by
  have hs : size.val ≤ order := by have := size.isLt; omega
  have hw := countedSubsequences_work size.val (List.finRange population)
  simp only [List.length_finRange] at hw
  have hp : (countedSubsequences size.val (List.finRange population)).value.length ≤ (population+1)^(order+2) := by
    rw [countedSubsequences_length,List.length_finRange]
    exact (Nat.choose_le_pow _ _).trans ((Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (by omega)))
  have hw' : (countedSubsequences size.val (List.finRange population)).work ≤ 10*(order+1)*(population+1)^(order+2) :=
    hw.trans (by gcongr; omega)
  have hc : (countedSubsequences size.val (List.finRange population)).value.length*(size.val+3)^2 ≤ (population+1)^(order+2)*(order+3)^2 := by gcongr
  have hone : 1 ≤ (population+1)^(order+2) := one_le_pow₀ (by omega)
  have hbase := source_work population
  have hpop : population+1 ≤ (population+1)^(order+2) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1≤population+1) (by omega : 1≤order+2)
  change (source population).work+_+_+2 ≤ _
  simp only [source_value]
  unfold entryWorkBound
  nlinarith

theorem current_work (population order : ℕ) : (current population order).work ≤ workBound population order := by
  have he : (((List.range (order+1)).attach.map (fun size =>
      (entry population order ⟨size.val,List.mem_range.mp size.property⟩).work))).sum ≤ (order+1)*entryWorkBound population order := by
    apply (List.sum_le_sum (fun size _ => entry_work population order ⟨size.val,List.mem_range.mp size.property⟩)).trans_eq
    simp
  have hl := current_length population order
  change _+3*(current population order).value.length+4*population+3*(order+1)+5 ≤ _
  simp only [List.map_map,Function.comp_def]
  unfold workBound
  omega

def guarded {population order : ℕ} (kernel : Tag population order → RationalResult) (tag : Tag population order) : RationalResult :=
  let test := lessCounter 1 tag.values.length
  let result := kernel tag
  ⟨if test.value then result.data else zero,test.work+result.work+2⟩

theorem guarded_value {population order : ℕ} (kernel : Tag population order → RationalResult) (tag : Tag population order) :
    (guarded kernel tag).data.decode=if 2≤tag.set.card then (kernel tag).data.decode else 0 := by
  have ht : (lessCounter 1 tag.values.length).value=true ↔ 2≤tag.set.card := by
    rw [lessCounter_value,Tag.card]; omega
  unfold guarded
  dsimp only
  split <;> rename_i h
  · rw [if_pos (ht.mp h)]
  · rw [if_neg (fun hc => h (ht.mpr hc)),zero_value]

def sum (population order : ℕ) (kernel : Tag population order → RationalResult) : RationalResult :=
  let tags := current population order
  let result := BinaryListSum.current (guarded kernel) tags.value
  ⟨result.data,tags.work+result.work+2⟩

def lengthBound (population order : ℕ) := (order+1)*(population+1)^order
def sumWork (population order bits budget : ℕ) :=
  workBound population order+BinaryListSum.work (lengthBound population order) bits (budget+3*order+7)+2

theorem guarded_bounds {population order : ℕ} (kernel : Tag population order → RationalResult)
    (tag : Tag population order) (bits budget : ℕ)
    (hh : HeightBound (kernel tag).data.decode bits) (hw : (kernel tag).work ≤ budget) :
    HeightBound (guarded kernel tag).data.decode bits ∧ (guarded kernel tag).work ≤ budget+3*order+7 := by
  have ht := lessCounter_work 1 tag.values.length
  have hl := tag.bounded
  constructor
  · unfold guarded
    dsimp only
    split
    · exact hh
    · rw [zero_value]; exact HeightBound.zero.mono (Nat.zero_le _)
  · change _+_+2 ≤ _
    omega

theorem sum_bounds (population order bits budget : ℕ) (kernel : Tag population order → RationalResult)
    (hh : ∀ tag, HeightBound (kernel tag).data.decode bits) (hw : ∀ tag, (kernel tag).work ≤ budget) :
    HeightBound (sum population order kernel).data.decode (BinaryListSum.height (lengthBound population order) bits) ∧
      (sum population order kernel).work ≤ sumWork population order bits budget := by
  have hg (tag : Tag population order) := guarded_bounds kernel tag bits budget (hh tag) (hw tag)
  have hl := current_length population order
  have hb := BinaryListSum.bounds_mono (bits := bits) (budget := budget+3*order+7) hl
  have hs := BinaryListSum.current_height (guarded kernel) (current population order).value bits (fun tag _ => (hg tag).1)
  have ws := BinaryListSum.current_work (guarded kernel) (current population order).value bits (budget+3*order+7)
    (fun tag _ => (hg tag).1) (fun tag _ => (hg tag).2)
  refine ⟨hs.mono hb.1,?_⟩
  have wt := current_work population order
  have ww := ws.trans hb.2
  change (current population order).work+_+2 ≤ _
  unfold sumWork
  dsimp only [lengthBound] at ww ⊢
  omega

theorem workBound_mono {population larger order : ℕ} (hp : population ≤ larger) :
    workBound population order ≤ workBound larger order := by
  unfold workBound entryWorkBound
  gcongr
theorem lengthBound_mono {population larger order : ℕ} (hp : population ≤ larger) :
    lengthBound population order ≤ lengthBound larger order := by
  unfold lengthBound
  gcongr

noncomputable def countPolynomial (order : ℕ) (population : Polynomial ℕ) : Polynomial ℕ := Polynomial.C (order+1)*(population+1)^order
noncomputable def generationWorkPolynomial (order : ℕ) (population : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (order+1)*(Polynomial.C (10*(order+1)+(order+3)^2+9)*(population+1)^(order+2))+
    3*countPolynomial order population+4*population+Polynomial.C (3*(order+1)+5)
noncomputable def heightPolynomial (order : ℕ) (population bits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryListSum.heightPolynomial (countPolynomial order population) bits
noncomputable def workPolynomial (order : ℕ) (population bits budget : Polynomial ℕ) : Polynomial ℕ :=
  generationWorkPolynomial order population+
    BinaryListSum.workPolynomial (countPolynomial order population) bits (budget+Polynomial.C (3*order+7))+2

theorem countPolynomial_eval (order : ℕ) (population : Polynomial ℕ) (security : ℕ) :
    (countPolynomial order population).eval security=lengthBound (population.eval security) order := by
  simp only [countPolynomial,lengthBound,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_one]
theorem generationWorkPolynomial_eval (order : ℕ) (population : Polynomial ℕ) (security : ℕ) :
    (generationWorkPolynomial order population).eval security=workBound (population.eval security) order := by
  simp only [generationWorkPolynomial,countPolynomial_eval,workBound,entryWorkBound,lengthBound,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_ofNat,Polynomial.eval_one]
  omega

theorem sum_polynomial_bounds (population order security : ℕ) (populationBound bits budget : Polynomial ℕ)
    (hp : population ≤ populationBound.eval security) (kernel : Tag population order → RationalResult)
    (hh : ∀ tag, HeightBound (kernel tag).data.decode (bits.eval security))
    (hw : ∀ tag, (kernel tag).work ≤ budget.eval security) :
    HeightBound (sum population order kernel).data.decode ((heightPolynomial order populationBound bits).eval security) ∧
      (sum population order kernel).work ≤ (workPolynomial order populationBound bits budget).eval security := by
  have h := sum_bounds population order (bits.eval security) (budget.eval security) kernel hh hw
  have hm := BinaryListSum.bounds_mono (bits := bits.eval security) (budget := budget.eval security+3*order+7) (lengthBound_mono (order := order) hp)
  constructor
  · apply h.1.mono
    rw [heightPolynomial,BinaryListSum.heightPolynomial_eval,countPolynomial_eval]
    exact hm.1
  · apply h.2.trans
    simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_ofNat,BinaryListSum.workPolynomial_eval,
      generationWorkPolynomial_eval,countPolynomial_eval,Polynomial.eval_C]
    unfold sumWork
    exact Nat.add_le_add_right (Nat.add_le_add (workBound_mono hp) hm.2) 2

noncomputable section
open scoped Classical
theorem sum_value (population order : ℕ) (kernel : Tag population order → RationalResult)
    (value : Finset (Fin population) → ℚ) (hvalue : ∀ tag, (kernel tag).data.decode=value tag.set) :
    (sum population order kernel).data.decode=
      ∑ selected∈(FullResponseEnumeration.boundedSubsets (Fin population) order).filter (fun selected => 2≤selected.card), value selected := by
  rw [sum,BinaryListSum.current_value]
  simp only [guarded_value,hvalue]
  have he : ((current population order).value.map (fun tag => if 2≤tag.set.card then value tag.set else 0)).sum=
      (((current population order).value.map Tag.set).map (fun selected => if 2≤selected.card then value selected else 0)).sum := by
    rw [List.map_map]; rfl
  rw [he]
  rw [current_sets,← List.sum_toFinset _ (boundedRootList_nodup population order)]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext selected
    simp only [Finset.mem_filter,List.mem_toFinset,mem_boundedRootList,FullResponseEnumeration.mem_boundedSubsets]
  · intro selected _; rfl

private theorem bounded_sum {Index : Type*} [Fintype Index] [DecidableEq Index] (order : ℕ) (value : Finset Index → ℚ) :
    (∑ selected∈(FullResponseEnumeration.boundedSubsets Index order).filter (fun selected => 2≤selected.card),value selected)=
      ∑ selected : Finset Index, if 2≤selected.card ∧ selected.card≤order then value selected else 0 := by
  have hsets : (FullResponseEnumeration.boundedSubsets Index order).filter (fun selected => 2≤selected.card)=
      (Finset.univ : Finset (Finset Index)).filter (fun selected => 2≤selected.card ∧ selected.card≤order) := by
    ext selected
    simp only [Finset.mem_filter,FullResponseEnumeration.mem_boundedSubsets,Finset.mem_univ,true_and,and_comm]
  rw [hsets,Finset.sum_filter]

theorem sum_value_equiv {Index : Type*} [Fintype Index] [DecidableEq Index] (population order : ℕ)
    (equiv : Fin population ≃ Index) (kernel : Tag population order → RationalResult) (value : Finset Index → ℚ)
    (hvalue : ∀ tag, (kernel tag).data.decode=value (equiv.finsetCongr tag.set)) :
    (sum population order kernel).data.decode=
      ∑ selected∈(FullResponseEnumeration.boundedSubsets Index order).filter (fun selected => 2≤selected.card), value selected := by
  rw [sum_value population order kernel (fun selected => value (equiv.finsetCongr selected)) hvalue,bounded_sum,bounded_sum]
  have he := equiv.finsetCongr.sum_comp (fun selected => if 2≤selected.card ∧ selected.card≤order then value selected else 0)
  simpa only [Equiv.finsetCongr_apply,Finset.card_map] using he

end
end CurrentAFT.CountedBoundedRootTags
