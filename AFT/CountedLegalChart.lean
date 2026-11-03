import AFT.CountedFiniteScans
import AFT.ChartLegalize
import Mathlib.Data.List.MinMax

/-! # The legal chart fallback as a counted scan of a stored Boolean array -/
namespace AFT.BoundaryCalibration
open RationalRejectionProgram

def countedListMinimum {State : Type*} [LinearOrder State] :
    List State → CountedValue (WithTop State)
  | [] => ⟨⊤,0⟩
  | first::rest =>
      let remaining := countedListMinimum rest
      ⟨min first remaining.value,remaining.work+2⟩

theorem countedListMinimum_value {State : Type*} [LinearOrder State]
    (input : List State) : (countedListMinimum input).value=input.minimum := by
  induction input with
  | nil => rfl
  | cons first rest ih => simp only [countedListMinimum,List.minimum_cons,ih]

theorem countedListMinimum_work {State : Type*} [LinearOrder State]
    (input : List State) : (countedListMinimum input).work=2*input.length := by
  induction input with
  | nil => rfl
  | cons first rest ih => simp only [countedListMinimum,List.length_cons,ih];omega

def countedLegalChartIndex (charts : ℕ) [NeZero charts]
    (mask : Vector Bool charts) (point : Fin charts) : CountedValue (Fin charts) :=
  if mask.get point then ⟨point,1⟩ else
    let selected := countedListFilter (fun index => ⟨mask.get index,1⟩) (List.ofFn id)
    let minimum := countedListMinimum selected.value
    ⟨match minimum.value with | none => 0 | some index => index,
      selected.work+minimum.work+charts+3⟩

theorem list_minimum_finset {State : Type*} [LinearOrder State]
    (input : List State) (legal : Finset State) (hmem : ∀ entry,entry∈input ↔ entry∈legal)
    (hlegal : legal.Nonempty) : input.minimum=(legal.min' hlegal : WithTop State) := by
  cases he : input.minimum with
  | top =>
      have hn : input=[] := List.minimum_eq_top.mp he
      obtain ⟨index,hi⟩ := hlegal
      have hh := (hmem index).mpr hi
      simp [hn] at hh
  | coe index =>
      have hi : index∈legal := (hmem index).mp (List.minimum_mem he)
      have hle : ∀ other∈legal,index≤other := fun other ho =>
        List.minimum_le_of_mem ((hmem other).mpr ho) he
      have hh := (Finset.min'_eq_iff legal hlegal index).mpr ⟨hi,hle⟩
      simp only [hh]

theorem countedLegalChartIndex_value (charts : ℕ) [NeZero charts]
    (mask : Vector Bool charts) (point : Fin charts) (legal : Finset (Fin charts))
    (hmask : ∀ index,mask.get index=true ↔ index∈legal) :
    (countedLegalChartIndex charts mask point).value=legalChartIndex charts legal point := by
  let input := (List.ofFn (id : Fin charts → Fin charts)).filter mask.get
  have hmem : ∀ index,index∈input ↔ index∈legal := by
    intro index
    simpa only [input,List.mem_filter,List.mem_ofFn,id_eq,exists_eq,true_and] using hmask index
  have hselected : (countedListFilter (fun index => ⟨mask.get index,1⟩)
      (List.ofFn id)).value=input := countedListFilter_value _ _
  by_cases hp : mask.get point=true
  · have hh := (hmask point).mp hp
    simp only [countedLegalChartIndex,hp,↓reduceIte,legalChartIndex,if_pos hh]
  · have hh : point∉legal := fun hi => hp ((hmask point).mpr hi)
    simp only [countedLegalChartIndex,hp,legalChartIndex,if_neg hh,
      hselected,countedListMinimum_value]
    by_cases hl : legal.Nonempty
    · rw [dif_pos hl,list_minimum_finset input legal hmem hl]
      rfl
    · have hi : input=[] := List.eq_nil_iff_forall_not_mem.mpr (fun index h =>
        hl ⟨index,(hmem index).mp h⟩)
      rw [dif_neg hl,hi]
      rfl

theorem countedLegalChartIndex_work (charts : ℕ) [NeZero charts]
    (mask : Vector Bool charts) (point : Fin charts) :
    (countedLegalChartIndex charts mask point).work≤ 6*charts+3 := by
  have hs := countedListFilter_work (fun index : Fin charts => ⟨mask.get index,1⟩)
    (List.ofFn id) 1 (fun _ _ => le_rfl)
  have hl : ((countedListFilter (fun index : Fin charts => ⟨mask.get index,1⟩)
      (List.ofFn id)).value).length≤ charts := by
    rw [countedListFilter_value]
    exact (List.length_filter_le _ _).trans_eq List.length_ofFn
  simp only [List.length_ofFn] at hs
  unfold countedLegalChartIndex
  split_ifs
  · dsimp only;omega
  · dsimp only
    rw [countedListMinimum_work]
    omega

end AFT.BoundaryCalibration
