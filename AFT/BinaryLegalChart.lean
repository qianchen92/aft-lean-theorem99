import AFT.BinaryChartArray
import AFT.ChartLegalize

/-! A real sequential Boolean scan for the legal-chart fallback. No finite-set
membership or minimum search is delegated to a constant-time oracle. -/
namespace AFT.BinaryArithmetic
open AFT.RationalRejectionProgram AFT.BoundaryCalibration AFT.BetaReference

def firstTrue : List Bool → CountedValue (Option ℕ)
  | [] => ⟨none,1⟩
  | true::_ => ⟨some 0,2⟩
  | false::tail =>
    let remaining := firstTrue tail
    ⟨remaining.value.map Nat.succ,remaining.work+3⟩

theorem firstTrue_value (input : List Bool) :
    (firstTrue input).value=input.findIdx? id := by
  induction input with
  | nil => rfl
  | cons head tail ih => cases head <;> simp [firstTrue,List.findIdx?_cons,ih]

theorem firstTrue_work (input : List Bool) :
    (firstTrue input).work ≤ 3*input.length+2 := by
  induction input with
  | nil => simp [firstTrue]
  | cons head tail ih => cases head <;> simp only [firstTrue,List.length_cons] <;> omega

theorem firstTrue_lt {input : List Bool} {index : ℕ}
    (h : (firstTrue input).value=some index) : index < input.length :=
  (List.findIdx?_eq_some_iff_findIdx_eq.mp ((firstTrue_value input).symm.trans h)).1

def legalChartScan {charts : ℕ} (mask : Vector Bool charts)
    (point : Fin charts) : CountedNatural :=
  let current := readVector false mask point
  if current.value then ⟨point.val,current.work+1⟩ else
    let found := firstTrue mask.toList
    ⟨found.value.getD 0,current.work+found.work+charts+3⟩

theorem legalChartScan_lt {charts : ℕ} [NeZero charts] (mask : Vector Bool charts)
    (point : Fin charts) : (legalChartScan mask point).value < charts := by
  unfold legalChartScan
  dsimp only
  split_ifs
  · exact point.isLt
  · dsimp only
    cases hf : (firstTrue mask.toList).value with
    | none => exact NeZero.pos charts
    | some index => simpa only [Option.getD_some,Vector.length_toList] using firstTrue_lt hf

def binaryLegalChartIndex {charts : ℕ} [NeZero charts] (mask : Vector Bool charts)
    (point : Fin charts) : CountedValue (Fin charts) :=
  let selected := legalChartScan mask point
  ⟨⟨selected.value,legalChartScan_lt mask point⟩,selected.work⟩

theorem binaryLegalChartIndex_value {charts : ℕ} [NeZero charts] (mask : Vector Bool charts)
    (point : Fin charts) (legal : Finset (Fin charts))
    (hmask : ∀ index,mask.get index=true ↔ index∈legal) :
    (binaryLegalChartIndex mask point).value=legalChartIndex charts legal point := by
  apply Fin.ext
  change (legalChartScan mask point).value=_
  by_cases hp : mask.get point=true
  · have hh := (hmask point).mp hp
    simp only [legalChartScan,readVector_value,hp,↓reduceIte,legalChartIndex,if_pos hh]
  · have hh : point∉legal := fun hi => hp ((hmask point).mpr hi)
    simp only [legalChartScan,readVector_value,if_neg hp,legalChartIndex,if_neg hh]
    cases hf : (firstTrue mask.toList).value with
    | none =>
      have hall := List.findIdx?_eq_none_iff.mp ((firstTrue_value mask.toList).symm.trans hf)
      have hn : ¬legal.Nonempty := by
        rintro ⟨index,hi⟩
        have ht : mask.get index=true := (hmask index).mpr hi
        have hm : mask.get index∈mask.toList := by
          simpa only [Vector.getElem_toList] using (List.getElem_mem (l := mask.toList) (n := index.val) (by simp))
        have hz := hall (mask.get index) hm
        simp only [id_eq,ht] at hz
        contradiction
      simp only [dif_neg hn,Option.getD_none,Fin.val_zero]
    | some index =>
      have hs := List.findIdx?_eq_some_iff_findIdx_eq.mp ((firstTrue_value mask.toList).symm.trans hf)
      have hi : index < charts := by simpa only [Vector.length_toList] using hs.1
      let selected : Fin charts := ⟨index,hi⟩
      have hm : selected∈legal := by
        apply (hmask selected).mp
        have hv := @List.findIdx_getElem Bool id mask.toList (by rw [hs.2];exact hs.1)
        simpa only [hs.2,id_eq,Vector.getElem_toList] using hv
      have hl : ∀ other∈legal,selected≤other := by
        intro other ho
        by_contra hn
        have ho' : other.val < index := by simpa only [Fin.not_le,selected] using hn
        have hz := @List.not_of_lt_findIdx Bool id mask.toList other.val (by rw [hs.2];exact ho')
        have ht := (hmask other).mpr ho
        have hv : mask.get other=false := by simpa only [id_eq,Vector.getElem_toList] using hz
        rw [ht] at hv
        contradiction
      have hne : legal.Nonempty := ⟨selected,hm⟩
      have hmin := (Finset.min'_eq_iff legal hne selected).mpr ⟨hm,hl⟩
      simp only [dif_pos hne,hmin,Option.getD_some,selected]

theorem binaryLegalChartIndex_work {charts : ℕ} [NeZero charts] (mask : Vector Bool charts)
    (point : Fin charts) : (binaryLegalChartIndex mask point).work ≤ 7*charts+8 := by
  have hr := readVector_work false mask point
  have hf := firstTrue_work mask.toList
  simp only [Vector.length_toList] at hf
  unfold binaryLegalChartIndex legalChartScan
  dsimp only
  split_ifs <;> dsimp only <;> omega

end AFT.BinaryArithmetic
