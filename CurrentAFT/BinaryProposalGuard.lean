import CurrentAFT.BinaryRationalCompare
import CurrentAFT.RationalProposalProgram

/-! # The proposal's full palette guard on stored binary entries

This executes every rational lower comparison and the uniform fallback.
The separate raw-table producer must still supply its actual binary data;
the theorem here does not postulate a cost for producing that table.
-/
namespace CurrentAFT.BinaryProposalGuard
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def allFin : (count : ℕ) → (Fin count → CountedValue Bool) → CountedValue Bool
  | 0, _ => ⟨true, 1⟩
  | count+1, test =>
    let previous := allFin count (fun index => test index.castSucc)
    let current := test (Fin.last count)
    ⟨previous.value && current.value, previous.work + current.work + 2⟩

theorem allFin_value (count : ℕ) (test : Fin count → CountedValue Bool) :
    (allFin count test).value = true ↔ ∀ index, (test index).value = true := by
  induction count with
  | zero => simp [allFin]
  | succ count ih =>
    simp only [allFin, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨hprevious, hlast⟩ index
      exact Fin.lastCases hlast hprevious index
    · intro hall
      exact ⟨fun index => hall index.castSucc, hall (Fin.last count)⟩

theorem allFin_work (count queryWork : ℕ) (test : Fin count → CountedValue Bool)
    (hw : ∀ index, (test index).work ≤ queryWork) :
    (allFin count test).work ≤ count*(queryWork+2)+1 := by
  induction count with
  | zero => simp [allFin]
  | succ count ih =>
    have hp := ih (fun index => test index.castSucc) (fun index => hw index.castSucc)
    have hn := hw (Fin.last count)
    simp only [allFin]
    nlinarith

def lowerCheck {count : ℕ} (threshold : RationalBits) (values : Vector RationalBits count) : CountedValue Bool :=
  allFin count (fun index =>
    let found := readVector zero values index
    let checked := BinaryRationalCompare.le threshold found.value
    ⟨checked.value, found.work + checked.work + 2⟩)

theorem lowerCheck_value {count : ℕ} (threshold : RationalBits) (values : Vector RationalBits count) :
    (lowerCheck threshold values).value = true ↔ ∀ index, threshold.decode ≤ (values.get index).decode := by
  simp only [lowerCheck, allFin_value, BinaryRationalCompare.le_value, readVector_value]

def lowerCheckWork (count height : ℕ) : ℕ := count*(3*count+BinaryRationalCompare.workBound height+7)+1

theorem lowerCheck_work {count : ℕ} (threshold : RationalBits) (values : Vector RationalBits count) (height : ℕ)
    (ht : HeightBound threshold.decode height) (hv : ∀ index, HeightBound (values.get index).decode height) :
    (lowerCheck threshold values).work ≤ lowerCheckWork count height := by
  apply allFin_work count (3*count+BinaryRationalCompare.workBound height+5)
  intro index
  have hr := readVector_work zero values index
  have hh : HeightBound (readVector zero values index).value.decode height := by rw [readVector_value]; exact hv index
  have hc := BinaryRationalCompare.le_work threshold (readVector zero values index).value height ht hh
  change (readVector zero values index).work +
    (BinaryRationalCompare.le threshold (readVector zero values index).value).work + 2 ≤ _
  omega

def uniformTable (count : ℕ) : ArrayResult count :=
  let denominator := ofCounter count
  let atom := RationalBits.inverse denominator.data
  let values := buildArray count (fun _ => ⟨atom.data, 1⟩)
  ⟨values.data, denominator.work + atom.work + values.work + 3⟩

theorem uniformTable_value (count : ℕ) (index : Fin count) :
    ((uniformTable count).data.get index).decode = (count:ℚ)⁻¹ := by
  simp only [uniformTable, buildArray_get, RationalBits.inverse_value, ofCounter_value]

def uniformWork (count : ℕ) : ℕ := 60*(count+1)^2+primitiveWorkBound count+3*count+5

theorem uniformTable_work (count : ℕ) : (uniformTable count).work ≤ uniformWork count := by
  have wd := ofCounter_work count
  have wi := RationalBits.inverse_work (ofCounter count).data count
  have wt := buildArray_work count 1 (fun _ => ⟨(RationalBits.inverse (ofCounter count).data).data, 1⟩) (by intro _; rfl)
  unfold uniformTable uniformWork
  dsimp only
  omega

def guardedTable {count : ℕ} (threshold : RationalBits) (raw : Vector RationalBits count) : ArrayResult count :=
  let checked := lowerCheck threshold raw
  let values := if checked.value then ⟨raw, 1⟩ else uniformTable count
  ⟨values.data, checked.work + values.work + 3⟩

theorem guardedTable_value {count : ℕ} (threshold : RationalBits) (raw : Vector RationalBits count) (index : Fin count) :
    ((guardedTable threshold raw).data.get index).decode =
      if ∀ position, threshold.decode ≤ (raw.get position).decode then (raw.get index).decode else (count:ℚ)⁻¹ := by
  unfold guardedTable
  dsimp only
  simp only [lowerCheck_value]
  split_ifs <;> simp only [uniformTable_value]

theorem guardedTable_work {count : ℕ} (threshold : RationalBits) (raw : Vector RationalBits count) (height : ℕ)
    (ht : HeightBound threshold.decode height) (hv : ∀ index, HeightBound (raw.get index).decode height) :
    (guardedTable threshold raw).work ≤ lowerCheckWork count height+uniformWork count+4 := by
  have wc := lowerCheck_work threshold raw height ht hv
  have wu := uniformTable_work count
  unfold guardedTable
  dsimp only
  split <;> (try dsimp only) <;> omega

def threshold (count : ℕ) : RationalResult :=
  let fourfold := multiplyCounter 4 count
  let encoded := ofCounter fourfold.count
  let result := RationalBits.inverse encoded.data
  ⟨result.data, fourfold.work + encoded.work + result.work + 3⟩

theorem threshold_value (count : ℕ) : (threshold count).data.decode = 1/(4*(count:ℚ)) := by
  simp only [threshold, RationalBits.inverse_value, ofCounter_value, multiplyCounter_value, Nat.cast_mul, Nat.cast_ofNat, one_div]

theorem threshold_height (count : ℕ) : HeightBound (threshold count).data.decode (4*count) := by
  rw [threshold_value]
  have h := (HeightBound.nat_coarse (4*count)).inv
  simpa only [Nat.cast_mul, Nat.cast_ofNat, one_div] using h

def thresholdWork (count : ℕ) : ℕ := (4*(2*count+3)+1) + 60*(4*count+1)^2+primitiveWorkBound (4*count)+3

theorem threshold_work (count : ℕ) : (threshold count).work ≤ thresholdWork count := by
  have we := ofCounter_work (4*count)
  have wi := RationalBits.inverse_work (ofCounter (4*count)).data (4*count)
  simp only [threshold, multiplyCounter_value, multiplyCounter_work, thresholdWork]
  omega

def primary {count : ℕ} (raw : Vector RationalBits count) : ArrayResult count :=
  let lower := threshold count
  let guarded := guardedTable lower.data raw
  ⟨guarded.data, lower.work + guarded.work + 2⟩

theorem primary_value (security bits : ℕ)
    (raw : Vector RationalBits (PublicParameterProgram.modulus security).count)
    (hraw : ∀ index, (raw.get index).decode = RationalProposalProgram.primaryRaw security bits index.val)
    (index : Fin (PublicParameterProgram.modulus security).count) :
    ((primary raw).data.get index).decode = RationalProposalProgram.primary security bits index.val := by
  simp only [primary, guardedTable_value, threshold_value]
  simp_rw [hraw]
  unfold RationalProposalProgram.primary RationalProposalProgram.primaryGood
  split_ifs <;> simp only [one_div]

theorem primary_work {count : ℕ} (raw : Vector RationalBits count) (height : ℕ)
    (hv : ∀ index, HeightBound (raw.get index).decode height) :
    (primary raw).work ≤ thresholdWork count+lowerCheckWork count (4*count+height)+uniformWork count+6 := by
  have ht := (threshold_height count).mono (Nat.le_add_right _ height)
  have hr (index : Fin count) : HeightBound (raw.get index).decode (4*count+height) := (hv index).mono (by omega)
  have wt := threshold_work count
  have wg := guardedTable_work (threshold count).data raw (4*count+height) ht hr
  change (threshold count).work + (guardedTable (threshold count).data raw).work + 2 ≤ _
  omega

end CurrentAFT.BinaryProposalGuard
