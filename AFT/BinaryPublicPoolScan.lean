import AFT.BinaryPermutationRows
import AFT.UnaryPolynomialCounters
import AFT.CountedPublicPoolScan

/-! Complete scans of stored public permutations, with real bounded-counter
comparisons and sequential array lookups. -/
namespace AFT.BinaryArithmetic
open AFT.PublicPoolProgram

theorem lessCounter_bool (first second : ℕ) :
    (lessCounter first second).value=decide (first < second) := by
  apply Bool.eq_iff_iff.mpr
  simp only [lessCounter_value,decide_eq_true_eq]

theorem not_lessCounter_bool (first second : ℕ) :
    (!(lessCounter first second).value)=decide (second ≤ first) := by
  rw [lessCounter_bool]
  simp only [←decide_not,not_lt]

def binaryPoolScan {population : ℕ} (legs queue : ℕ) (permutation : Vector (Fin population) population) :
    List (Fin population) → ScanResult population
  | [] => ⟨[],[],1⟩
  | point::remaining =>
      let previous := binaryPoolScan legs queue permutation remaining
      let image := BinaryArithmetic.readVector point permutation point
      let queued := lessCounter image.value.val queue
      let leg := lessCounter point.val legs
      ⟨if (!queued.value) && leg.value then point::previous.controls else previous.controls,
       if (!queued.value) && (!leg.value) then point::previous.available else previous.available,
       previous.work+image.work+queued.work+leg.work+8⟩

theorem binaryPoolScan_controls {population : ℕ} (legs queue : ℕ)
    (permutation : Vector (Fin population) population) (input : List (Fin population)) :
    (binaryPoolScan legs queue permutation input).controls=
      (scan legs queue (fun point => ⟨permutation.get point,0⟩) input).controls := by
  induction input with
  | nil => rfl
  | cons point input ih =>
      simp only [binaryPoolScan,scan,BinaryArithmetic.readVector_value,
        lessCounter_bool,←decide_not,not_lt,ih]

theorem binaryPoolScan_available {population : ℕ} (legs queue : ℕ)
    (permutation : Vector (Fin population) population) (input : List (Fin population)) :
    (binaryPoolScan legs queue permutation input).available=
      (scan legs queue (fun point => ⟨permutation.get point,0⟩) input).available := by
  induction input with
  | nil => rfl
  | cons point input ih =>
      simp only [binaryPoolScan,scan,BinaryArithmetic.readVector_value,
        not_lessCounter_bool,ih]

theorem binaryPoolScan_work {population : ℕ} (legs queue : ℕ)
    (permutation : Vector (Fin population) population) (input : List (Fin population)) :
    (binaryPoolScan legs queue permutation input).work ≤ input.length*(9*population+15)+1 := by
  induction input with
  | nil => simp only [binaryPoolScan,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons point input ih =>
      have hr := BinaryArithmetic.readVector_work point permutation point
      have hq := lessCounter_work_left (BinaryArithmetic.readVector point permutation point).value.val queue
      have hl := lessCounter_work_left point.val legs
      have himage := (BinaryArithmetic.readVector point permutation point).value.isLt
      have hpoint := point.isLt
      simp only [binaryPoolScan,List.length_cons]
      nlinarith

def binaryRunPoolScan {population : ℕ} (legs queue : ℕ)
    (permutation : Vector (Fin population) population) : ScanResult population :=
  let range := rangePrefix population population le_rfl
  let selected := binaryPoolScan legs queue permutation range.values
  ⟨selected.controls,selected.available,range.work+selected.work+1⟩

theorem binaryRunPoolScan_controls {population : ℕ} (legs queue : ℕ)
    (permutation : Vector (Fin population) population) :
    (binaryRunPoolScan legs queue permutation).controls=
      (runScan legs queue (fun point => ⟨permutation.get point,0⟩)).controls := by
  simp only [binaryRunPoolScan,runScan,binaryPoolScan_controls]

theorem binaryRunPoolScan_available {population : ℕ} (legs queue : ℕ)
    (permutation : Vector (Fin population) population) :
    (binaryRunPoolScan legs queue permutation).available=
      (runScan legs queue (fun point => ⟨permutation.get point,0⟩)).available := by
  simp only [binaryRunPoolScan,runScan,binaryPoolScan_available]

theorem binaryRunPoolScan_work {population : ℕ} (legs queue : ℕ)
    (permutation : Vector (Fin population) population) :
    (binaryRunPoolScan legs queue permutation).work ≤ (population+1)^2+population*(9*population+15)+2 := by
  have hr := rangePrefix_work population population le_rfl
  have hs := binaryPoolScan_work legs queue permutation (rangePrefix population population le_rfl).values
  rw [rangePrefix_length] at hs
  simp only [binaryRunPoolScan]
  omega

theorem binaryPermutationPool_controls (bits population legs queue : ℕ)
    (word : Fin population → Fin bits → Fin 2) :
    (binaryRunPoolScan legs queue (binaryPermutationRows bits population word).value).controls=
      finiteSetScan (controlSet population legs queue (PermutationProgram.rows bits population word)) := by
  rw [binaryRunPoolScan_controls,runScan_controls]
  exact scan_controls_correct legs queue _ _ (binaryPermutationRows_value bits population word)

theorem binaryPermutationPool_available (bits population legs queue : ℕ)
    (word : Fin population → Fin bits → Fin 2) :
    (binaryRunPoolScan legs queue (binaryPermutationRows bits population word).value).available=
      finiteSetScan (availableSet population legs queue (PermutationProgram.rows bits population word)) := by
  rw [binaryRunPoolScan_available,runScan_available]
  exact scan_available_correct legs queue _ _ (binaryPermutationRows_value bits population word)

end AFT.BinaryArithmetic
