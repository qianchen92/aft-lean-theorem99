import AFT.BinaryChartArray
import AFT.LinearIterationHeight

/-! Materialized Neumann iteration on canonical binary rationals. Every
matrix and vector access is an explicit sequential lookup. -/
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics AFT.RationalRejectionProgram
open scoped BigOperators

def matrixEntry {count : ℕ} (matrix : Vector (Vector RationalBits count) count)
    (output input : Fin count) : CountedValue RationalBits :=
  let fallback := Vector.replicate count zero
  let row := readVector fallback matrix output
  let entry := readVector zero row.value input
  ⟨entry.value,row.work+entry.work+count+2⟩

theorem matrixEntry_value {count : ℕ} (matrix : Vector (Vector RationalBits count) count)
    (output input : Fin count) : (matrixEntry matrix output input).value=(matrix.get output).get input := by
  simp only [matrixEntry,readVector_value]

theorem matrixEntry_work {count : ℕ} (matrix : Vector (Vector RationalBits count) count)
    (output input : Fin count) : (matrixEntry matrix output input).work ≤ 7*count+8 := by
  have hr := readVector_work (Vector.replicate count zero) matrix output
  have he := readVector_work zero (readVector (Vector.replicate count zero) matrix output).value input
  simp only [matrixEntry]
  omega

def matrixProductTerm {count : ℕ} (matrix : Vector (Vector RationalBits count) count)
    (profile : Vector RationalBits count) (output input : Fin count) : RationalResult :=
  let coefficient := matrixEntry matrix output input
  let argument := readVector zero profile input
  let result := multiply coefficient.value argument.value
  ⟨result.data,coefficient.work+argument.work+result.work+2⟩

theorem matrixProductTerm_value {count : ℕ} (matrix : Vector (Vector RationalBits count) count)
    (profile : Vector RationalBits count) (output input : Fin count) :
    (matrixProductTerm matrix profile output input).data.decode=
      ((matrix.get output).get input).decode*(profile.get input).decode := by
  simp only [matrixProductTerm,multiply_value,matrixEntry_value,readVector_value]

def matrixRow {count : ℕ} (matrix : Vector (Vector RationalBits count) count)
    (profile : Vector RationalBits count) (output : Fin count) : RationalResult :=
  sumFin count (matrixProductTerm matrix profile output)

def matrixApply {count : ℕ} (matrix : Vector (Vector RationalBits count) count)
    (profile : Vector RationalBits count) : ArrayResult count :=
  buildArray count (matrixRow matrix profile)

theorem matrixRow_value {count : ℕ} (matrix : Vector (Vector RationalBits count) count)
    (profile : Vector RationalBits count) (output : Fin count) :
    (matrixRow matrix profile output).data.decode=
      ∑ input,((matrix.get output).get input).decode*(profile.get input).decode := by
  simp only [matrixRow,sumFin_value,matrixProductTerm_value]

theorem matrixApply_value {count : ℕ} (matrix : Vector (Vector RationalBits count) count)
    (profile : Vector RationalBits count) (output : Fin count) :
    ((matrixApply matrix profile).data.get output).decode=
      ∑ input,((matrix.get output).get input).decode*(profile.get input).decode := by
  simp only [matrixApply,buildArray_get,matrixRow_value]

def matrixRowWork (count bits : ℕ) : ℕ :=
  count*(10*count+13+primitiveWorkBound bits+primitiveWorkBound ((count+1)*(2*bits+1))+2)+2

def matrixApplyWork (count bits : ℕ) : ℕ := count*(matrixRowWork count bits+2)+2

theorem matrixRow_work {count : ℕ} (matrix : Vector (Vector RationalBits count) count)
    (profile : Vector RationalBits count) (bits : ℕ)
    (hm : ∀ output input,HeightBound ((matrix.get output).get input).decode bits)
    (hp : ∀ input,HeightBound (profile.get input).decode bits) (output : Fin count) :
    (matrixRow matrix profile output).work ≤ matrixRowWork count bits := by
  apply sumFin_work count (2*bits) (10*count+13+primitiveWorkBound bits)
  · intro input
    rw [matrixProductTerm_value]
    exact ((hm output input).mul (hp input)).mono (by omega)
  · intro input
    have hc := matrixEntry_work matrix output input
    have hv := readVector_work zero profile input
    have ha := multiply_work (matrixEntry matrix output input).value (readVector zero profile input).value bits
      (by rw [matrixEntry_value];exact hm output input) (by rw [readVector_value];exact hp input)
    simp only [matrixProductTerm]
    omega

theorem matrixApply_work {count : ℕ} (matrix : Vector (Vector RationalBits count) count)
    (profile : Vector RationalBits count) (bits : ℕ)
    (hm : ∀ output input,HeightBound ((matrix.get output).get input).decode bits)
    (hp : ∀ input,HeightBound (profile.get input).decode bits) :
    (matrixApply matrix profile).work ≤ matrixApplyWork count bits :=
  buildArray_work count (matrixRowWork count bits) _ (matrixRow_work matrix profile bits hm hp)

def iterationEntry {count : ℕ} (rhs applied : Vector RationalBits count) (output : Fin count) : RationalResult :=
  let right := readVector zero rhs output
  let image := readVector zero applied output
  let negative := negate image.value
  let result := add right.value negative.data
  ⟨result.data,right.work+image.work+negative.work+result.work+3⟩

theorem iterationEntry_value {count : ℕ} (rhs applied : Vector RationalBits count) (output : Fin count) :
    (iterationEntry rhs applied output).data.decode=(rhs.get output).decode-(applied.get output).decode := by
  simp only [iterationEntry,add_value,negate_value,readVector_value,sub_eq_add_neg]

def iteration {count : ℕ} (matrix : Vector (Vector RationalBits count) count)
    (rhs : Vector RationalBits count) : ℕ → ArrayResult count
  | 0 => ⟨Vector.replicate count zero,2*count+2⟩
  | steps+1 =>
    let previous := iteration matrix rhs steps
    let applied := matrixApply matrix previous.data
    let result := buildArray count (iterationEntry rhs applied.data)
    ⟨result.data,previous.work+applied.work+result.work+3⟩

theorem iteration_value {count : ℕ} (matrix : Vector (Vector RationalBits count) count)
    (rhs : Vector RationalBits count) (steps : ℕ) (output : Fin count) :
    ((iteration matrix rhs steps).data.get output).decode=
      linearIteration (fun out inp => ((matrix.get out).get inp).decode) (fun out => (rhs.get out).decode) steps output := by
  induction steps generalizing output with
  | zero => simp [iteration,linearIteration]
  | succ steps ih =>
    simp only [iteration,buildArray_get,iterationEntry_value,matrixApply_value,linearIteration,Pi.sub_apply,AFT.RationalNumerics.matrixApply]
    congr 1
    apply Finset.sum_congr rfl
    intro input _
    rw [ih]

def iterationBits (count bits limit : ℕ) : ℕ :=
  bits+limit*((3*(count^2+count)+1)*bits+count+1)

def iterationWorkStep (count bits limit : ℕ) : ℕ :=
  matrixApplyWork count (iterationBits count bits limit)+
    count*(6*count+13+2*primitiveWorkBound ((count+1)*(2*iterationBits count bits limit+1)))+5

theorem iteration_work {count : ℕ} (matrix : Vector (Vector RationalBits count) count)
    (rhs : Vector RationalBits count) (bits limit steps : ℕ)
    (hm : ∀ output input,HeightBound ((matrix.get output).get input).decode bits)
    (hr : ∀ output,HeightBound (rhs.get output).decode bits) (hs : steps ≤ limit) :
    (iteration matrix rhs steps).work ≤ steps*iterationWorkStep count bits limit+2*count+2 := by
  induction steps with
  | zero => simp [iteration]
  | succ steps ih =>
    let B := iterationBits count bits limit
    let D := (count+1)*(2*B+1)
    have hbits : bits ≤ B := by dsimp [B,iterationBits];omega
    have hp (input : Fin count) : HeightBound ((iteration matrix rhs steps).data.get input).decode B := by
      rw [iteration_value]
      have hh := linearIteration_height (fun out inp => ((matrix.get out).get inp).decode)
        (fun out => (rhs.get out).decode) bits steps hm hr input
      simp only [Fintype.card_fin] at hh
      apply hh.mono
      dsimp [B,iterationBits]
      exact (Nat.mul_le_mul_right _ (show steps ≤ limit by omega)).trans (Nat.le_add_left _ _)
    have ham := matrixApply_work matrix (iteration matrix rhs steps).data B
      (fun out inp => (hm out inp).mono hbits) hp
    have ha (input : Fin count) : HeightBound ((matrixApply matrix (iteration matrix rhs steps).data).data.get input).decode D := by
      rw [matrixApply_value]
      have hh := HeightBound.sum Finset.univ
        (fun inp => ((matrix.get input).get inp).decode*((iteration matrix rhs steps).data.get inp).decode)
        (2*B) (fun inp _ => by exact (((hm input inp).mono hbits).mul (hp inp)).mono (by omega))
      simp only [Finset.card_univ,Fintype.card_fin] at hh
      exact hh.mono (Nat.mul_le_mul_right _ (by omega))
    have he (output : Fin count) :
        (iterationEntry rhs (matrixApply matrix (iteration matrix rhs steps).data).data output).work ≤
          6*count+11+2*primitiveWorkBound D := by
      have hrv := readVector_work zero rhs output
      have hiv := readVector_work zero (matrixApply matrix (iteration matrix rhs steps).data).data output
      have hn := negate_work (readVector zero (matrixApply matrix (iteration matrix rhs steps).data).data output).value D
      have hadd := add_work (readVector zero rhs output).value
        (negate (readVector zero (matrixApply matrix (iteration matrix rhs steps).data).data output).value).data D
        (by rw [readVector_value];exact (hr output).mono (by dsimp [D];nlinarith))
        (by rw [negate_value,readVector_value];exact (ha output).neg)
      simp only [iterationEntry]
      omega
    have hb := buildArray_work count (6*count+11+2*primitiveWorkBound D)
      (iterationEntry rhs (matrixApply matrix (iteration matrix rhs steps).data).data) he
    have hi := ih (by omega)
    simp only [iteration,iterationWorkStep] at *
    dsimp only [B,D] at ham hb
    nlinarith

end AFT.BinaryArithmetic.RationalBits
