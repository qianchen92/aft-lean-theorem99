import AFT.BinaryChartArray
import AFT.BinaryLoopControl

/-! Runtime tests and cardinalities for the stored chart Boolean masks. -/
namespace AFT.BinaryArithmetic
open AFT.RationalRejectionProgram
open scoped BigOperators

def equalCounter : ℕ → ℕ → CountedValue Bool
  | 0,0 => ⟨true,2⟩
  | 0,_+1 => ⟨false,2⟩
  | _+1,0 => ⟨false,2⟩
  | first+1,second+1 => let previous := equalCounter first second;⟨previous.value,previous.work+3⟩

theorem equalCounter_value (first second : ℕ) : (equalCounter first second).value=true ↔ first=second := by
  induction first generalizing second with
  | zero => cases second <;> simp [equalCounter]
  | succ first ih => cases second <;> simp [equalCounter,ih]

theorem equalCounter_work (first second : ℕ) :
    (equalCounter first second).work ≤ 3*(first+second)+2 := by
  induction first generalizing second with
  | zero => cases second <;> simp only [equalCounter];all_goals omega
  | succ first ih =>
    cases second with
    | zero => simp only [equalCounter];omega
    | succ second => have hh := ih second;simp only [equalCounter];omega

def countFin : (count : ℕ) → (Fin count → CountedValue Bool) → UnaryCounterResult
  | 0,_ => ⟨0,2⟩
  | count+1,test =>
    let previous := countFin count (fun index => test index.castSucc)
    let current := test (Fin.last count)
    ⟨if current.value then previous.count.succ else previous.count,previous.work+current.work+3⟩

theorem countFin_value (count : ℕ) (test : Fin count → CountedValue Bool) :
    (countFin count test).count=∑ index,if (test index).value then 1 else 0 := by
  induction count with
  | zero => simp [countFin]
  | succ count ih =>
    simp only [countFin,ih,Fin.sum_univ_castSucc]
    split <;> simp_all

theorem countFin_work (count queryWork : ℕ) (test : Fin count → CountedValue Bool)
    (h : ∀ index,(test index).work ≤ queryWork) :
    (countFin count test).work ≤ count*(queryWork+3)+2 := by
  induction count with
  | zero => simp [countFin]
  | succ count ih =>
    have hi := ih (fun index => test index.castSucc) (fun index => h index.castSucc)
    have hh := h (Fin.last count)
    simp only [countFin]
    nlinarith

def maskCount {count : ℕ} (mask : Vector Bool count) : UnaryCounterResult :=
  countFin count (readVector false mask)

/-- The finite set occurs only in the specification, not in the program. -/
def maskSet {count : ℕ} (mask : Vector Bool count) : Finset (Fin count) :=
  Finset.univ.filter (fun index => mask.get index=true)

theorem maskCount_value {count : ℕ} (mask : Vector Bool count) :
    (maskCount mask).count=(maskSet mask).card := by
  simp only [maskCount,countFin_value,readVector_value,maskSet,Finset.card_filter]

theorem maskCount_le {count : ℕ} (mask : Vector Bool count) : (maskCount mask).count ≤ count := by
  rw [maskCount_value]
  simpa using Finset.card_le_univ (maskSet mask)

theorem maskCount_work {count : ℕ} (mask : Vector Bool count) :
    (maskCount mask).work ≤ count*(3*count+6)+2 :=
  countFin_work count (3*count+3) _ (readVector_work false mask)

end AFT.BinaryArithmetic
