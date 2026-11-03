import CurrentAFT.BinaryWindowAverage

/-! # Executed rational sums over stored finite metadata lists -/
namespace CurrentAFT.BinaryListSum
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
variable {Index : Type*}

def current (kernel : Index → RationalResult) : List Index → RationalResult
  | [] => ⟨zero,1⟩
  | index::tail =>
    let remaining := current kernel tail
    let next := kernel index
    let result := RationalBits.add next.data remaining.data
    ⟨result.data,remaining.work+next.work+result.work+2⟩

theorem current_value (kernel : Index → RationalResult) (indices : List Index) :
    (current kernel indices).data.decode=(indices.map (fun index => (kernel index).data.decode)).sum := by
  induction indices with
  | nil => exact zero_value
  | cons index tail ih => simp only [current,RationalBits.add_value,ih,List.map_cons,List.sum_cons]

def height (count bits : ℕ) := count*(bits+1)
def work (count bits budget : ℕ) := count*(budget+primitiveWorkBound ((count+1)*(bits+1))+2)+2

theorem current_height (kernel : Index → RationalResult) (indices : List Index) (bits : ℕ)
    (hh : ∀ index∈indices, HeightBound (kernel index).data.decode bits) :
    HeightBound (current kernel indices).data.decode (height indices.length bits) := by
  induction indices with
  | nil => rw [current,zero_value]; simpa only [height,List.length_nil,Nat.zero_mul] using HeightBound.zero
  | cons index tail ih =>
    rw [current,RationalBits.add_value]
    have ha := hh index List.mem_cons_self
    have hb := ih (fun value hv => hh value (List.mem_cons_of_mem _ hv))
    exact (ha.add hb).mono (by unfold height; simp only [List.length_cons]; nlinarith)

theorem current_work (kernel : Index → RationalResult) (indices : List Index) (bits budget : ℕ)
    (hh : ∀ index∈indices, HeightBound (kernel index).data.decode bits)
    (hw : ∀ index∈indices, (kernel index).work ≤ budget) :
    (current kernel indices).work ≤ work indices.length bits budget := by
  induction indices with
  | nil => simp only [current,List.length_nil,work,Nat.zero_mul,Nat.zero_add]; omega
  | cons index tail ih =>
    have ht := current_height kernel tail bits (fun value hv => hh value (List.mem_cons_of_mem _ hv))
    have ha := hh index List.mem_cons_self
    have wa := hw index List.mem_cons_self
    have hi := ih (fun value hv => hh value (List.mem_cons_of_mem _ hv)) (fun value hv => hw value (List.mem_cons_of_mem _ hv))
    let H := (tail.length+2)*(bits+1)
    have wr := RationalBits.add_work (kernel index).data (current kernel tail).data H
      (ha.mono (by dsimp only [H]; nlinarith)) (ht.mono (by unfold height; dsimp only [H]; nlinarith))
    have hm := primitiveWorkBound_mono (show (tail.length+1)*(bits+1) ≤ H by dsimp only [H]; nlinarith)
    change (current kernel tail).work+(kernel index).work+(RationalBits.add (kernel index).data (current kernel tail).data).work+2 ≤ _
    simp only [List.length_cons,work] at hi ⊢
    change _ ≤ (tail.length+1)*(budget+primitiveWorkBound H+2)+2
    nlinarith only [hi,wa,wr,Nat.mul_le_mul_left tail.length hm]

theorem bounds_mono {count larger bits budget : ℕ} (hc : count ≤ larger) :
    height count bits ≤ height larger bits ∧ work count bits budget ≤ work larger bits budget := by
  constructor
  · unfold height; gcongr
  · unfold work primitiveWorkBound; gcongr

noncomputable def heightPolynomial (count bits : Polynomial ℕ) : Polynomial ℕ := count*(bits+1)
noncomputable def workPolynomial (count bits budget : Polynomial ℕ) : Polynomial ℕ :=
  count*(budget+primitiveWorkPolynomial ((count+1)*(bits+1))+2)+2

theorem heightPolynomial_eval (count bits : Polynomial ℕ) (security : ℕ) :
    (heightPolynomial count bits).eval security=height (count.eval security) (bits.eval security) := by
  simp only [heightPolynomial,height,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_one]
theorem workPolynomial_eval (count bits budget : Polynomial ℕ) (security : ℕ) :
    (workPolynomial count bits budget).eval security=work (count.eval security) (bits.eval security) (budget.eval security) := by
  simp only [workPolynomial,work,primitiveWorkPolynomial_eval,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_ofNat,Polynomial.eval_one]

end CurrentAFT.BinaryListSum
