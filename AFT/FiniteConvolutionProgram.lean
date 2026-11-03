import AFT.RootMarginal
import AFT.ClippedSource

/-! # Materialized finite convolution tables

The executable recurrence stores each complete previous row in an array.
It does not enumerate all source words or recursively recompute its cells.
The work counter counts elementary arithmetic, comparisons and array accesses;
bit costs of the coefficient arithmetic remain separate.
-/
namespace AFT.FiniteConvolutionProgram
open scoped BigOperators

structure Result (R : Type*) where
  data : Array R
  work : ℕ

def lookup {R : Type*} [Zero R] (data : Array R) (target : ℕ) : R :=
  data[target]?.getD 0

/-- `alphabet` is the greatest source index. The previous row is evaluated
once and materialized before constructing the next row. -/
def run {R : Type*} [Semiring R] (alphabet : ℕ) (weight : Fin (alphabet+1) → R) : ℕ → Result R
  | 0 => ⟨#[1],1⟩
  | count+1 =>
      let previous := run alphabet weight count
      ⟨Array.ofFn (fun target : Fin (alphabet*(count+1)+1) =>
        ∑ source : Fin (alphabet+1),if source.val ≤ target.val then
          weight source*lookup previous.data (target.val-source.val) else 0),
        previous.work+(alphabet*(count+1)+1)*(5*(alphabet+1)+2)⟩

theorem run_size {R : Type*} [Semiring R] (alphabet : ℕ)
    (weight : Fin (alphabet+1) → R) (count : ℕ) :
    (run alphabet weight count).data.size=alphabet*count+1 := by
  cases count <;> simp [run]

theorem lookup_ofFn {R : Type*} [Zero R] {size : ℕ} (value : Fin size → R) (target : ℕ) :
    lookup (Array.ofFn value) target=if h : target<size then value ⟨target,h⟩ else 0 := by
  unfold lookup
  by_cases h : target<size
  · rw [dif_pos h,Array.getElem?_eq_getElem (by simpa only [Array.size_ofFn] using h),Option.getD_some,Array.getElem_ofFn]
  · rw [dif_neg h,Array.getElem?_eq_none (by simpa only [Array.size_ofFn] using Nat.le_of_not_gt h),Option.getD_none]

noncomputable section
open scoped Classical

def wordCoefficient {R : Type*} [CommSemiring R] (alphabet : ℕ)
    (weight : Fin (alphabet+1) → R) (count target : ℕ) : R :=
  ∑ word : Fin count → Fin (alphabet+1),if (∑ i,(word i).val)=target then ∏ i,weight (word i) else 0

theorem wordCoefficient_outside {R : Type*} [CommSemiring R] (alphabet : ℕ)
    (weight : Fin (alphabet+1) → R) (count target : ℕ) (hout : alphabet*count<target) :
    wordCoefficient alphabet weight count target=0 := by
  apply Finset.sum_eq_zero
  intro word _
  have hb : (∑ i : Fin count,(word i).val) ≤ alphabet*count := by
    calc
      _ ≤ ∑ _i : Fin count,alphabet := Finset.sum_le_sum fun i _ => by have hi := (word i).isLt; omega
      _ = _ := by simp [Nat.mul_comm]
  rw [if_neg (by omega)]

theorem wordCoefficient_succ {R : Type*} [CommSemiring R] (alphabet : ℕ)
    (weight : Fin (alphabet+1) → R) (count target : ℕ) :
    wordCoefficient alphabet weight (count+1) target=
      ∑ source : Fin (alphabet+1),if source.val ≤ target then
        weight source*wordCoefficient alphabet weight count (target-source.val) else 0 := by
  unfold wordCoefficient
  rw [← (Fin.consEquiv (fun _ : Fin (count+1) => Fin (alphabet+1))).sum_comp,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro source _
  simp only [Fin.consEquiv_apply,Fin.sum_univ_succ,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
  by_cases hs : source.val ≤ target
  · rw [if_pos hs,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro tail _
    have he : source.val+(∑ i,(tail i).val)=target ↔ (∑ i,(tail i).val)=target-source.val := by omega
    simp only [he,mul_ite,mul_zero]
  · rw [if_neg hs]
    apply Finset.sum_eq_zero
    intro tail _
    rw [if_neg (by omega)]

/-- Every array entry is the exact coefficient of the full independent
source sum, including the zero values outside its attainable interval. -/
theorem run_correct {R : Type*} [CommSemiring R] (alphabet : ℕ)
    (weight : Fin (alphabet+1) → R) (count target : ℕ) :
    lookup (run alphabet weight count).data target=wordCoefficient alphabet weight count target := by
  induction count generalizing target with
  | zero =>
    cases target <;> simp [run,lookup,wordCoefficient]
  | succ count ih =>
    rw [run,lookup_ofFn]
    split_ifs with ht
    · rw [wordCoefficient_succ]
      apply Finset.sum_congr rfl
      intro source _
      simp only [ih]
    · rw [wordCoefficient_outside alphabet weight (count+1) target (by omega)]

/-- The explicitly charged work is polynomial in the number of convolutions
and the source support, independent of the number of full source words. -/
theorem run_work_le {R : Type*} [Semiring R] (alphabet : ℕ)
    (weight : Fin (alphabet+1) → R) (count : ℕ) :
    (run alphabet weight count).work ≤ 1+7*count*(alphabet*count+1)*(alphabet+1) := by
  induction count with
  | zero => simp [run]
  | succ count ih =>
    change (run alphabet weight count).work+(alphabet*(count+1)+1)*(5*(alphabet+1)+2) ≤ _
    have hh : 7*count*(alphabet*count+1)*(alphabet+1) ≤
        7*count*(alphabet*(count+1)+1)*(alphabet+1) := by gcongr; omega
    have hs : 5*(alphabet+1)+2 ≤ 7*(alphabet+1) := by omega
    calc
      _ ≤ (1+7*count*(alphabet*(count+1)+1)*(alphabet+1))+
          (alphabet*(count+1)+1)*(7*(alphabet+1)) :=
        add_le_add (ih.trans (Nat.add_le_add_left hh 1)) (Nat.mul_le_mul_left _ hs)
      _ = _ := by ring

end
end AFT.FiniteConvolutionProgram
