import AFT.FiniteExpectationAlgebra

/-! # Executable finite-table sampling from a uniformly selected ticket

The selection function uses comparisons and subtraction only. The theorem
below identifies its complete output law for every integer count table.
-/

namespace AFT.FiniteTicketSampler

open scoped BigOperators Classical

/-- Index of the bucket containing a ticket, in the specified table order. -/
def bucket : List ℕ → ℕ → ℕ
  | [], _ => 0
  | count :: rest, ticket => if ticket < count then 0 else 1 + bucket rest (ticket - count)

theorem bucket_lt_length (counts : List ℕ) (ticket : ℕ) (h : ticket < counts.sum) :
    bucket counts ticket < counts.length := by
  induction counts generalizing ticket with
  | nil => simp at h
  | cons count rest ih =>
    simp only [List.sum_cons] at h
    simp only [bucket, List.length_cons]
    split_ifs with hfirst
    · omega
    · have hh := ih (ticket - count) (by omega)
      omega

/-- Exactly the declared number of tickets selects each table entry,
including zero-count entries and indices beyond the end of the table. -/
theorem bucket_count (counts : List ℕ) (index : ℕ) :
    (∑ ticket ∈ Finset.range counts.sum, if bucket counts ticket = index then 1 else 0) =
      counts[index]?.getD 0 := by
  induction counts generalizing index with
  | nil => simp
  | cons count rest ih =>
    rw [List.sum_cons, Finset.sum_range_add]
    have hfirst (ticket : ℕ) (ht : ticket ∈ Finset.range count) :
        bucket (count :: rest) ticket = 0 := by
      simp only [bucket, if_pos (Finset.mem_range.mp ht)]
    have hsecond (ticket : ℕ) : bucket (count :: rest) (count + ticket) = 1 + bucket rest ticket := by
      simp only [bucket, show ¬count + ticket < count by omega, if_false, Nat.add_sub_cancel_left]
    simp_rw [hsecond]
    cases index with
    | zero =>
      have hf : (∑ ticket ∈ Finset.range count, if bucket (count :: rest) ticket = 0 then 1 else 0) = count := by
        calc
          _ = ∑ _ticket ∈ Finset.range count, (1 : ℕ) := by
            apply Finset.sum_congr rfl
            intro ticket ht
            rw [hfirst ticket ht]
            simp
          _ = _ := by simp
      simp [hf]
    | succ index =>
      have hf : (∑ ticket ∈ Finset.range count,
          if bucket (count :: rest) ticket = index + 1 then 1 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro ticket ht
        rw [hfirst ticket ht]
        simp
      simp only [hf, zero_add, Nat.add_comm 1, Nat.add_right_cancel_iff,
        List.getElem?_cons_succ, ih]

/-- This function is executable for any natural count table. -/
def draw (counts : List ℕ) (ticket : Fin counts.sum) : Fin counts.length :=
  ⟨bucket counts ticket.val, bucket_lt_length counts ticket.val ticket.isLt⟩

/-- An explicit list table with total `T` is sampled exactly using one
uniform integer in `[0,T)`. No real-valued sampling oracle is assumed. -/
theorem draw_law (counts : List ℕ) (hpositive : 0 < counts.sum) (index : Fin counts.length) :
    (by
      letI : NeZero counts.sum := ⟨hpositive.ne'⟩
      exact ((FiniteDist.uniform (Fin counts.sum)).map (draw counts)).weight index) =
      ((counts[index.val]?.getD 0 : ℕ) : ℝ) / counts.sum := by
  letI : NeZero counts.sum := ⟨hpositive.ne'⟩
  have hcount := bucket_count counts index.val
  have hreal : (∑ ticket ∈ Finset.range counts.sum,
      if bucket counts ticket = index.val then (1 : ℝ) else 0) = counts[index.val]?.getD 0 := by
    exact_mod_cast hcount
  simp only [FiniteDist.map_weight, FiniteDist.uniform_weight, Fintype.card_fin,
    draw, Fin.ext_iff]
  simp_rw [show ∀ ticket : Fin counts.sum,
    (if bucket counts ticket.val = index.val then (counts.sum : ℝ)⁻¹ else 0) =
      (counts.sum : ℝ)⁻¹ * (if bucket counts ticket.val = index.val then 1 else 0) from
        fun ticket => by split_ifs <;> simp]
  rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range
    (fun ticket => if bucket counts ticket = index.val then (1 : ℝ) else 0) counts.sum, hreal]
  ring

end AFT.FiniteTicketSampler
