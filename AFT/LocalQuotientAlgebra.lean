import AFT.BackgroundQueueAlgebra

/-! # The nonlinear difference of a literal finite local quotient -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
variable {Seed : Type*}

def localUpperTable (linear higher positiveError : Table Seed) (depth : ℕ) : Table Seed :=
  (linear+higher)*finiteCorrection positiveError depth-linear

theorem localUpperTable_formula (linear higher positiveError : Table Seed) (depth : ℕ) :
    localUpperTable linear higher positiveError depth =
      higher*finiteCorrection positiveError depth+linear*(finiteCorrection positiveError depth-1) := by
  unfold localUpperTable
  ring

theorem localUpperTable_activity_le (weight : Seed → ℝ) (hw : ∀ seed,0 ≤ weight seed)
    (linear higher positiveError : Table Seed) (depth : ℕ)
    (hs : activity weight positiveError ≤ 1/2) :
    activity weight (localUpperTable linear higher positiveError depth) ≤
      2*activity weight higher+2*activity weight positiveError*activity weight linear := by
  rw [localUpperTable_formula]
  apply (activity_add_le weight hw _ _).trans
  have hf := activity_finiteCorrection_le_two weight hw positiveError depth hs
  have he := activity_finiteCorrection_sub_one_le weight hw positiveError depth hs
  have hfirst := (activity_mul_le weight hw higher _).trans
    (mul_le_mul_of_nonneg_left hf (activity_nonneg weight hw higher))
  have hsecond := (activity_mul_le weight hw linear _).trans
    (mul_le_mul_of_nonneg_left he (activity_nonneg weight hw linear))
  exact (add_le_add hfirst hsecond).trans_eq (by ring)

theorem localUpperTable_hasOrder (order : Seed → ℕ) (linear higher positiveError : Table Seed)
    (depth : ℕ) (hl : HasOrder order 1 linear) (hh : HasOrder order 2 higher)
    (he : HasOrder order 1 positiveError) :
    HasOrder order 2 (localUpperTable linear higher positiveError depth) := by
  rw [localUpperTable_formula]
  have hfirst := hasOrder_mul order 2 0 higher (finiteCorrection positiveError depth) hh
    (hasOrder_zero _ _)
  have hsecond := hasOrder_mul order 1 1 linear (finiteCorrection positiveError depth-1) hl
    (hasOrder_finiteCorrection_sub_one order positiveError depth he)
  intro powers hp
  rw [MvPolynomial.coeff_add, hfirst powers hp, hsecond powers hp]
  simp

/-- A local quotient replacement raises the order of the complete joint
input, including every unchanged primary and body coordinate. -/
theorem localUpperTable_hasOrder_relative (order : Seed → ℕ) (minimum : ℕ)
    (linear higher positiveError : Table Seed) (depth : ℕ)
    (hl : HasOrder order minimum linear) (hh : HasOrder order (minimum+1) higher)
    (he : HasOrder order 1 positiveError) :
    HasOrder order (minimum+1) (localUpperTable linear higher positiveError depth) := by
  rw [localUpperTable_formula]
  have hfirst := hasOrder_mul order (minimum+1) 0 higher (finiteCorrection positiveError depth) hh
    (hasOrder_zero _ _)
  have hsecond := hasOrder_mul order minimum 1 linear (finiteCorrection positiveError depth-1) hl
    (hasOrder_finiteCorrection_sub_one order positiveError depth he)
  intro powers hp
  rw [MvPolynomial.coeff_add,hfirst powers hp,hsecond powers hp]
  simp

end
end AFT.RepresentedPolynomial
