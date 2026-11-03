import AFT.OrderedSeedFactors
import AFT.Correction

/-! # Exact finite inverse semantics and size of ordered column programs -/
namespace AFT.RationalNumerics
open RepresentedPolynomial
open scoped BigOperators

variable {Code : Type*}

theorem OrderedSeedTable.scale_length (scalar : ℚ) (table : OrderedSeedTable Code) :
    (table.scale scalar).length=table.length := List.length_map ..

theorem OrderedSeedTable.applyColumns_length (columns : List Code → OrderedSeedTable Code)
    (table : OrderedSeedTable Code) (bound : ℕ) (hbound : ∀ term∈table,(columns term.factors).length ≤ bound) :
    (table.applyColumns columns).length ≤ table.length*bound := by
  induction table with
  | nil => simp [OrderedSeedTable.applyColumns]
  | cons term table ih =>
    simp only [OrderedSeedTable.applyColumns,List.flatMap_cons,List.length_append,scale_length,List.length_cons]
    exact (Nat.add_le_add (hbound term (List.mem_cons_self ..))
      (ih (fun other ho => hbound other (List.mem_cons_of_mem _ ho)))).trans_eq (by ring)

/-- For fixed inverse depth, a polynomial column-size bound gives a
polynomial total-size bound; no compressed-kernel operation is needed. -/
theorem OrderedSeedTable.correction_length (columns : List Code → OrderedSeedTable Code)
    (target : OrderedSeedTable Code) (bound : ℕ) (hbound : ∀ factors,(columns factors).length ≤ bound)
    (depth : ℕ) :
    (OrderedSeedTable.correction columns target depth).length ≤ target.length*(bound+1)^depth := by
  induction depth with
  | zero => simp [OrderedSeedTable.correction]
  | succ depth ih =>
    simp only [OrderedSeedTable.correction,List.length_append,scale_length]
    have hcolumn := applyColumns_length columns (OrderedSeedTable.correction columns target depth) bound
      (fun term _ => hbound term.factors)
    have hpow : 1 ≤ (bound+1)^depth := Nat.one_le_pow _ _ (by omega)
    calc
      _ ≤ target.length+(target.length*(bound+1)^depth)*bound :=
        Nat.add_le_add_left (hcolumn.trans (Nat.mul_le_mul_right bound ih)) _
      _ ≤ target.length*(bound+1)^depth+(target.length*(bound+1)^depth)*bound := by
        gcongr
        exact Nat.le_mul_of_pos_right _ hpow
      _ = _ := by rw [pow_succ]; ring

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {Seed : Type*}

private theorem correction_succ_linear (linear : Module.End ℝ (Table Seed)) (depth : ℕ) :
    finiteCorrection linear (depth+1)=1-linear*finiteCorrection linear depth := by
  unfold finiteCorrection
  rw [Finset.sum_range_succ']
  simp only [pow_succ',pow_zero,←Finset.mul_sum]
  have hm (other : Module.End ℝ (Table Seed)) : (-linear)*other= -(linear*other) := by
    ext table powers
    rfl
  rw [hm,sub_eq_add_neg,add_comm]

/-- Executing the ordered-list recurrence agrees with the actual finite
Neumann sum whenever its concrete columns have the stated exact semantics. -/
theorem OrderedSeedTable.interpret_correction (decode : Code → Seed)
    (columns : List Code → OrderedSeedTable Code) (linear : Module.End ℝ (Table Seed))
    (hcolumns : ∀ factors,(columns factors).interpret decode=
      linear ((factors.map (fun code => MvPolynomial.X (decode code))).prod))
    (target : OrderedSeedTable Code) (depth : ℕ) :
    (OrderedSeedTable.correction columns target depth).interpret decode=
      finiteCorrection linear depth (target.interpret decode) := by
  induction depth with
  | zero => simp [OrderedSeedTable.correction,finiteCorrection]
  | succ depth ih =>
    rw [OrderedSeedTable.correction,interpret_append,interpret_scale,
      interpret_applyColumns decode columns linear _ (fun term _ => hcolumns term.factors),ih,
      correction_succ_linear]
    simp only [Rat.cast_neg,Rat.cast_one,neg_one_smul,sub_eq_add_neg,LinearMap.add_apply,LinearMap.neg_apply,Module.End.one_apply,
      Module.End.mul_apply]

end
end AFT.RationalNumerics
