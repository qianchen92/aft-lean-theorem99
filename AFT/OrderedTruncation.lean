import AFT.OrderedCorrectionSemantics

/-! # Ordered term filtering implements the literal weighted cutoff -/
namespace AFT.RationalNumerics
open RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
variable {Code Seed : Type*}

theorem OrderedSeedTable.interpret_truncate (decode : Code → Seed)
    (order : Seed → ℕ) (codeOrder : Code → ℕ) (horder : ∀ code,order (decode code)=codeOrder code)
    (cutoff : ℕ) (table : OrderedSeedTable Code) :
    (table.truncate codeOrder cutoff).interpret decode=RepresentedPolynomial.truncate order cutoff (table.interpret decode) := by
  have hterm (term : OrderedSeedTerm Code) :
      RepresentedPolynomial.truncate order cutoff (term.interpret decode)=
        if (term.factors.map codeOrder).sum ≤ cutoff then term.interpret decode else 0 := by
    rw [OrderedSeedTerm.interpret_monomial]
    have hsum : weightedOrder order (orderedSeedPowers decode term.factors)=(term.factors.map codeOrder).sum := by
      rw [orderedSeedPowers_order]
      simp only [horder]
    ext powers
    simp only [coeff_truncate,MvPolynomial.coeff_monomial]
    by_cases hp : powers=orderedSeedPowers decode term.factors
    · subst powers
      simp only [hsum,if_true]
      split_ifs <;> simp
    · simp only [if_neg (Ne.symm hp)]
      split_ifs <;> simp [Ne.symm hp]
  induction table with
  | nil => simp only [OrderedSeedTable.truncate,List.filter_nil,OrderedSeedTable.interpret_nil,truncate_zero]
  | cons term table ih =>
    change interpret decode (List.filter (fun term => decide ((term.factors.map codeOrder).sum ≤ cutoff)) table)=_ at ih
    by_cases ht : (term.factors.map codeOrder).sum ≤ cutoff
    · simp only [OrderedSeedTable.truncate,List.filter_cons,ht,decide_true,if_true,
        OrderedSeedTable.interpret_cons,truncate_add,hterm,ih]
    · simp only [OrderedSeedTable.truncate,List.filter_cons,ht,decide_false,Bool.false_eq_true,if_false,
        OrderedSeedTable.interpret_cons,truncate_add,hterm,ih]
      simp only [zero_add]

end
end AFT.RationalNumerics
