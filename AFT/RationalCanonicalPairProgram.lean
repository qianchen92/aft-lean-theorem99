import AFT.NumericalPairFamily

/-! A natural-number indexed implementation of finite pair canonicalization. -/
namespace AFT.RationalNumerics
open scoped BigOperators

def rationalCanonicalPairProgram (colors : ℕ) (reference : ℕ → ℚ) (mass : ℕ → ℕ → ℚ)
    (first second : ℕ) : ℚ :=
  mass first second-reference first*(∑ point∈Finset.range colors,mass point second)-
    (∑ point∈Finset.range colors,mass first point)*reference second+
    (∑ first∈Finset.range colors,∑ second∈Finset.range colors,mass first second)*reference first*reference second

theorem rationalCanonicalPairProgram_fin (colors : ℕ) (reference : ℕ → ℚ) (mass : ℕ → ℕ → ℚ)
    (first second : Fin colors) :
    rationalCanonicalPairProgram colors reference mass first.val second.val=
      rationalCanonicalPair (fun color : Fin colors => reference color.val)
        (fun first second : Fin colors => mass first.val second.val) first second := by
  simp only [rationalCanonicalPairProgram,rationalCanonicalPair,←Fin.sum_univ_eq_sum_range]

end AFT.RationalNumerics
