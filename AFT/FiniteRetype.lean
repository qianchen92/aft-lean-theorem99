import AFT.FiniteProbability

/-! # Transport a finite probability law across the unique Fintype instance -/

namespace AFT.FiniteDist

open scoped BigOperators

/-- Only the finite enumeration instance changes. All point weights are
literally preserved, and total mass follows by uniqueness of `Fintype`. -/
def retype {α : Type*} {source : Fintype α} [target : Fintype α]
    (law : @FiniteDist α source) : FiniteDist α where
  weight := @FiniteDist.weight α source law
  nonneg := @FiniteDist.nonneg α source law
  sum_one := by
    have h : source = target := Subsingleton.elim _ _
    cases h
    exact law.sum_one

@[simp] theorem retype_weight {α : Type*} {source : Fintype α} [target : Fintype α]
    (law : @FiniteDist α source) (point : α) : (retype law).weight point = @FiniteDist.weight α source law point := rfl

end AFT.FiniteDist
