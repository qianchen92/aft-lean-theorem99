import AFT.FiniteRetype
import AFT.TotalVariation

/-! # Statistical distances do not depend on a finite enumeration instance -/
namespace CurrentAFT.FiniteEnumeration
open AFT
open scoped BigOperators Classical
noncomputable section

theorem totalVariation_retype {State : Type*} {source target : Fintype State}
    (first second : @FiniteDist State source) :
    @FiniteDist.totalVariation State target (@FiniteDist.retype State source target first)
      (@FiniteDist.retype State source target second) = @FiniteDist.totalVariation State source first second := by
  cases Subsingleton.elim source target
  rfl

theorem totalVariation_eq_of_weights {State : Type*} {source target : Fintype State}
    (first second : @FiniteDist State source) (first' second' : @FiniteDist State target)
    (hfirst : ∀ point, @FiniteDist.weight State source first point = @FiniteDist.weight State target first' point)
    (hsecond : ∀ point, @FiniteDist.weight State source second point = @FiniteDist.weight State target second' point) :
    @FiniteDist.totalVariation State source first second = @FiniteDist.totalVariation State target first' second' := by
  cases Subsingleton.elim source target
  rw [FiniteDist.ext hfirst, FiniteDist.ext hsecond]

theorem tvBound_retype {State : Type*} {source target : Fintype State}
    (first second : @FiniteDist State source) (error : ℝ) :
    @FiniteDist.TVBound State target (@FiniteDist.retype State source target first)
      (@FiniteDist.retype State source target second) error ↔ @FiniteDist.TVBound State source first second error := by
  cases Subsingleton.elim source target
  rfl

end
end CurrentAFT.FiniteEnumeration
