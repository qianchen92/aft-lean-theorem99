import CurrentAFT.RootMeanPrimary
import CurrentAFT.RootLocalDenominators
import CurrentAFT.OrdinaryRaising

/-! Equality of the literal primary denominator data for free root means
and ordinary groups, before polynomial evaluation. -/
namespace CurrentAFT.RootOrdinaryDataIdentity
open AFT
open scoped Classical
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem meanProfile_free (security : ℕ) :
    RootMeanPrimary.meanProfile security .free 0 = OrdinaryRaising.deviation security := by
  unfold RootMeanPrimary.meanProfile OrdinaryRaising.deviation
  rw [RootLocalDenominators.meanLaw_free, RootLocalDenominators.uniformReference_eq]

theorem positiveAtom_free (security order : ℕ) (horder : 1 ≤ order) :
    RootMeanPrimary.positiveAtom security order horder .free 0 = OrdinaryRaising.positiveAtom security order horder := by
  unfold RootMeanPrimary.positiveAtom OrdinaryRaising.positiveAtom
  congr 1
  exact congrArg PrimaryMassFamilies.oneWordProfile (meanProfile_free security)

theorem positiveFamily_free (security order : ℕ) (horder : 1 ≤ order) :
    RootMeanPrimary.positiveFamily security order horder .free 0 = OrdinaryRaising.positiveFamily security order horder := by
  unfold RootMeanPrimary.positiveFamily OrdinaryRaising.positiveFamily
  rw [positiveAtom_free]

theorem positiveInverse_free (security order : ℕ) (horder : 1 ≤ order) :
    RootMeanPrimary.positiveInverse security order horder .free 0 = OrdinaryRaising.positiveInverse security order horder := by
  unfold RootMeanPrimary.positiveInverse OrdinaryRaising.positiveInverse
  rw [positiveFamily_free]

end
end CurrentAFT.RootOrdinaryDataIdentity
