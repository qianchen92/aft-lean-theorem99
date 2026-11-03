import CurrentAFT.AffineLegReference
import CurrentAFT.ActualPublicCharge

/-!
# Removing the auxiliary activation bits before positive public sampling

The reference activation bit is not the real public chart flag.  Both the
clipped coefficient weight and public charge predicate ignore every such
bit.  Thus their public sampling law can first forget these bits, then use
the genuine half-flag chart completion of `AffineLegReference`.
-/

namespace CurrentAFT.AffineFlagCalibration

open AFT ActualPublicCharge
open scoped BigOperators Classical

noncomputable section

def setActivationBits (security : ℕ) (core : Core security)
    (bits : Fin (Parameters.legCount security) → Bool) : Core security :=
  { core with legs := fun leg =>
      (setMarked security (core.legs leg).1 (bits leg), (core.legs leg).2) }

def eraseActivation (security : ℕ) (core : Core security) : Core security :=
  setActivationBits security core (fun _ => false)

theorem pulledWeight_setActivationBits (security order : ℕ)
    (coefficient : ActualControls.Coefficients security order) (core : Core security)
    (bits : Fin (Parameters.legCount security) → Bool) :
    pulledWeight security order coefficient (setActivationBits security core bits) =
      pulledWeight security order coefficient core := rfl

theorem chargeValue_setActivationBits (security : ℕ) (core : Core security)
    (bits : Fin (Parameters.legCount security) → Bool) :
    chargeValue security (setActivationBits security core bits) = chargeValue security core := rfl

theorem publicCharge_setActivationBits (security : ℕ) (core : Core security)
    (bits : Fin (Parameters.legCount security) → Bool) :
    publicCharge security (setActivationBits security core bits) ↔ publicCharge security core := Iff.rfl

/-- The actual bounded nonnegative multiplier, including charge selection. -/
def positiveMultiplier (security order : ℕ)
    (coefficient : ActualControls.Coefficients security order) (core : Core security) : ℝ :=
  clip (pulledWeight security order coefficient core) * if publicCharge security core then 1 else 0

theorem positiveMultiplier_setActivationBits (security order : ℕ)
    (coefficient : ActualControls.Coefficients security order) (core : Core security)
    (bits : Fin (Parameters.legCount security) → Bool) :
    positiveMultiplier security order coefficient (setActivationBits security core bits) =
      positiveMultiplier security order coefficient core := rfl

theorem eraseActivation_idempotent (security : ℕ) (core : Core security) :
    eraseActivation security (eraseActivation security core) = eraseActivation security core := rfl

/-- Both numerator and normalizing mass of the positive public law can be
computed after erasing the auxiliary activation bits.  The test may be any
function of all the remaining public core coordinates. -/
theorem positive_erasure_expectation (security order : ℕ)
    (coefficient : ActualControls.Coefficients security order) (test : Core security → ℝ) :
    (proposal security).expectation (fun core =>
      positiveMultiplier security order coefficient core * test (eraseActivation security core)) =
      ((proposal security).map (eraseActivation security)).expectation
        (fun core => positiveMultiplier security order coefficient core * test core) := by
  rw [FiniteDist.expectation_map]
  rfl

theorem positive_erasure_mass (security order : ℕ)
    (coefficient : ActualControls.Coefficients security order) :
    (proposal security).expectation (positiveMultiplier security order coefficient) =
      ((proposal security).map (eraseActivation security)).expectation
        (positiveMultiplier security order coefficient) := by
  rw [FiniteDist.expectation_map]
  rfl

end
end CurrentAFT.AffineFlagCalibration
