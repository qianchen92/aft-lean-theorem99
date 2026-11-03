import CurrentAFT.UniformBodyProfiles
import CurrentAFT.ConditionalPairMean

/-! # Actual root-averaged profiles for each body role and each fixed queue -/

namespace CurrentAFT.BodyRootAverages

open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy FirstHistogram
  UniformBodyProfiles BackgroundCertificates
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ProposalPrimary.centerLaw
  ProposalPrimary.safeLaw

private theorem conjugate_add {Color Group : Type*} [AddCommGroup Group]
    (equiv : Color ≃ Group) (first second : Group) (color : Color) :
    (equiv.trans ((Equiv.addRight second).trans equiv.symm))
      ((equiv.trans ((Equiv.addRight first).trans equiv.symm)) color) =
      (equiv.trans ((Equiv.addRight (first + second)).trans equiv.symm)) color := by
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
  change equiv.symm ((equiv color + first) + second) = equiv.symm (equiv color + (first + second))
  rw [add_assoc]

private noncomputable def cyclicShift (modulus : ℕ) [NeZero modulus] (shift : ℤ) :
    Fin modulus ≃ Fin modulus :=
  (ZMod.finEquiv modulus).toEquiv.trans
    ((Equiv.addRight (shift : ZMod modulus)).trans (ZMod.finEquiv modulus).toEquiv.symm)

private theorem cyclicShift_add (modulus : ℕ) [NeZero modulus] (first second : ℤ)
    (color : Fin modulus) :
    cyclicShift modulus second (cyclicShift modulus first color) =
      cyclicShift modulus (first + second) color := by
  simpa only [cyclicShift, Int.cast_add] using
    conjugate_add (ZMod.finEquiv modulus).toEquiv (first : ZMod modulus) (second : ZMod modulus) color

theorem shiftEquiv_add (security : ℕ) (first second : ℤ)
    (color : LocalReferenceEnergy.Palette security) :
    shiftEquiv security second (shiftEquiv security first color) =
      shiftEquiv security (first + second) color :=
  cyclicShift_add (Parameters.modulus security) first second color

theorem shiftLaw_add (security : ℕ) (law : FiniteDist (LocalReferenceEnergy.Palette security))
    (first second : ℤ) :
    (law.map (shiftEquiv security first)).map (shiftEquiv security second) =
      law.map (shiftEquiv security (first + second)) := by
  rw [FiniteDist.map_map]
  congr 1
  funext color
  exact shiftEquiv_add security first second color

def rootAverage (security : ℕ) (law : FiniteDist (LocalReferenceEnergy.Palette security)) :
    FiniteDist (LocalReferenceEnergy.Palette security) :=
  (publicBlurLaw security).mix fun pair => law.map (shiftEquiv security (pair.2.val - pair.1.val))

theorem rootAverage_seed (security : ℕ) (law : FiniteDist (LocalReferenceEnergy.Palette security)) :
    rootAverage security law = (actualSeedLaw security).mix
      (fun seed => law.map (shiftEquiv security (actualBlur security seed))) := by
  ext output
  simp only [rootAverage, publicBlurLaw, actualSeedLaw, FiniteDist.mix_weight,
    Fintype.sum_prod_type, FiniteDist.prod_weight, FiniteDist.map_equiv_weight,
    actualBlur]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, FiniteDist.sum_one, one_mul]
  ring

theorem rootAverage_free (security : ℕ) :
    rootAverage security (centerLaw security) = convolvedCenterLaw security :=
  rootAverage_seed security (centerLaw security)

theorem rootAverage_safe (security : ℕ) :
    rootAverage security (safeLaw security) = bodyLaw security false := by
  rw [rootAverage_seed]
  unfold bodyLaw
  simp only [Bool.false_eq_true, if_false, add_zero]

theorem rootAverage_map (security : ℕ) (law : FiniteDist (LocalReferenceEnergy.Palette security))
    (shift : ℤ) :
    rootAverage security (law.map (shiftEquiv security shift)) =
      (rootAverage security law).map (shiftEquiv security shift) := by
  simp only [rootAverage, FiniteDist.map_mix]
  congr 1
  funext pair
  rw [shiftLaw_add, shiftLaw_add, add_comm shift]

theorem rootAverage_mix {Choice : Type*} [Fintype Choice] (security : ℕ)
    (choiceLaw : FiniteDist Choice) (laws : Choice → FiniteDist (LocalReferenceEnergy.Palette security)) :
    rootAverage security (choiceLaw.mix laws) = choiceLaw.mix (fun choice => rootAverage security (laws choice)) := by
  ext output
  simp only [rootAverage, FiniteDist.mix_weight, FiniteDist.map_equiv_weight]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro choice _
  apply Finset.sum_congr rfl
  intro pair _
  ring

theorem rootAverage_attachment (security : ℕ) :
    rootAverage security ((scalarLaw security).mix (fun scalar =>
      (safeLaw security).map (shiftEquiv security scalar.val))) = bodyLaw security true := by
  ext output
  simp only [rootAverage, publicBlurLaw, bodyLaw, actualSeedLaw, FiniteDist.mix_weight,
    Fintype.sum_prod_type, FiniteDist.prod_weight, FiniteDist.map_equiv_weight,
    if_true, actualBlur, actualSecond]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro scalar _
  have hshift := congrArg (fun distribution : FiniteDist (LocalReferenceEnergy.Palette security) =>
    distribution.weight output) (shiftLaw_add security (safeLaw security)
      scalar.val (first.val - second.val))
  simp only [FiniteDist.map_equiv_weight] at hshift
  rw [add_comm scalar.val] at hshift
  rw [hshift]
  ring

theorem role_rootAverage (security : ℕ) (role : BodyRole) (queue : ℤ) :
    rootAverage security (preRootLaw security role queue) =
      match role with
      | .free => convolvedCenterLaw security
      | .attachment => bodyLaw security true
      | .queue => (bodyLaw security false).map (shiftEquiv security queue) := by
  cases role with
  | free => exact rootAverage_free security
  | attachment => exact rootAverage_attachment security
  | queue => rw [preRootLaw, rootAverage_map, rootAverage_safe]

end

end CurrentAFT.BodyRootAverages
