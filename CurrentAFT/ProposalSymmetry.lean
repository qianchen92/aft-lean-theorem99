import CurrentAFT.ProposalCenter
import AFT.ReflectionCalibration
import AFT.GaussianReflection

/-!
# Reflection symmetry and the fair actual inward-anchor sign

The reflection acts simultaneously on the three actual protected Gaussian
scalars. It preserves their joint product weight and reverses both the
public blur and the protected second input. The diffuse profiles and cyclic
body profiles are then reflected before applying the current primary
balancing formula. No frozen-V7 primary law or parameter family is used.

The anchor's direction uses the actual midpoint fair coin. Its exact fair
law is proved from the reflection of the actual constructed primary law,
not supplied as a sign-mixture assumption.
-/

namespace CurrentAFT.ProposalSymmetry

open AFT DiffuseProfiles ProposalPrimary
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth
  Parameters.sourceCutoff Parameters.safeMargin DiffuseProfiles.activation

def seedNegate (security : ℕ) : ActualSeed security ≃ ActualSeed security :=
  ((GaussianSource.windowNegateEquiv (edgeCutoff security)).prodCongr
    (GaussianSource.windowNegateEquiv (edgeCutoff security))).prodCongr
      (GaussianSource.windowNegateEquiv (Parameters.sourceCutoff security - 1))

theorem seedNegate_weight (security : ℕ) (seed : ActualSeed security) :
    (actualSeedLaw security).weight (seedNegate security seed) = (actualSeedLaw security).weight seed := by
  simp only [actualSeedLaw, seedNegate, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, FiniteDist.prod_weight,
    edgeLaw, scalarLaw, GaussianSource.windowGaussian_reflection]

theorem actualBlur_negate (security : ℕ) (seed : ActualSeed security) :
    actualBlur security (seedNegate security seed) = -actualBlur security seed := by
  simp only [actualBlur, seedNegate, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
    GaussianSource.windowNegateEquiv_val]
  ring

theorem actualSecond_negate (security : ℕ) (seed : ActualSeed security) :
    actualSecond security (seedNegate security seed) = -actualSecond security seed := rfl

theorem palette_rev_value (modulus : ℕ) (color : Fin modulus) :
    (color.rev.val : ℤ) = (modulus : ℤ) - 1 - color.val := by
  simp only [Fin.val_rev]
  omega

theorem intervalStart_reflection (positive : Bool) (width : ℕ) (blur : ℤ) :
    intervalStart (!positive) width (-blur) =
      TrimmedSlice.reflectedStart (intervalStart positive width blur) width := by
  cases positive <;> simp only [Bool.not_false, Bool.not_true, intervalStart,
    Bool.false_eq_true, if_false, if_true, TrimmedSlice.reflectedStart] <;> ring

theorem actualProfile_reflection (security : ℕ) (positive : Bool)
    (color : Fin (Parameters.modulus security)) :
    actualProfile security positive color.rev = actualProfile security (!positive) color := by
  unfold actualProfile profile
  rw [palette_rev_value]
  exact TrimmedSlice.mixedLaw_reflection _ _ _
    (fun seed => intervalStart positive (Parameters.anchorWidth security) (actualBlur security seed))
    (fun seed => intervalStart (!positive) (Parameters.anchorWidth security) (actualBlur security seed))
    (actualSecond security) (actualSeedLaw security).weight (seedNegate security)
    (seedNegate_weight security) (actualSecond_negate security)
    (fun seed => by dsimp only; rw [actualBlur_negate, intervalStart_reflection]) _

theorem safeLaw_reflection (security : ℕ) (color : Fin (Parameters.modulus security)) :
    (safeLaw security).weight color.rev = (safeLaw security).weight color := by
  rw [safeLaw, TrimmedSlice.finiteLaw_weight, TrimmedSlice.finiteLaw_weight,
    palette_rev_value, TrimmedSlice.law_reflection, neg_zero]

def shiftColor (modulus : ℕ) [NeZero modulus] (shift : ℤ) : Fin modulus :=
  (ZMod.finEquiv modulus).symm (shift : ZMod modulus)

theorem shiftColor_neg (modulus : ℕ) [NeZero modulus] (shift : ℤ) :
    shiftColor modulus (-shift) = -shiftColor modulus shift := by
  simp only [shiftColor, Int.cast_neg, map_neg]

private theorem cyclicShift_apply (modulus : ℕ) [NeZero modulus] (shift : ℤ) (color : Fin modulus) :
    ((ZMod.finEquiv modulus).toEquiv.trans
      ((Equiv.addRight (shift : ZMod modulus)).trans (ZMod.finEquiv modulus).toEquiv.symm)) color =
        color + shiftColor modulus shift := by
  apply (ZMod.finEquiv modulus).injective
  change (ZMod.finEquiv modulus)
      ((ZMod.finEquiv modulus).symm ((ZMod.finEquiv modulus) color + (shift : ZMod modulus))) = _
  simp only [RingEquiv.apply_symm_apply, map_add, shiftColor]

theorem shiftEquiv_apply (security : ℕ) (shift : ℤ) (color : Fin (Parameters.modulus security)) :
    shiftEquiv security shift color = color + shiftColor (Parameters.modulus security) shift :=
  cyclicShift_apply _ _ _

theorem shiftEquiv_symm_apply (security : ℕ) (shift : ℤ) (color : Fin (Parameters.modulus security)) :
    (shiftEquiv security shift).symm color = shiftEquiv security (-shift) color := by
  apply (shiftEquiv security shift).injective
  rw [Equiv.apply_symm_apply]
  simp only [shiftEquiv_apply, shiftColor_neg]
  abel

theorem shiftEquiv_reflection (security : ℕ) (shift : ℤ) (color : Fin (Parameters.modulus security)) :
    shiftEquiv security (-shift) color.rev = (shiftEquiv security shift color).rev := by
  simp only [shiftEquiv_apply, Fin.rev_add, shiftColor_neg, sub_eq_add_neg]

theorem shiftEquiv_symm_reflection (security : ℕ) (shift : ℤ) (color : Fin (Parameters.modulus security)) :
    (shiftEquiv security (-shift)).symm color.rev = ((shiftEquiv security shift).symm color).rev := by
  simp only [shiftEquiv_symm_apply, neg_neg]
  simpa only [neg_neg] using shiftEquiv_reflection security (-shift) color

theorem body_shift_negate (security : ℕ) (includeScalar : Bool) (seed : ActualSeed security) :
    actualBlur security (seedNegate security seed) +
        (if includeScalar then actualSecond security (seedNegate security seed) else 0) =
      -(actualBlur security seed + if includeScalar then actualSecond security seed else 0) := by
  rw [actualBlur_negate, actualSecond_negate]
  cases includeScalar <;> simp only [Bool.false_eq_true, if_false, if_true] <;> ring

theorem bodyLaw_reflection (security : ℕ) (includeScalar : Bool)
    (color : Fin (Parameters.modulus security)) :
    (bodyLaw security includeScalar).weight color.rev = (bodyLaw security includeScalar).weight color := by
  unfold bodyLaw
  simp only [FiniteDist.mix_weight, FiniteDist.map_equiv_weight]
  calc
    _ = ∑ seed, (actualSeedLaw security).weight (seedNegate security seed) *
        (safeLaw security).weight ((shiftEquiv security
          (actualBlur security (seedNegate security seed) +
            if includeScalar then actualSecond security (seedNegate security seed) else 0)).symm color.rev) :=
      ((seedNegate security).sum_comp _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro seed _
      rw [seedNegate_weight, body_shift_negate, shiftEquiv_symm_reflection, safeLaw_reflection]

theorem diffuseMean_reflection (security : ℕ) (color : Fin (Parameters.modulus security)) :
    diffuseMean security color.rev = diffuseMean security color := by
  simp only [diffuseMean, actualProfile_reflection, Bool.not_true, Bool.not_false]
  ring

theorem primaryProfile_reflection (security : ℕ) (color : Fin (Parameters.modulus security)) :
    primaryProfile security color.rev = primaryProfile security color := by
  simp only [primaryProfile, bodyLaw_reflection, diffuseMean_reflection]

theorem primaryLaw_reflection (security : ℕ) (color : Fin (Parameters.modulus security)) :
    (primaryLaw security).weight color.rev = (primaryLaw security).weight color :=
  primaryProfile_reflection security color

theorem signProfile_reflection (security : ℕ) (color : Fin (Parameters.modulus security)) :
    signProfile security color.rev = -signProfile security color := by
  simp only [signProfile, actualProfile_reflection, Bool.not_true, Bool.not_false]
  ring

/-- Reflection reverses the inward direction, including the midpoint coin. -/
theorem positiveDirection_reflection (security : ℕ) (color : InwardAnchor.Palette security) (coin : Bool) :
    InwardAnchor.positiveDirection security color.rev (!coin) =
      !(InwardAnchor.positiveDirection security color coin) := by
  have hsum : color.rev.val + color.val = Parameters.modulus security - 1 := by
    simp only [Fin.val_rev]
    omega
  by_cases hlow : 2 * color.val < Parameters.modulus security - 1
  · have hrevhigh : Parameters.modulus security - 1 < 2 * color.rev.val := by omega
    have hrevlow : ¬2 * color.rev.val < Parameters.modulus security - 1 := by omega
    simp only [InwardAnchor.positiveDirection, hlow, hrevhigh, hrevlow, if_true, if_false, Bool.not_false]
  · by_cases hhigh : Parameters.modulus security - 1 < 2 * color.val
    · have hrevlow : 2 * color.rev.val < Parameters.modulus security - 1 := by omega
      simp only [InwardAnchor.positiveDirection, hlow, hhigh, hrevlow, if_true, if_false, Bool.not_true]
    · have hrevlow : ¬2 * color.rev.val < Parameters.modulus security - 1 := by omega
      have hrevhigh : ¬Parameters.modulus security - 1 < 2 * color.rev.val := by omega
      simp only [InwardAnchor.positiveDirection, hlow, hhigh, hrevlow, hrevhigh, if_false]

def directionLaw (security : ℕ) : FiniteDist Bool :=
  ((primaryLaw security).prod (FiniteDist.uniform Bool)).map
    (fun input => InwardAnchor.positiveDirection security input.1 input.2)

theorem directionLaw_reflection (security : ℕ) (direction : Bool) :
    (directionLaw security).weight (!direction) = (directionLaw security).weight direction := by
  classical
  let reverse := (Fin.revPerm : Equiv.Perm (Fin (Parameters.modulus security))).prodCongr Equiv.boolNot
  have hweight (input : Fin (Parameters.modulus security) × Bool) :
      ((primaryLaw security).prod (FiniteDist.uniform Bool)).weight (reverse input) =
        ((primaryLaw security).prod (FiniteDist.uniform Bool)).weight input := by
    change (primaryLaw security).weight input.1.rev * (FiniteDist.uniform Bool).weight (!input.2) = _
    rw [primaryLaw_reflection]
    rfl
  have hdirection (input : Fin (Parameters.modulus security) × Bool) :
      InwardAnchor.positiveDirection security (reverse input).1 (reverse input).2 =
        !(InwardAnchor.positiveDirection security input.1 input.2) :=
    positiveDirection_reflection security input.1 input.2
  unfold directionLaw
  simp only [FiniteDist.map_weight]
  calc
    _ = ∑ input, @ite ℝ
        (InwardAnchor.positiveDirection security (reverse input).1 (reverse input).2 = !direction)
        (Classical.propDecidable _)
        (((primaryLaw security).prod (FiniteDist.uniform Bool)).weight (reverse input)) 0 :=
      (reverse.sum_comp (fun input : Fin (Parameters.modulus security) × Bool =>
        @ite ℝ (InwardAnchor.positiveDirection security input.1 input.2 = !direction)
          (Classical.propDecidable _)
          (((primaryLaw security).prod (FiniteDist.uniform Bool)).weight input) 0)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro input _
      rw [hweight, hdirection]
      simp only [Bool.not_inj_iff]
      split_ifs <;> rfl

/-- The actual sampled inward direction is exactly fair, with the genuine
primary law and the fresh midpoint coin. -/
theorem directionLaw_fair (security : ℕ) (direction : Bool) :
    (directionLaw security).weight direction = 1 / 2 := by
  have hsum := (directionLaw security).sum_one
  have hreflection := directionLaw_reflection security true
  simp only [Fintype.sum_bool] at hsum
  simp only [Bool.not_true] at hreflection
  cases direction <;> linarith

theorem directionLaw_eq_uniform (security : ℕ) :
    directionLaw security = FiniteDist.uniform Bool := by
  apply FiniteDist.ext
  intro direction
  rw [directionLaw_fair]
  simp [FiniteDist.uniform_weight]

end

end CurrentAFT.ProposalSymmetry
