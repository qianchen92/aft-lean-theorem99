import CurrentAFT.DiffusePairBounds
import CurrentAFT.PairReindex

/-!
# Actual diffuse-pair residual after the safe two-body seed

The residual is defined by exact subtraction of the protected convolution
of the concrete safe seed from the true pair's uniform canonical profile.
The finite-palette and residue representations are related by an explicit
equivalence, preserving every counting Hilbert sum.
-/

namespace CurrentAFT.DiffusePairResidual

open AFT AFT.TrimmedSlice AFT.SafePair AFT.SafeConvolution
  DiffuseProfiles ProposalPrimary FirstResponse ActualControls PairSmoothing
  DiffusePair DiffusePairBounds PairReindex
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
  Parameters.safeMargin ProposalPrimary.primaryLaw ProposalPrimary.centerLaw ActualControls.bodyReference
  DiffusePair.pairProfile DiffusePair.safePairProfile DiffusePair.liftedPairProfile
  DiffusePair.rootPairLaw DiffusePair.rootPairShift DiffusePair.pairSeedLaw DiffusePair.pairStart
  DiffuseProfiles.actualSeedLaw DiffuseProfiles.edgeLaw DiffuseProfiles.scalarLaw

theorem restricted_lift_identity {Index : Type*} [Fintype Index]
    (modulus coreDepth : ℕ) [NeZero modulus] (boundary : ℤ)
    (starts scalars : Index → ℤ) (law : FiniteDist Index) (width : ℕ) :
    (fun color : ZMod modulus × ZMod modulus =>
      liftPair (ZMod.finEquiv modulus).toEquiv
        (restrictPair (paletteSlice modulus coreDepth 0)
          (mixedPair modulus boundary starts scalars law.weight width)) color.1 color.2) =
      liftedRestrictedMixedPair modulus coreDepth boundary starts scalars law width := rfl

theorem finitePalette_uniform_error (modulus : ℕ) [NeZero modulus]
    (seed mass : Fin modulus → Fin modulus → ℝ) :
    countingL2 ((fun color : ZMod modulus × ZMod modulus =>
        liftPair (ZMod.finEquiv modulus).toEquiv seed color.1 color.2) -
      uniformCanonical (fun color : ZMod modulus × ZMod modulus =>
        liftPair (ZMod.finEquiv modulus).toEquiv mass color.1 color.2)) =
      pairCountingL2 (seed - canonicalPair (fun _ => 1 / (modulus : ℝ)) mass) := by
  have h := liftPair_uniform_error_countingL2 (ZMod.finEquiv modulus).toEquiv seed mass
  change pairCountingL2 (liftPair (ZMod.finEquiv modulus).toEquiv seed -
    canonicalPair (fun _ => 1 / (Fintype.card (ZMod modulus) : ℝ))
      (liftPair (ZMod.finEquiv modulus).toEquiv mass)) = _
  simpa only [Fintype.card_fin] using h

noncomputable abbrev residueEquiv (security : ℕ) : ActualControls.Palette security ≃ ZMod (Parameters.modulus security) :=
  (ZMod.finEquiv (Parameters.modulus security)).toEquiv

def originalProfile (security : ℕ) (scalar : ℤ) :
    ZMod (Parameters.modulus security) × ZMod (Parameters.modulus security) → ℝ :=
  fun color => liftPair ((ZMod.finEquiv (Parameters.modulus security)).toEquiv) (pairProfile security scalar) color.1 color.2

def restrictedProfile (security : ℕ) (scalar : ℤ) :
    ZMod (Parameters.modulus security) × ZMod (Parameters.modulus security) → ℝ :=
  fun color => liftPair ((ZMod.finEquiv (Parameters.modulus security)).toEquiv)
    (restrictPair (safeCore security) (pairProfile security scalar)) color.1 color.2

def seedProfile (security : ℕ) (scalar : ℤ) :
    ZMod (Parameters.modulus security) × ZMod (Parameters.modulus security) → ℝ :=
  fun color => liftPair ((ZMod.finEquiv (Parameters.modulus security)).toEquiv) (safePairProfile security scalar) color.1 color.2

def residueCore (security : ℕ) : Finset (ZMod (Parameters.modulus security)) :=
  (safeCore security).map ((ZMod.finEquiv (Parameters.modulus security)).toEquiv).toEmbedding

theorem restrictedProfile_eq (security : ℕ) (scalar : ℤ) :
    restrictedProfile security scalar = liftedPairProfile security scalar := by
  unfold restrictedProfile liftedPairProfile safeCore pairProfile
  exact restricted_lift_identity _ _ _ _ _ _ _

theorem seedProfile_eq (security : ℕ) (scalar : ℤ) :
    seedProfile security scalar = fun color => coreSeed (residueCore security)
      (liftPair ((ZMod.finEquiv (Parameters.modulus security)).toEquiv) (pairProfile security scalar)) color.1 color.2 := by
  rw [residueCore, coreSeed_map]
  unfold seedProfile safePairProfile
  rfl

def rootResiduePairLaw (security : ℕ) :
    FiniteDist (ZMod (Parameters.modulus security) × ZMod (Parameters.modulus security)) :=
  (rootPairLaw security).map (rootPairShift security)

theorem root_convolution (security : ℕ) (profile :
    ZMod (Parameters.modulus security) × ZMod (Parameters.modulus security) → ℝ) :
    convolution (rootResiduePairLaw security).weight profile =
      smoothProfile (rootPairLaw security) (rootPairShift security) profile := by
  funext color
  change ((rootPairLaw security).map (rootPairShift security)).expectation
    (fun shift => profile (color - shift)) = _
  rw [FiniteDist.expectation_map]
  rfl

def residualProfile (security : ℕ) (scalar : ℤ) :
    ZMod (Parameters.modulus security) × ZMod (Parameters.modulus security) → ℝ :=
  uniformCanonical (originalProfile security scalar) -
    convolution (rootResiduePairLaw security).weight (seedProfile security scalar)

theorem residualProfile_leading (security : ℕ) (scalar : ℤ) :
    convolution (rootResiduePairLaw security).weight (seedProfile security scalar) +
      residualProfile security scalar = uniformCanonical (originalProfile security scalar) := by
  unfold residualProfile
  abel

theorem residualProfile_counting_bound (security : ℕ) (scalar : ℤ) :
    countingL2 (residualProfile security scalar) ≤
      countingL2 (seedProfile security scalar - uniformCanonical (restrictedProfile security scalar)) +
      countingL2 (convolution (rootResiduePairLaw security).weight (restrictedProfile security scalar) -
        restrictedProfile security scalar) +
      countingL2 (restrictedProfile security scalar - originalProfile security scalar) := by
  have h := smoothed_core_error_L2_le (rootResiduePairLaw security) (residueCore security)
    (liftPair ((ZMod.finEquiv (Parameters.modulus security)).toEquiv) (pairProfile security scalar)) 1
  have hrestrict : (fun color : ZMod (Parameters.modulus security) × ZMod (Parameters.modulus security) =>
      restrictPair (residueCore security) (liftPair ((ZMod.finEquiv (Parameters.modulus security)).toEquiv) (pairProfile security scalar)) color.1 color.2) =
        restrictedProfile security scalar := by
    rw [residueCore, restrictPair_map]
    rfl
  have hseed := seedProfile_eq security scalar
  dsimp only at h
  rw [← hseed, hrestrict] at h
  simp only [pow_one, Nat.cast_one, one_mul] at h
  have hneg : residualProfile security scalar =
      -(convolution (rootResiduePairLaw security).weight (seedProfile security scalar) -
        uniformCanonical (originalProfile security scalar)) := by
    unfold residualProfile
    abel
  rw [hneg, countingL2_neg]
  exact h

theorem reference_error_reindex (security : ℕ) (scalar : ℤ) :
    countingL2 (seedProfile security scalar - uniformCanonical (restrictedProfile security scalar)) =
      pairCountingL2 (safePairProfile security scalar -
        canonicalPair (fun _ => 1 / (Parameters.modulus security : ℝ))
          (restrictPair (safeCore security) (pairProfile security scalar))) := by
  exact finitePalette_uniform_error (Parameters.modulus security)
    (safePairProfile security scalar) (restrictPair (safeCore security) (pairProfile security scalar))

theorem edge_error_reindex (security : ℕ) (scalar : ℤ) :
    countingL2 (restrictedProfile security scalar - originalProfile security scalar) =
      pairCountingL2 (restrictPair (safeCore security) (pairProfile security scalar) - pairProfile security scalar) := by
  have h := liftPair_difference_countingL2 ((ZMod.finEquiv (Parameters.modulus security)).toEquiv)
    (restrictPair (safeCore security) (pairProfile security scalar)) (pairProfile security scalar)
  simpa only [restrictedProfile, originalProfile, pairCountingL2, Pi.sub_apply] using h

theorem safeCore_card (security : ℕ) :
    ((safeCore security).card : ℝ) = (Parameters.modulus security : ℝ) - 2 * Parameters.safeMargin security := by
  have h : 2 * Parameters.safeMargin security ≤ Parameters.modulus security := by
    have h := safe_clearance security
    omega
  have hcard : (safeCore security).card = Parameters.modulus security - 2 * Parameters.safeMargin security := by
    rw [safeCore, paletteSlice_card _ _ _ (by positivity)]
    simp only [abs_zero, sub_zero]
    omega
  rw [hcard, Nat.cast_sub h, Nat.cast_mul, Nat.cast_ofNat]

theorem pairProfile_marginal_upper (security : ℕ) (scalar : ℤ)
    (hscalar : |scalar| ≤ Parameters.sourceCutoff security) (first : ActualControls.Palette security) :
    (∑ second, pairProfile security scalar first second) ≤ 2 / (Parameters.modulus security : ℝ) := by
  have h := mixedLaw_le (Parameters.modulus security : ℤ) 1
    (2 * (Parameters.anchorWidth security : ℤ) + Parameters.sourceCutoff security)
    (Parameters.sourceCutoff security) (pairStart security) (fun _ => scalar) (pairSeedLaw security).weight
    (Parameters.anchorWidth security) (InwardAnchor.anchorWidth_pos security).ne'
    (pairSeedLaw security).nonneg (pairSeedLaw security).sum_one (pairStart_bound security)
    (fun _ => hscalar) (pair_clearance security) first.val
  have hd : (Parameters.modulus security : ℝ) / 2 ≤ (Parameters.modulus security : ℝ) - deletion security := by
    have h := Nat.cast_le (α := ℝ).mpr (two_deletion_le_modulus security)
    push_cast at h
    linarith
  have hq := FirstResponse.modulus_pos security
  have hden : 1 / ((Parameters.modulus security : ℝ) - deletion security) ≤ 2 / Parameters.modulus security := by
    calc
      _ ≤ 1 / ((Parameters.modulus security : ℝ) / 2) :=
        one_div_le_one_div_of_le (by positivity) hd
      _ = _ := by ring
  apply le_trans _ hden
  rw [pairProfile, mixedPair_first_marginal _ _ _ _ _ _ (by norm_num)]
  convert h using 1
  simp only [deletion, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Int.cast_add,
    Int.cast_mul, Int.cast_natCast, Int.cast_ofNat, Int.cast_one]
  congr 1
  ring

theorem reference_error_scaled_square (security : ℕ) (scalar : ℤ)
    (hscalar : |scalar| ≤ Parameters.sourceCutoff security) :
    ((Parameters.modulus security : ℝ) *
      countingL2 (seedProfile security scalar - uniformCanonical (restrictedProfile security scalar))) ^ 2 ≤
        128 * (Parameters.safeMargin security : ℝ) / Parameters.modulus security := by
  have hq := FirstResponse.modulus_pos security
  have hupper := coreSeed_reference_error_le (safeCore security) (safeCore_nonempty security)
    (pairProfile security scalar) (2 / (Parameters.modulus security : ℝ)) (by positivity)
    (pairProfile_nonneg security scalar) (pairProfile_mass security scalar hscalar).le
    (pairProfile_marginal_upper security scalar hscalar)
    (fun second => by
      simpa only [pairProfile_symmetric security scalar] using pairProfile_marginal_upper security scalar hscalar second)
  have hcard : (Parameters.modulus security : ℝ) / 2 ≤ ((safeCore security).card : ℝ) := by
    rw [safeCore_card]
    have h := Nat.cast_lt (α := ℝ).mpr (safe_clearance security)
    push_cast at h
    linarith
  rw [reference_error_reindex]
  have hnorm : 0 ≤ pairCountingL2 (safePairProfile security scalar -
      canonicalPair (fun _ => 1 / (Parameters.modulus security : ℝ))
        (restrictPair (safeCore security) (pairProfile security scalar))) := countingL2_nonneg _
  have hupper' : pairCountingL2 (safePairProfile security scalar -
      canonicalPair (fun _ => 1 / (Parameters.modulus security : ℝ))
        (restrictPair (safeCore security) (pairProfile security scalar))) ≤
      Real.sqrt (1 / ((safeCore security).card : ℝ) - 1 / (Parameters.modulus security : ℝ)) *
        (2 * Real.sqrt (2 / (Parameters.modulus security : ℝ)) +
          Real.sqrt (1 / ((safeCore security).card : ℝ)) + Real.sqrt (1 / (Parameters.modulus security : ℝ))) := by
    simpa only [Fintype.card_fin, safePairProfile] using hupper
  have hs := pow_le_pow_left₀ (mul_nonneg hq.le hnorm)
    (mul_le_mul_of_nonneg_left hupper' hq.le) 2
  exact hs.trans (core_reference_scaled_square_le _ _ _ hq (Nat.cast_nonneg _)
    hcard (safeCore_card security))

theorem edge_error_scaled_square (security : ℕ) (scalar : ℤ)
    (hscalar : |scalar| ≤ Parameters.sourceCutoff security) :
    ((Parameters.modulus security : ℝ) *
      countingL2 (restrictedProfile security scalar - originalProfile security scalar)) ^ 2 ≤
        16 * (Parameters.safeMargin security : ℝ) / Parameters.anchorWidth security := by
  have hq := FirstResponse.modulus_pos security
  have ha : (0 : ℝ) < Parameters.anchorWidth security := Nat.cast_pos.mpr (InwardAnchor.anchorWidth_pos security)
  have hd : (Parameters.modulus security : ℝ) / 2 ≤ (Parameters.modulus security : ℝ) - deletion security := by
    have h := Nat.cast_le (α := ℝ).mpr (two_deletion_le_modulus security)
    push_cast at h
    linarith
  have hcore : 2 * (Parameters.safeMargin security : ℤ) ≤ Parameters.modulus security := by
    have h := safe_clearance security
    omega
  have h := actual_core_square_loss (Parameters.modulus security) 1
    (2 * (Parameters.anchorWidth security : ℤ) + Parameters.sourceCutoff security)
    (Parameters.sourceCutoff security) (Parameters.safeMargin security) (Parameters.anchorWidth security)
    (InwardAnchor.anchorWidth_pos security).ne' (pairStart security) (fun _ => scalar) (pairSeedLaw security)
    (by norm_num) (by positivity) hcore (pairStart_bound security) (fun _ => hscalar) (pair_clearance security)
  have h' : (countingL2 (restrictedProfile security scalar - originalProfile security scalar)) ^ 2 ≤
      4 * (Parameters.safeMargin security : ℝ) /
        ((Parameters.anchorWidth security : ℝ) * ((Parameters.modulus security : ℝ) - deletion security) ^ 2) := by
    rw [edge_error_reindex, pairCountingL2, countingL2, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    simp only [Fintype.sum_prod_type]
    convert h using 1
    · apply Finset.sum_congr rfl
      intro first _
      apply Finset.sum_congr rfl
      intro second _
      simp only [Pi.sub_apply, safeCore, pairProfile]
      ring
    · simp only [deletion, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Int.cast_add,
        Int.cast_mul, Int.cast_natCast, Int.cast_ofNat, Int.cast_one]
      congr 2
      ring
  calc
    _ = (Parameters.modulus security : ℝ) ^ 2 *
        (countingL2 (restrictedProfile security scalar - originalProfile security scalar)) ^ 2 := by ring
    _ ≤ (Parameters.modulus security : ℝ) ^ 2 *
        (4 * (Parameters.safeMargin security : ℝ) /
          ((Parameters.anchorWidth security : ℝ) * ((Parameters.modulus security : ℝ) - deletion security) ^ 2)) :=
      mul_le_mul_of_nonneg_left h' (sq_nonneg _)
    _ ≤ (Parameters.modulus security : ℝ) ^ 2 *
        (4 * (Parameters.safeMargin security : ℝ) /
          ((Parameters.anchorWidth security : ℝ) * ((Parameters.modulus security : ℝ) / 2) ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hd 2) ha.le
    _ = _ := by field_simp; ring

end

end CurrentAFT.DiffusePairResidual
