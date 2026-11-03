import CurrentAFT.PairSmoothing
import CurrentAFT.ProposalSymmetry
import CurrentAFT.BackgroundFamilies
import AFT.TrimmedPairCoreBounds

/-!
# The actual fixed-scalar diffuse pair and its safe quadratic seed

The anchor sign is the pushforward of the actual primary color and fair
midpoint coin. Public blur uses two actual independent edge Gaussians. The
protected second scalar is fixed throughout each pair; it is not resampled
between the two endpoints or across factors of a shared-scalar product.
-/

namespace CurrentAFT.DiffusePair

open AFT AFT.TrimmedSlice AFT.SafeConvolution DiffuseProfiles ProposalPrimary
  ProposalSymmetry ActualControls FirstResponse PairSmoothing
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
  Parameters.safeMargin ProposalPrimary.primaryLaw ProposalPrimary.centerLaw
  DiffuseProfiles.edgeLaw ProposalSymmetry.directionLaw

abbrev PairSeed (security : ℕ) := Bool ×
  (GaussianSource.Window (edgeCutoff security) × GaussianSource.Window (edgeCutoff security))

def pairSeedLaw (security : ℕ) : FiniteDist (PairSeed security) :=
  (directionLaw security).prod ((edgeLaw security).prod (edgeLaw security))

def pairBlur (security : ℕ) (seed : PairSeed security) : ℤ := seed.2.1 - seed.2.2

def pairStart (security : ℕ) (seed : PairSeed security) : ℤ :=
  intervalStart seed.1 (Parameters.anchorWidth security) (pairBlur security seed)

theorem pairBlur_bound (security : ℕ) (seed : PairSeed security) :
    |pairBlur security seed| ≤ Parameters.sourceCutoff security := by
  have h1 := Finset.mem_Icc.mp seed.2.1.property
  have h2 := Finset.mem_Icc.mp seed.2.2.property
  unfold pairBlur edgeCutoff at *
  apply abs_le.mpr
  constructor <;> omega

theorem pairStart_bound (security : ℕ) (seed : PairSeed security) (shift : ℤ)
    (hshift : shift ∈ anchorInterval (pairStart security seed) (Parameters.anchorWidth security)) :
    |shift| ≤ 2 * (Parameters.anchorWidth security : ℤ) + Parameters.sourceCutoff security :=
  interval_bound seed.1 (Parameters.anchorWidth security) _ _ shift (pairBlur_bound security seed) hshift

theorem pair_clearance (security : ℕ) :
    2 * (1 : ℤ) + (2 * (Parameters.anchorWidth security : ℤ) + Parameters.sourceCutoff security) +
      Parameters.sourceCutoff security < Parameters.modulus security := by
  have h := deletion_clearance security
  unfold deletion at h
  omega

def pairProfile (security : ℕ) (scalar : ℤ) :
    ActualControls.Palette security → ActualControls.Palette security → ℝ :=
  mixedPair (Parameters.modulus security) 1 (pairStart security) (fun _ => scalar)
    (pairSeedLaw security).weight (Parameters.anchorWidth security)

theorem pairProfile_nonneg (security : ℕ) (scalar : ℤ) (first second : ActualControls.Palette security) :
    0 ≤ pairProfile security scalar first second :=
  mixedPair_nonneg _ _ _ _ _ _ (pairSeedLaw security).nonneg _ _

theorem pairProfile_mass (security : ℕ) (scalar : ℤ) (hscalar : |scalar| ≤ Parameters.sourceCutoff security) :
    ∑ first, ∑ second, pairProfile security scalar first second = 1 :=
  mixedPair_mass (Parameters.modulus security) 1
    (2 * (Parameters.anchorWidth security : ℤ) + Parameters.sourceCutoff security)
    (Parameters.sourceCutoff security) (Parameters.anchorWidth security)
    (InwardAnchor.anchorWidth_pos security).ne' _ _ _ (pairSeedLaw security).sum_one (by norm_num)
      (pairStart_bound security) (fun _ => hscalar) (pair_clearance security)

def pairLaw (security : ℕ) (scalar : ℤ) (hscalar : |scalar| ≤ Parameters.sourceCutoff security) :
    FiniteDist (ActualControls.Palette security × ActualControls.Palette security) where
  weight colors := pairProfile security scalar colors.1 colors.2
  nonneg colors := pairProfile_nonneg security scalar colors.1 colors.2
  sum_one := by rw [Fintype.sum_prod_type]; exact pairProfile_mass security scalar hscalar

theorem pairProfile_symmetric (security : ℕ) (scalar : ℤ) (first second : ActualControls.Palette security) :
    pairProfile security scalar first second = pairProfile security scalar second first :=
  mixedPair_symmetric _ _ _ _ _ _ _ _

theorem pairProfile_height (security : ℕ) (scalar : ℤ) (hscalar : |scalar| ≤ Parameters.sourceCutoff security)
    (first second : ActualControls.Palette security) :
    pairProfile security scalar first second ≤
      1 / ((Parameters.anchorWidth security : ℝ) *
        ((Parameters.modulus security : ℝ) - deletion security)) := by
  have h := mixedPair_le (Parameters.modulus security) 1
    (2 * (Parameters.anchorWidth security : ℤ) + Parameters.sourceCutoff security)
    (Parameters.sourceCutoff security) (Parameters.anchorWidth security)
    (pairStart security) (fun _ => scalar) (pairSeedLaw security).weight
    (pairSeedLaw security).nonneg (pairSeedLaw security).sum_one
    (pairStart_bound security) (fun _ => hscalar) (pair_clearance security) first second
  convert h using 1
  simp only [deletion, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Int.cast_add,
    Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]
  congr 2
  ring

def safeCore (security : ℕ) : Finset (ActualControls.Palette security) :=
  paletteSlice (Parameters.modulus security) (Parameters.safeMargin security) 0

theorem safeCore_mem (security : ℕ) (color : ActualControls.Palette security) :
    color ∈ safeCore security ↔ InwardAnchor.SafeColor security color :=
  core_palette_mem _ _ _

theorem safeCore_nonempty (security : ℕ) : (safeCore security).Nonempty := by
  apply paletteSlice_nonempty
  · positivity
  · have h := safe_clearance security
    simp only [abs_zero]
    omega

def safePairProfile (security : ℕ) (scalar : ℤ) :
    ActualControls.Palette security → ActualControls.Palette security → ℝ :=
  SafePair.coreSeed (safeCore security) (pairProfile security scalar)

theorem safePairProfile_canonical (security : ℕ) (scalar : ℤ) :
    (∀ first, ∑ second, safePairProfile security scalar first second = 0) ∧
    (∀ second, ∑ first, safePairProfile security scalar first second = 0) :=
  SafePair.coreSeed_canonical _ _ (safeCore_nonempty security)

theorem safePairProfile_zero_outside (security : ℕ) (scalar : ℤ)
    (first second : ActualControls.Palette security)
    (hout : ¬InwardAnchor.SafeColor security first ∨ ¬InwardAnchor.SafeColor security second) :
    safePairProfile security scalar first second = 0 := by
  apply SafePair.coreSeed_supported
  simpa only [safeCore_mem] using hout

theorem safePairProfile_counting_square (security : ℕ) (scalar : ℤ)
    (hscalar : |scalar| ≤ Parameters.sourceCutoff security) :
    (∑ first, ∑ second, safePairProfile security scalar first second ^ 2) ≤
      1 / ((Parameters.anchorWidth security : ℝ) *
        ((Parameters.modulus security : ℝ) - deletion security)) := by
  calc
    _ ≤ ∑ first, ∑ second, pairProfile security scalar first second ^ 2 :=
      SafePair.coreSeed_square_le _ _ (safeCore_nonempty security)
    _ ≤ ∑ first, ∑ second,
        (1 / ((Parameters.anchorWidth security : ℝ) *
          ((Parameters.modulus security : ℝ) - deletion security))) * pairProfile security scalar first second := by
      apply Finset.sum_le_sum
      intro first _
      apply Finset.sum_le_sum
      intro second _
      have h := mul_le_mul_of_nonneg_right (pairProfile_height security scalar hscalar first second)
        (pairProfile_nonneg security scalar first second)
      nlinarith only [h]
    _ = _ := by simp only [← Finset.mul_sum, pairProfile_mass security scalar hscalar, mul_one]

def liftedPairProfile (security : ℕ) (scalar : ℤ) :
    ZMod (Parameters.modulus security) × ZMod (Parameters.modulus security) → ℝ :=
  liftedRestrictedMixedPair (Parameters.modulus security) (Parameters.safeMargin security) 1
    (pairStart security) (fun _ => scalar) (pairSeedLaw security) (Parameters.anchorWidth security)

def rootPairLaw (security : ℕ) : FiniteDist (DiffuseProfiles.ActualSeed security × DiffuseProfiles.ActualSeed security) :=
  (actualSeedLaw security).prod (actualSeedLaw security)

def rootPairShift (security : ℕ) (seed : DiffuseProfiles.ActualSeed security × DiffuseProfiles.ActualSeed security) :
    ZMod (Parameters.modulus security) × ZMod (Parameters.modulus security) :=
  ((actualBlur security seed.1 : ZMod (Parameters.modulus security)),
    (actualBlur security seed.2 : ZMod (Parameters.modulus security)))

theorem liftedPairProfile_smoothing_square (security : ℕ) (scalar : ℤ)
    (hscalar : |scalar| ≤ Parameters.sourceCutoff security) :
    (∑ color, (smoothProfile (rootPairLaw security) (rootPairShift security) (liftedPairProfile security scalar) color -
      liftedPairProfile security scalar color) ^ 2) ≤
      16 * (Parameters.modulus security : ℝ) * Parameters.sourceCutoff security /
        (((Parameters.modulus security : ℝ) / 2) ^ 2 * (Parameters.anchorWidth security : ℝ) ^ 2) +
      16 * (Parameters.modulus security : ℝ) * (Parameters.sourceCutoff security : ℝ) ^ 2 /
        (((Parameters.modulus security : ℝ) / 2) ^ 4 * Parameters.anchorWidth security) +
      8 * (Parameters.sourceCutoff security : ℝ) /
        (((Parameters.modulus security : ℝ) / 2) ^ 2 * Parameters.anchorWidth security) := by
  have hq := FirstResponse.modulus_pos security
  have hcore : 2 * Parameters.safeMargin security ≤ Parameters.modulus security := by
    have h := safe_clearance security
    omega
  have hmargin : Parameters.sourceCutoff security ≤ Parameters.safeMargin security := by
    simp only [Parameters.safeMargin]
    omega
  have hden : (Parameters.modulus security : ℝ) / 2 ≤
      (Parameters.modulus security : ℝ) - 2 * (1 : ℝ) -
        (2 * (Parameters.anchorWidth security : ℝ) + Parameters.sourceCutoff security) -
        Parameters.sourceCutoff security := by
    have h := Nat.cast_le (α := ℝ).mpr (two_deletion_le_modulus security)
    simp only [deletion, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at h
    linarith
  exact restrictedMixedPair_smoothing_square_le (Parameters.modulus security) (Parameters.safeMargin security)
    (Parameters.sourceCutoff security) 1
    (2 * (Parameters.anchorWidth security : ℤ) + Parameters.sourceCutoff security)
    (Parameters.sourceCutoff security) (Parameters.anchorWidth security) ((Parameters.modulus security : ℝ) / 2)
    (by positivity) hcore (by have h := InwardAnchor.sourceCutoff_pos security; have := hmargin; omega) hmargin
    (pairStart security) (fun _ => scalar) (pairSeedLaw security) (rootPairLaw security)
    (fun seed => actualBlur security seed.1) (fun seed => actualBlur security seed.2)
    (fun seed => (actualBlur_bound security seed.1).trans (by omega))
    (fun seed => (actualBlur_bound security seed.2).trans (by omega))
    (pairStart_bound security) (fun _ => hscalar) (by simpa only [Int.cast_add, Int.cast_mul,
      Int.cast_natCast, Int.cast_ofNat, Int.cast_one] using hden)

end

end CurrentAFT.DiffusePair
