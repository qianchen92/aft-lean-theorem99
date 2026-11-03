import CurrentAFT.LocalReferenceEnergy
import CurrentAFT.ActualControls

/-! # The actual source-independent public seed of one protected leg

The protected scalar is absent from the seed type and its probability law.
The public primary control determines the inward sign after the fair
midpoint coin, while the public anchor index and blur are shared by the
marked and diffuse refinements.
-/
namespace CurrentAFT.ActualPublicLegCharge
open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy InwardAnchor
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance anchorWidthNeZero (security : ℕ) : NeZero (Parameters.anchorWidth security) :=
  ⟨(InwardAnchor.anchorWidth_pos security).ne'⟩
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff activation

structure PublicSeed (security : ℕ) where
  marked : Bool
  coin : Bool
  anchorIndex : InwardAnchor.Index security
  blur : LocalReferenceEnergy.BlurSeed security

abbrev SeedProduct (security : ℕ) :=
  Bool × (Bool × (InwardAnchor.Index security × LocalReferenceEnergy.BlurSeed security))

def seedEquiv (security : ℕ) : PublicSeed security ≃ SeedProduct security where
  toFun seed := (seed.marked, (seed.coin, (seed.anchorIndex, seed.blur)))
  invFun draw := ⟨draw.1, draw.2.1, draw.2.2.1, draw.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance seedFintype (security : ℕ) : Fintype (PublicSeed security) :=
  Fintype.ofEquiv (SeedProduct security) (seedEquiv security).symm

def activationLaw (security : ℕ) : FiniteDist Bool where
  weight marked := if marked then activation security else 1 - activation security
  nonneg marked := by
    cases marked
    · simp only [Bool.false_eq_true, if_false]
      linarith [activation_le_half security]
    · simpa only [if_true] using (activation_pos security).le
  sum_one := by simp only [Fintype.sum_bool, Bool.false_eq_true, if_false, if_true]; ring

def seedLaw (security : ℕ) : FiniteDist (PublicSeed security) :=
  ((activationLaw security).prod ((FiniteDist.uniform Bool).prod
    ((FiniteDist.uniform (InwardAnchor.Index security)).prod (publicBlurLaw security)))).map (seedEquiv security).symm

def signedOffset (security : ℕ) (primary : ActualControls.Palette security) (seed : PublicSeed security) : ℤ :=
  if positiveDirection security primary seed.coin then offset security seed.anchorIndex else -offset security seed.anchorIndex

def publicShift (security : ℕ) (primary : ActualControls.Palette security) (seed : PublicSeed security) : ℤ :=
  signedOffset security primary seed + seed.blur.1.val - seed.blur.2.val

theorem seedLaw_weight (security : ℕ) (seed : PublicSeed security) :
    (seedLaw security).weight seed =
      (activationLaw security).weight seed.marked *
        ((FiniteDist.uniform Bool).weight seed.coin *
          ((FiniteDist.uniform (InwardAnchor.Index security)).weight seed.anchorIndex * (publicBlurLaw security).weight seed.blur)) := by
  rw [seedLaw, FiniteDist.map_equiv_weight]
  rfl

theorem activationLaw_true (security : ℕ) : (activationLaw security).weight true = activation security := rfl

theorem activationLaw_false (security : ℕ) : (activationLaw security).weight false = 1 - activation security := rfl

theorem blur_bound (security : ℕ) (seed : PublicSeed security) :
    |seed.blur.1.val - seed.blur.2.val| ≤ (Parameters.sourceCutoff security : ℤ) - 1 := by
  have h1 := Finset.mem_Icc.mp seed.blur.1.property
  have h2 := Finset.mem_Icc.mp seed.blur.2.property
  have hcut := InwardAnchor.sourceCutoff_pos security
  unfold edgeCutoff at *
  apply abs_le.mpr
  constructor <;> omega

theorem signedOffset_bound (security : ℕ) (primary : ActualControls.Palette security) (seed : PublicSeed security) :
    |signedOffset security primary seed| ≤ 2 * (Parameters.anchorWidth security : ℤ) - 1 := by
  have hindex := seed.anchorIndex.isLt
  unfold signedOffset offset
  split_ifs
  · rw [abs_of_nonneg (by positivity)]
    omega
  · rw [abs_neg, abs_of_nonneg (by positivity)]
    omega

theorem publicShift_bound (security : ℕ) (primary : ActualControls.Palette security) (seed : PublicSeed security) :
    |publicShift security primary seed| ≤
      2 * (Parameters.anchorWidth security : ℤ) + ((Parameters.sourceCutoff security : ℤ) - 1) := by
  have h := (abs_add_le (signedOffset security primary seed) (seed.blur.1.val - seed.blur.2.val)).trans
    (add_le_add (signedOffset_bound security primary seed) (blur_bound security seed))
  have hequal : publicShift security primary seed = signedOffset security primary seed + (seed.blur.1.val - seed.blur.2.val) := by
    unfold publicShift
    ring
  rw [hequal]
  exact h.trans (by omega)

end
end CurrentAFT.ActualPublicLegCharge
