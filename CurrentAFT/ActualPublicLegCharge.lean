import CurrentAFT.ActualPublicLegSeed
import CurrentAFT.Conditioning

/-! # The real public leg seed fixes the protected pair's integer charge

The seed is sampled before the protected scalar. Its marked branch is the
actual inward anchor point and its diffuse branch is the actual ordered
trimmed pair slice. Both branches have the same exact integer pair sum.
-/
namespace CurrentAFT.ActualPublicLegCharge
open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy FirstHistogram InwardAnchor
open scoped BigOperators Classical Fin.NatCast
noncomputable section
local instance chargeFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance chargeModulusNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
abbrev Palette (security : ℕ) := ActualControls.Palette security

theorem finEquiv_natCast (modulus : ℕ) [NeZero modulus] (color : Fin modulus) :
    (ZMod.finEquiv modulus) color = (color.val : ZMod modulus) := by
  cases modulus with
  | zero => exact Fin.elim0 color
  | succ modulus =>
      change color = (color.val : Fin (modulus + 1))
      exact (Fin.cast_val_eq_self color).symm

theorem shiftEquiv_value (security : ℕ) (shift : ℤ) (color : Palette security)
    (hlower : 0 ≤ (color.val : ℤ) + shift)
    (hupper : (color.val : ℤ) + shift < Parameters.modulus security) :
    ((shiftEquiv security shift color).val : ℤ) = (color.val : ℤ) + shift := by
  let output : Palette security := ⟨((color.val : ℤ) + shift).toNat, by omega⟩
  have houtput : (output.val : ℤ) = (color.val : ℤ) + shift := by dsimp [output]; omega
  have hemb (point : Palette security) : (ZMod.finEquiv (Parameters.modulus security)) point =
      (point.val : ZMod (Parameters.modulus security)) := finEquiv_natCast _ point
  have hequal : shiftEquiv security shift color = output := by
    apply (ZMod.finEquiv (Parameters.modulus security)).injective
    change (ZMod.finEquiv (Parameters.modulus security))
      ((ZMod.finEquiv (Parameters.modulus security)).symm
        ((ZMod.finEquiv (Parameters.modulus security)) color + (shift : ZMod (Parameters.modulus security)))) = _
    rw [RingEquiv.apply_symm_apply, hemb, hemb]
    have hcast := congrArg (fun value : ℤ => (value : ZMod (Parameters.modulus security))) houtput
    simpa only [Int.cast_natCast, Int.cast_add] using hcast.symm
  rw [hequal, houtput]

def markedPoint (security : ℕ) (primary : Palette security) (scalar : FirstHistogram.Scalar security)
    (seed : PublicSeed security) : Palette security :=
  shiftEquiv security (seed.blur.1.val - seed.blur.2.val)
    (point security primary seed.coin seed.anchorIndex (-scalar.val)
      (by simpa only [abs_neg] using InwardAnchor.scalar_bound security scalar))

theorem markedPoint_value (security : ℕ) (primary : Palette security) (scalar : FirstHistogram.Scalar security)
    (seed : PublicSeed security) :
    (markedPoint security primary scalar seed).val =
      ((Parameters.modulus security : ℤ) - 1 - primary.val + publicShift security primary seed - scalar.val).toNat := by
  have hs := integerPoint_safe security primary seed.coin seed.anchorIndex (-scalar.val)
    (by simpa only [abs_neg] using InwardAnchor.scalar_bound security scalar)
  have hp := point_value security primary seed.coin seed.anchorIndex (-scalar.val)
    (by simpa only [abs_neg] using InwardAnchor.scalar_bound security scalar)
  have hblur := abs_le.mp (blur_bound security seed)
  have hmargin : (Parameters.safeMargin security : ℤ) = 3 * (Parameters.sourceCutoff security : ℤ) := by
    rw [Parameters.safeMargin]
    push_cast
    ring
  have hcut := InwardAnchor.sourceCutoff_pos security
  have hvalue := shiftEquiv_value security (seed.blur.1.val - seed.blur.2.val)
    (point security primary seed.coin seed.anchorIndex (-scalar.val)
      (by simpa only [abs_neg] using InwardAnchor.scalar_bound security scalar))
    (by rw [hp]; omega) (by rw [hp]; omega)
  change (shiftEquiv security (seed.blur.1.val - seed.blur.2.val) _).val = _
  apply Int.ofNat_inj.mp
  rw [hvalue, hp]
  have hequal : integerPoint security primary seed.coin seed.anchorIndex (-scalar.val) +
      (seed.blur.1.val - seed.blur.2.val) =
      (Parameters.modulus security : ℤ) - 1 - primary.val + publicShift security primary seed - scalar.val := by
    unfold integerPoint publicShift signedOffset
    ring
  rw [← hequal, Int.toNat_of_nonneg]
  omega

def markedLaw (security : ℕ) (primary : Palette security) (scalar : FirstHistogram.Scalar security)
    (seed : PublicSeed security) : FiniteDist (Palette security × Palette security) :=
  (FiniteDist.uniform Unit).map (fun _ => (primary, markedPoint security primary scalar seed))

theorem markedLaw_weight (security : ℕ) (primary : Palette security) (scalar : FirstHistogram.Scalar security)
    (seed : PublicSeed security) (pair : Palette security × Palette security) :
    (markedLaw security primary scalar seed).weight pair =
      if (primary, markedPoint security primary scalar seed) = pair then 1 else 0 := by
  simp [markedLaw, FiniteDist.map_weight, FiniteDist.uniform_weight]

theorem diffuse_shift_clearance (security : ℕ) (primary : Palette security) (scalar : FirstHistogram.Scalar security)
    (seed : PublicSeed security) :
    2 * (1 : ℤ) + |publicShift security primary seed - scalar.val| < Parameters.modulus security := by
  have habs := (abs_sub (publicShift security primary seed) scalar.val).trans
    (add_le_add (publicShift_bound security primary seed) (InwardAnchor.scalar_bound security scalar))
  have hclear := DiffuseProfiles.deletion_clearance security
  simp only [DiffuseProfiles.deletion] at hclear
  omega

def diffuseLaw (security : ℕ) (primary : Palette security) (scalar : FirstHistogram.Scalar security)
    (seed : PublicSeed security) : FiniteDist (Palette security × Palette security) where
  weight pair := TrimmedSlice.orderedPairSlice (Parameters.modulus security) 1
    (publicShift security primary seed - scalar.val) pair.1 pair.2
  nonneg pair := TrimmedSlice.orderedPairSlice_nonneg _ _ _ _ _
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [TrimmedSlice.orderedPairSlice_marginal (Parameters.modulus security) 1
      (publicShift security primary seed - scalar.val) (by norm_num)]
    exact TrimmedSlice.law_palette_mass _ _ _ (by norm_num) (diffuse_shift_clearance security primary scalar seed)

def refinedPair (security : ℕ) (primary : Palette security) (scalar : FirstHistogram.Scalar security)
    (seed : PublicSeed security) : FiniteDist (Palette security × Palette security) :=
  if seed.marked then markedLaw security primary scalar seed else diffuseLaw security primary scalar seed

theorem markedLaw_charge (security : ℕ) (primary : Palette security) (scalar : FirstHistogram.Scalar security)
    (seed : PublicSeed security) (pair : Palette security × Palette security)
    (hweight : (markedLaw security primary scalar seed).weight pair ≠ 0) :
    (pair.1.val : ℤ) + pair.2.val = (Parameters.modulus security : ℤ) - 1 + publicShift security primary seed - scalar.val := by
  rw [markedLaw_weight] at hweight
  have hpair : pair = (primary, markedPoint security primary scalar seed) := by
    by_contra hne
    simp only [Ne.symm hne, if_false, ne_eq, not_true_eq_false] at hweight
  subst pair
  have hs := integerPoint_safe security primary seed.coin seed.anchorIndex (-scalar.val)
    (by simpa only [abs_neg] using InwardAnchor.scalar_bound security scalar)
  have hblur := abs_le.mp (blur_bound security seed)
  have hcut := InwardAnchor.sourceCutoff_pos security
  rw [markedPoint_value]
  rw [Int.toNat_of_nonneg]
  · ring
  · unfold integerPoint publicShift signedOffset at *
    rw [Parameters.safeMargin] at hs
    push_cast at hs
    omega

theorem refinedPair_charge (security : ℕ) (primary : Palette security) (scalar : FirstHistogram.Scalar security)
    (seed : PublicSeed security) (pair : Palette security × Palette security)
    (hweight : (refinedPair security primary scalar seed).weight pair ≠ 0) :
    (pair.1.val : ℤ) + pair.2.val = (Parameters.modulus security : ℤ) - 1 + publicShift security primary seed - scalar.val := by
  unfold refinedPair at hweight
  split_ifs at hweight with hmarked
  · exact markedLaw_charge security primary scalar seed pair hweight
  · change TrimmedSlice.orderedPairSlice (Parameters.modulus security) 1
      (publicShift security primary seed - scalar.val) pair.1 pair.2 ≠ 0 at hweight
    unfold TrimmedSlice.orderedPairSlice at hweight
    by_contra hcharge
    have hne : (pair.2.val : ℤ) ≠ (Parameters.modulus security : ℤ) - 1 +
        (publicShift security primary seed - scalar.val) - pair.1.val := by omega
    simp only [hne, if_false, mul_zero, ne_eq, not_true_eq_false] at hweight


theorem refinedPair_modular_charge (security : ℕ) (primary : Palette security) (scalar : FirstHistogram.Scalar security)
    (seed : PublicSeed security) (pair : Palette security × Palette security)
    (hweight : (refinedPair security primary scalar seed).weight pair ≠ 0) :
    (ZMod.finEquiv (Parameters.modulus security)) pair.1 + (ZMod.finEquiv (Parameters.modulus security)) pair.2 =
      (-1 : ZMod (Parameters.modulus security)) + (publicShift security primary seed : ZMod (Parameters.modulus security)) -
        (scalar.val : ZMod (Parameters.modulus security)) := by
  have h := congrArg (fun value : ℤ => (value : ZMod (Parameters.modulus security)))
    (refinedPair_charge security primary scalar seed pair hweight)
  rw [finEquiv_natCast, finEquiv_natCast]
  simpa only [Int.cast_add, Int.cast_sub, Int.cast_natCast, Int.cast_one, ZMod.natCast_self,
    zero_sub] using h

theorem refinedPair_eventMass_charge (security : ℕ) (primary : Palette security) (scalar : FirstHistogram.Scalar security)
    (seed : PublicSeed security) :
    (refinedPair security primary scalar seed).eventMass (fun pair =>
      (pair.1.val : ℤ) + pair.2.val = (Parameters.modulus security : ℤ) - 1 + publicShift security primary seed - scalar.val) = 1 := by
  unfold FiniteDist.eventMass
  calc
    _ = ∑ pair, (refinedPair security primary scalar seed).weight pair := by
      apply Finset.sum_congr rfl
      intro pair _
      split_ifs with hcharge
      · rfl
      · have hz : (refinedPair security primary scalar seed).weight pair = 0 := by
          by_contra hne
          exact hcharge (refinedPair_charge security primary scalar seed pair hne)
        exact hz.symm
    _ = 1 := (refinedPair security primary scalar seed).sum_one

end
end CurrentAFT.ActualPublicLegCharge
