import AFT.CoreWindowKernel
import AFT.SmoothingDifference
import CurrentAFT.FirstResponse

/-!
# Full smoothing cost of the true trimmed integer-window pair

The cyclic comparison retains the original varying slice denominator and
both endpoint masks. A no-wrap argument is proved for an arbitrary modulus,
then the complete integer translation estimate is averaged under any actual
finite protected-root law. No old parameter family is used.
-/

namespace CurrentAFT.PairSmoothing

open AFT AFT.TrimmedSlice AFT.SafeConvolution
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem finEquiv_symm_val (modulus : ℕ) [NeZero modulus] (color : ZMod modulus) :
    ((ZMod.finEquiv modulus).symm color).val = color.val := by
  cases modulus with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ modulus => rfl

theorem sub_val_on_core (modulus : ℕ) [NeZero modulus] (core shift : ℤ)
    (color : ZMod modulus) (hshift : |shift| ≤ core)
    (hl : core ≤ ((color - (shift : ZMod modulus)).val : ℤ))
    (hu : ((color - (shift : ZMod modulus)).val : ℤ) < (modulus : ℤ) - core) :
    ((color - (shift : ZMod modulus)).val : ℤ) = color.val - shift := by
  let input := color - (shift : ZMod modulus)
  have hlo : 0 ≤ (input.val : ℤ) + shift := by
    dsimp only [input]
    have hh := abs_le.mp hshift
    omega
  have hhi : (input.val : ℤ) + shift < modulus := by
    dsimp only [input]
    have hh := abs_le.mp hshift
    omega
  have heq : (((input.val : ℤ) + shift : ℤ) : ZMod modulus) = color := by
    rw [Int.cast_add, Int.cast_natCast, ZMod.natCast_zmod_val]
    dsimp only [input]
    abel
  have hv : (((((input.val : ℤ) + shift : ℤ) : ZMod modulus)).val : ℤ) = input.val + shift := by
    rw [ZMod.val_intCast, Int.emod_eq_of_lt hlo hhi]
  rw [heq] at hv
  dsimp only [input] at hv
  omega

theorem core_profile_translation (modulus : ℕ) [NeZero modulus] (core : ℤ) (hcore : 0 ≤ core)
    (profile : ℤ → ℤ → ℝ)
    (hsupport : ∀ first second, profile first second ≠ 0 →
      (core ≤ first ∧ first < (modulus : ℤ) - core) ∧
      (core ≤ second ∧ second < (modulus : ℤ) - core))
    (firstShift secondShift : ℤ) (hfirst : |firstShift| ≤ core) (hsecond : |secondShift| ≤ core)
    (first second : ZMod modulus) :
    profile ((first - (firstShift : ZMod modulus)).val : ℤ)
        ((second - (secondShift : ZMod modulus)).val : ℤ) =
      profile ((first.val : ℤ) - firstShift) ((second.val : ℤ) - secondShift) := by
  by_cases hn : profile ((first - (firstShift : ZMod modulus)).val : ℤ)
      ((second - (secondShift : ZMod modulus)).val : ℤ) = 0
  · rw [hn]
    symm
    by_contra hneq
    have hh := hsupport _ _ hneq
    have hl1 : 0 ≤ (first.val : ℤ) - firstShift := hcore.trans hh.1.1
    have hu1 : (first.val : ℤ) - firstShift < modulus := by linarith [hh.1.2]
    have hl2 : 0 ≤ (second.val : ℤ) - secondShift := hcore.trans hh.2.1
    have hu2 : (second.val : ℤ) - secondShift < modulus := by linarith [hh.2.2]
    have heq1 : (((first.val : ℤ) - firstShift : ℤ) : ZMod modulus) = first - (firstShift : ZMod modulus) := by
      rw [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val]
    have heq2 : (((second.val : ℤ) - secondShift : ℤ) : ZMod modulus) = second - (secondShift : ZMod modulus) := by
      rw [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val]
    have hv1 : ((first - (firstShift : ZMod modulus)).val : ℤ) = first.val - firstShift := by
      rw [← heq1, ZMod.val_intCast, Int.emod_eq_of_lt hl1 hu1]
    have hv2 : ((second - (secondShift : ZMod modulus)).val : ℤ) = second.val - secondShift := by
      rw [← heq2, ZMod.val_intCast, Int.emod_eq_of_lt hl2 hu2]
    rw [hv1, hv2] at hn
    exact hneq hn
  · have hh := hsupport _ _ hn
    rw [sub_val_on_core modulus core firstShift first hfirst hh.1.1 hh.1.2,
      sub_val_on_core modulus core secondShift second hsecond hh.2.1 hh.2.2]

def liftedRestrictedPair (modulus coreDepth : ℕ) [NeZero modulus]
    (boundary start source : ℤ) (width : ℕ) (color : ZMod modulus × ZMod modulus) : ℝ :=
  SafePair.restrictPair (paletteSlice modulus coreDepth 0)
    (averagedPair modulus boundary start source width)
      ((ZMod.finEquiv modulus).symm color.1) ((ZMod.finEquiv modulus).symm color.2)

theorem restrictedPair_translation_square_le (modulus coreDepth radius : ℕ) [NeZero modulus]
    (boundary start source shiftBound cutoff : ℤ) (width : ℕ) (lower : ℝ) (hlower : 0 < lower)
    (hcore : 2 * coreDepth ≤ modulus) (hboundary : boundary ≤ coreDepth)
    (firstShift secondShift : ℤ) (hfirst : |firstShift| ≤ radius) (hsecond : |secondShift| ≤ radius)
    (hradius : radius ≤ coreDepth)
    (hstarts : ∀ shift ∈ anchorInterval start width, |shift| ≤ shiftBound) (hsource : |source| ≤ cutoff)
    (hclear : lower ≤ (modulus : ℝ) - 2 * boundary - shiftBound - cutoff) :
    (∑ color : ZMod modulus × ZMod modulus,
      (liftedRestrictedPair modulus coreDepth boundary start source width
        (color - ((firstShift : ZMod modulus), (secondShift : ZMod modulus))) -
       liftedRestrictedPair modulus coreDepth boundary start source width color) ^ 2) ≤
      16 * (modulus : ℝ) * radius / (lower ^ 2 * (width : ℝ) ^ 2) +
      16 * (modulus : ℝ) * (radius : ℝ) ^ 2 / (lower ^ 4 * width) +
      8 * (radius : ℝ) / (lower ^ 2 * width) := by
  let integerMass := maskedIntegerPair modulus boundary lower start source width coreDepth (modulus - 2 * coreDepth)
  have heq (color : ZMod modulus × ZMod modulus) :
      liftedRestrictedPair modulus coreDepth boundary start source width color =
        integerMass color.1.val color.2.val := by
    rw [liftedRestrictedPair, restricted_averagedPair_eq_maskedIntegerPair modulus coreDepth
      boundary start source shiftBound cutoff width lower hlower hcore hboundary hstarts hsource hclear]
    simp only [finEquiv_symm_val]
    rfl
  have hsupport (first second : ℤ) (hn : integerMass first second ≠ 0) :
      ((coreDepth : ℤ) ≤ first ∧ first < (modulus : ℤ) - coreDepth) ∧
      ((coreDepth : ℤ) ≤ second ∧ second < (modulus : ℤ) - coreDepth) := by
    dsimp only [integerMass, maskedIntegerPair] at hn
    split_ifs at hn with hmask
    · exact ⟨(core_interval_mem _ _ hcore _).mp hmask.1,
        (core_interval_mem _ _ hcore _).mp hmask.2⟩
    · exact (hn rfl).elim
  have htranslation (color : ZMod modulus × ZMod modulus) :
      liftedRestrictedPair modulus coreDepth boundary start source width
          (color - ((firstShift : ZMod modulus), (secondShift : ZMod modulus))) =
        integerMass ((color.1.val : ℤ) - firstShift) ((color.2.val : ℤ) - secondShift) := by
    rw [heq]
    exact core_profile_translation modulus coreDepth (by positivity) integerMass hsupport firstShift secondShift
      (hfirst.trans (by exact_mod_cast hradius)) (hsecond.trans (by exact_mod_cast hradius)) color.1 color.2
  simp only [htranslation, heq, Fintype.sum_prod_type]
  have hinj : Function.Injective (fun color : ZMod modulus => (color.val : ℤ)) := by
    intro a b hequal
    apply ZMod.val_injective modulus
    dsimp only at hequal
    exact_mod_cast hequal
  have hh := maskedIntegerPair_translation_square_le
    (fun color : ZMod modulus => (color.val : ℤ)) hinj modulus boundary lower hlower start source
    firstShift secondShift coreDepth width (modulus - 2 * coreDepth)
  simp only [ZMod.card] at hh
  have habuR : |(firstShift : ℝ)| ≤ radius := by exact_mod_cast hfirst
  have habvR : |(secondShift : ℝ)| ≤ radius := by exact_mod_cast hsecond
  have habsum : |((firstShift + secondShift : ℤ) : ℝ)| ≤ 2 * (radius : ℝ) := by
    push_cast
    linarith [abs_add_le (firstShift : ℝ) secondShift]
  have hsum : ((firstShift + secondShift).natAbs : ℝ) ≤ 2 * radius := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using habsum
  have hsquare : (((firstShift + secondShift : ℤ) : ℝ)) ^ 2 ≤ (2 * (radius : ℝ)) ^ 2 := by
    simpa only [← sq, sq_abs] using mul_self_le_mul_self (abs_nonneg _) habsum
  have hboth : (firstShift.natAbs : ℝ) + secondShift.natAbs ≤ 2 * radius := by
    simpa only [Nat.cast_natAbs, Int.cast_abs, two_mul] using add_le_add habuR habvR
  apply hh.trans
  calc
    _ ≤ 2 * (modulus : ℝ) *
        (4 * (2 * (radius : ℝ)) / (lower ^ 2 * (width : ℝ) ^ 2) +
          2 * (2 * (radius : ℝ)) ^ 2 / (lower ^ 4 * width)) +
        4 * (2 * (radius : ℝ)) / (lower ^ 2 * width) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply add_le_add
        · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (by norm_num)) (by positivity)
        · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsquare (by norm_num)) (by positivity)
      · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hboth (by norm_num)) (by positivity)
    _ = _ := by ring

def smoothProfile {State Seed : Type*} [Fintype Seed] [Sub State]
    (source : FiniteDist Seed) (shifts : Seed → State) (profile : State → ℝ) : State → ℝ :=
  fun color => ∑ seed, source.weight seed * profile (color - shifts seed)

theorem smoothProfile_difference_square_le {State Seed : Type*} [Fintype State] [Fintype Seed] [Sub State]
    (source : FiniteDist Seed) (shifts : Seed → State) (profile : State → ℝ) (bound : ℝ)
    (hbound : ∀ seed, (∑ color, (profile (color - shifts seed) - profile color) ^ 2) ≤ bound) :
    (∑ color, (smoothProfile source shifts profile color - profile color) ^ 2) ≤ bound := by
  have heq (color : State) : smoothProfile source shifts profile color - profile color =
      ∑ seed, source.weight seed * (profile (color - shifts seed) - profile color) := by
    simp only [smoothProfile, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, source.sum_one, one_mul]
  simp only [heq]
  exact probability_profile_mixture_square_le_uniform source _ bound hbound

theorem restrictedPair_smoothing_square_le {Seed : Type*} [Fintype Seed]
    (modulus coreDepth radius : ℕ) [NeZero modulus]
    (boundary start scalar shiftBound cutoff : ℤ) (width : ℕ) (lower : ℝ) (hlower : 0 < lower)
    (hcore : 2 * coreDepth ≤ modulus) (hboundary : boundary ≤ coreDepth) (hradius : radius ≤ coreDepth)
    (source : FiniteDist Seed) (firstShift secondShift : Seed → ℤ)
    (hfirst : ∀ seed, |firstShift seed| ≤ radius) (hsecond : ∀ seed, |secondShift seed| ≤ radius)
    (hstarts : ∀ shift ∈ anchorInterval start width, |shift| ≤ shiftBound) (hscalar : |scalar| ≤ cutoff)
    (hclear : lower ≤ (modulus : ℝ) - 2 * boundary - shiftBound - cutoff) :
    let profile := liftedRestrictedPair modulus coreDepth boundary start scalar width
    (∑ color, (smoothProfile source
      (fun seed => ((firstShift seed : ZMod modulus), (secondShift seed : ZMod modulus))) profile color - profile color) ^ 2) ≤
      16 * (modulus : ℝ) * radius / (lower ^ 2 * (width : ℝ) ^ 2) +
      16 * (modulus : ℝ) * (radius : ℝ) ^ 2 / (lower ^ 4 * width) +
      8 * (radius : ℝ) / (lower ^ 2 * width) := by
  apply smoothProfile_difference_square_le
  intro seed
  exact restrictedPair_translation_square_le modulus coreDepth radius boundary start scalar shiftBound cutoff width lower
    hlower hcore hboundary (firstShift seed) (secondShift seed) (hfirst seed) (hsecond seed)
      hradius hstarts hscalar hclear

theorem smoothProfile_mixture {State Seed Index : Type*}
    [Fintype Seed] [Fintype Index] [Sub State]
    (source : FiniteDist Seed) (shifts : Seed → State) (weights : Index → ℝ)
    (profiles : Index → State → ℝ) (color : State) :
    smoothProfile source shifts (fun point => ∑ index, weights index * profiles index point) color =
      ∑ index, weights index * smoothProfile source shifts (profiles index) color := by
  simp only [smoothProfile, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro index _
  apply Finset.sum_congr rfl
  intro seed _
  ring

def liftedRestrictedMixedPair {Index : Type*} [Fintype Index]
    (modulus coreDepth : ℕ) [NeZero modulus] (boundary : ℤ)
    (starts scalars : Index → ℤ) (law : FiniteDist Index) (width : ℕ)
    (color : ZMod modulus × ZMod modulus) : ℝ :=
  SafePair.restrictPair (paletteSlice modulus coreDepth 0)
    (mixedPair modulus boundary starts scalars law.weight width)
      ((ZMod.finEquiv modulus).symm color.1) ((ZMod.finEquiv modulus).symm color.2)

theorem liftedRestrictedMixedPair_mixture {Index : Type*} [Fintype Index]
    (modulus coreDepth : ℕ) [NeZero modulus] (boundary : ℤ)
    (starts scalars : Index → ℤ) (law : FiniteDist Index) (width : ℕ)
    (color : ZMod modulus × ZMod modulus) :
    liftedRestrictedMixedPair modulus coreDepth boundary starts scalars law width color =
      ∑ index, law.weight index *
        liftedRestrictedPair modulus coreDepth boundary (starts index) (scalars index) width color := by
  by_cases hc : (ZMod.finEquiv modulus).symm color.1 ∈ paletteSlice modulus coreDepth 0 ∧
      (ZMod.finEquiv modulus).symm color.2 ∈ paletteSlice modulus coreDepth 0
  · simp only [liftedRestrictedMixedPair, liftedRestrictedPair, SafePair.restrictPair, hc, and_self, if_true, mixedPair]
  · simp only [liftedRestrictedMixedPair, liftedRestrictedPair, SafePair.restrictPair, hc,
      if_false, mul_zero, Finset.sum_const_zero]

theorem restrictedMixedPair_smoothing_square_le {Seed Index : Type*} [Fintype Seed] [Fintype Index]
    (modulus coreDepth radius : ℕ) [NeZero modulus]
    (boundary shiftBound cutoff : ℤ) (width : ℕ) (lower : ℝ) (hlower : 0 < lower)
    (hcore : 2 * coreDepth ≤ modulus) (hboundary : boundary ≤ coreDepth) (hradius : radius ≤ coreDepth)
    (starts scalars : Index → ℤ) (law : FiniteDist Index)
    (source : FiniteDist Seed) (firstShift secondShift : Seed → ℤ)
    (hfirst : ∀ seed, |firstShift seed| ≤ radius) (hsecond : ∀ seed, |secondShift seed| ≤ radius)
    (hstarts : ∀ index shift, shift ∈ anchorInterval (starts index) width → |shift| ≤ shiftBound)
    (hscalar : ∀ index, |scalars index| ≤ cutoff)
    (hclear : lower ≤ (modulus : ℝ) - 2 * boundary - shiftBound - cutoff) :
    let profile := liftedRestrictedMixedPair modulus coreDepth boundary starts scalars law width
    (∑ color, (smoothProfile source
      (fun seed => ((firstShift seed : ZMod modulus), (secondShift seed : ZMod modulus))) profile color - profile color) ^ 2) ≤
      16 * (modulus : ℝ) * radius / (lower ^ 2 * (width : ℝ) ^ 2) +
      16 * (modulus : ℝ) * (radius : ℝ) ^ 2 / (lower ^ 4 * width) +
      8 * (radius : ℝ) / (lower ^ 2 * width) := by
  have hmass : liftedRestrictedMixedPair modulus coreDepth boundary starts scalars law width =
      fun color => ∑ index, law.weight index *
        liftedRestrictedPair modulus coreDepth boundary (starts index) (scalars index) width color := by
    funext color
    exact liftedRestrictedMixedPair_mixture modulus coreDepth boundary starts scalars law width color
  dsimp only
  rw [hmass]
  simp only [smoothProfile_mixture, ← Finset.sum_sub_distrib, ← mul_sub]
  apply probability_profile_mixture_square_le_uniform law
  intro index
  exact restrictedPair_smoothing_square_le modulus coreDepth radius boundary (starts index) (scalars index)
    shiftBound cutoff width lower hlower hcore hboundary hradius source firstShift secondShift
      hfirst hsecond (hstarts index) (hscalar index) hclear

end

end CurrentAFT.PairSmoothing
