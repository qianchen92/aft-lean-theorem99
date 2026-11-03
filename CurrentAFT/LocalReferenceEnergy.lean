import CurrentAFT.FirstHistogram
import CurrentAFT.GaussianHeights
import AFT.ActivatedPair
import AFT.JointSignedChannel

/-!
# Actual fixed-source local pair Hilbert estimates

The protected scalar is fixed before estimating the operator. All public
blur, midpoint, anchor-index, and integer-slice draws are the concrete
current laws. Thus later root/retained inputs can be arbitrary joint
functions, and no inverse root or sign probability is introduced.
-/

namespace CurrentAFT.LocalReferenceEnergy

open AFT DiffuseProfiles ProposalPrimary FirstHistogram
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
  primaryLaw centerLaw activation actualSeedLaw

abbrev Palette (security : ℕ) := FirstHistogram.Palette security
abbrev Pair (security : ℕ) := FirstHistogram.Pair security
abbrev Scalar (security : ℕ) := FirstHistogram.Scalar security
abbrev BlurSeed (security : ℕ) :=
  GaussianSource.Window (edgeCutoff security) × GaussianSource.Window (edgeCutoff security)

def publicBlurLaw (security : ℕ) : FiniteDist (BlurSeed security) :=
  (edgeLaw security).prod (edgeLaw security)

def diffusePairAt (security : ℕ) (primary : Palette security) (scalar : Scalar security) : FiniteDist (Pair security) :=
  (FiniteDist.uniform Bool).mix (fun coin =>
    (publicBlurLaw security).mix (fun edge =>
      diffuseSeedPair security (InwardAnchor.positiveDirection security primary coin) (edge, scalar)))

def markedCompanionAt (security : ℕ) (primary : Palette security) (scalar : Scalar security) :
    FiniteDist (Palette security) :=
  (publicBlurLaw security).mix (fun edge =>
    (InwardAnchor.shiftedAnchorLaw security primary (-scalar.val)
      (by simpa only [abs_neg] using InwardAnchor.scalar_bound security scalar)).map
        (shiftEquiv security (edge.1.val - edge.2.val)))

def markedPairAt (security : ℕ) (primary : Palette security) (scalar : Scalar security) : FiniteDist (Pair security) :=
  (markedCompanionAt security primary scalar).map (fun companion => (primary, companion))

def pairAt (security : ℕ) (primary : Palette security) (scalar : Scalar security) : FiniteDist (Pair security) where
  weight pair := (1 - activation security) * (diffusePairAt security primary scalar).weight pair +
    activation security * (markedPairAt security primary scalar).weight pair
  nonneg pair := add_nonneg
    (mul_nonneg (by linarith [activation_le_half security]) ((diffusePairAt security primary scalar).nonneg pair))
    (mul_nonneg (activation_pos security).le ((markedPairAt security primary scalar).nonneg pair))
  sum_one := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, FiniteDist.sum_one, FiniteDist.sum_one]
    ring

private theorem averagedPair_height (modulus width cutoff : ℕ) (start source : ℤ)
    (hwidth : 0 < width) (hdelete : 2 * (2 + 2 * width + 2 * cutoff) ≤ modulus)
    (hstart : ∀ offset ∈ anchorInterval start width,
      |offset| ≤ 2 * (width : ℤ) + ((cutoff : ℤ) - 1))
    (hsource : |source| ≤ (cutoff : ℤ) - 1) (first second : Fin modulus) :
    TrimmedSlice.averagedPair modulus 1 start source width first second ≤
      2 / ((width : ℝ) * modulus) := by
  have hclear : 2 * (1 : ℤ) + (2 * (width : ℤ) + ((cutoff : ℤ) - 1)) +
      ((cutoff : ℤ) - 1) < modulus := by omega
  have h := TrimmedSlice.mixedPair_le modulus 1
    (2 * (width : ℤ) + ((cutoff : ℤ) - 1)) ((cutoff : ℤ) - 1) width
    (fun _ : Unit => start) (fun _ : Unit => source) (FiniteDist.uniform Unit).weight
    (FiniteDist.uniform Unit).nonneg (FiniteDist.uniform Unit).sum_one
    (fun _ => hstart) (fun _ => hsource) hclear first second
  simp only [TrimmedSlice.mixedPair, Fintype.sum_unique, FiniteDist.uniform_weight,
    Fintype.card_unique, Nat.cast_one, inv_one, one_mul] at h
  apply h.trans
  have hq : (0 : ℝ) < modulus := by exact_mod_cast (by omega : 0 < modulus)
  have hw : (0 : ℝ) < width := Nat.cast_pos.mpr hwidth
  have hd := Nat.cast_le (α := ℝ).mpr hdelete
  push_cast at hd
  have hden : 0 < (modulus : ℝ) - 2 - (2 * width + ((cutoff : ℝ) - 1)) - ((cutoff : ℝ) - 1) := by linarith
  push_cast
  norm_num only [mul_one]
  apply (div_le_div_iff₀ (mul_pos hw hden) (mul_pos hw hq)).mpr
  nlinarith only [hd, hw]

theorem diffuseSeedPair_height (security : ℕ) (positive : Bool) (seed : ActualSeed security)
    (first second : Palette security) :
    (diffuseSeedPair security positive seed).weight (first, second) ≤
      2 / ((Parameters.anchorWidth security : ℝ) * Parameters.modulus security) := by
  rw [diffuseSeedPair_weight]
  apply averagedPair_height _ _ _ _ _ (InwardAnchor.anchorWidth_pos security)
  · exact FirstResponse.two_deletion_le_modulus security
  · exact fun offset hin => interval_bound positive _ _ _ _ (actualBlur_bound security seed) hin
  · exact actualSecond_bound security seed

theorem diffusePairAt_height (security : ℕ) (primary : Palette security) (scalar : Scalar security)
    (first second : Palette security) :
    (diffusePairAt security primary scalar).weight (first, second) ≤
      2 / ((Parameters.anchorWidth security : ℝ) * Parameters.modulus security) := by
  unfold diffusePairAt
  simp only [FiniteDist.mix_weight]
  calc
    _ ≤ ∑ coin, (FiniteDist.uniform Bool).weight coin *
        ∑ edge, (publicBlurLaw security).weight edge *
          (2 / ((Parameters.anchorWidth security : ℝ) * Parameters.modulus security)) := by
      apply Finset.sum_le_sum
      intro coin _
      apply mul_le_mul_of_nonneg_left _ (FiniteDist.nonneg _ _)
      exact Finset.sum_le_sum (fun edge _ => mul_le_mul_of_nonneg_left
        (diffuseSeedPair_height security _ _ first second) ((publicBlurLaw security).nonneg edge))
    _ = _ := by simp only [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

theorem markedCompanionAt_height (security : ℕ) (primary : Palette security) (scalar : Scalar security)
    (output : Palette security) :
    (markedCompanionAt security primary scalar).weight output ≤ 1 / (Parameters.anchorWidth security : ℝ) := by
  unfold markedCompanionAt
  simp only [FiniteDist.mix_weight, FiniteDist.map_equiv_weight]
  calc
    _ ≤ ∑ edge, (publicBlurLaw security).weight edge * (1 / (Parameters.anchorWidth security : ℝ)) :=
      Finset.sum_le_sum (fun edge _ => mul_le_mul_of_nonneg_left
        (InwardAnchor.shiftedAnchorLaw_height security primary _ _ _) ((publicBlurLaw security).nonneg edge))
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

def uniformReference (security : ℕ) : FiniteDist (Palette security) := FiniteDist.uniform _

theorem uniformReference_weight (security : ℕ) (color : Palette security) :
    (uniformReference security).weight color = 1 / (Parameters.modulus security : ℝ) := by
  simp only [uniformReference, FiniteDist.uniform_weight, Fintype.card_fin, one_div]

theorem diffusePairAt_energy (security : ℕ) (primary : Palette security) (scalar : Scalar security) :
    BlockDensity.pairEnergy (uniformReference security).weight (uniformReference security).weight
      (fun first second => (diffusePairAt security primary scalar).weight (first, second)) ≤
        2 * (Parameters.modulus security : ℝ) / Parameters.anchorWidth security := by
  have hq := FirstResponse.modulus_pos security
  have hw : (0 : ℝ) < Parameters.anchorWidth security := Nat.cast_pos.mpr (InwardAnchor.anchorWidth_pos security)
  have h := BlockDensity.diffuse_pair_energy_le
    (uniformReference security).weight (uniformReference security).weight
    (fun first second => (diffusePairAt security primary scalar).weight (first, second))
    (1 / (Parameters.modulus security : ℝ)) (1 / (Parameters.modulus security : ℝ))
    (2 / ((Parameters.anchorWidth security : ℝ) * Parameters.modulus security))
    (by positivity) (by positivity) (by positivity)
    (fun color => (uniformReference_weight security color).ge) (fun color => (uniformReference_weight security color).ge)
    (fun first second => (diffusePairAt security primary scalar).nonneg (first, second))
    (diffusePairAt_height security primary scalar)
    (by have hmass := (diffusePairAt security primary scalar).sum_one
        rw [Fintype.sum_prod_type] at hmass; exact hmass.le)
  convert h using 1
  field_simp

/-- Finite weighted Cauchy--Schwarz before summing the full output pair.
The input score can have arbitrary signs. -/
theorem pair_channel_energy_le {Input Color : Type*} [Fintype Input] [Fintype Color]
    (input : FiniteDist Input) (reference : FiniteDist Color)
    (hreference : ∀ color, 0 < reference.weight color)
    (channel : Input → FiniteDist (Color × Color)) (score : Input → ℝ) (bound : ℝ)
    (hbound : ∀ point, BlockDensity.pairEnergy reference.weight reference.weight
      (fun first second => (channel point).weight (first, second)) ≤ bound) :
    BlockDensity.pairEnergy reference.weight reference.weight
      (fun first second => ∑ point, input.weight point * score point * (channel point).weight (first, second)) ≤
        bound * input.expectation (fun point => score point ^ 2) := by
  have hcauchy (first second : Color) :
      (∑ point, input.weight point * score point * (channel point).weight (first, second)) ^ 2 ≤
        input.expectation (fun point => score point ^ 2) *
          ∑ point, input.weight point * (channel point).weight (first, second) ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    · intro point _; exact mul_nonneg (input.nonneg point) (sq_nonneg _)
    · intro point _; exact mul_nonneg (input.nonneg point) (sq_nonneg _)
    · intro point _; ring
  unfold BlockDensity.pairEnergy
  calc
    _ ≤ ∑ first, ∑ second, input.expectation (fun point => score point ^ 2) *
        (∑ point, input.weight point * (channel point).weight (first, second) ^ 2) /
          (reference.weight first * reference.weight second) :=
      Finset.sum_le_sum (fun first _ => Finset.sum_le_sum (fun second _ =>
        div_le_div_of_nonneg_right (hcauchy first second) (mul_pos (hreference first) (hreference second)).le))
    _ = input.expectation (fun point => score point ^ 2) *
        ∑ point, input.weight point * BlockDensity.pairEnergy reference.weight reference.weight
          (fun first second => (channel point).weight (first, second)) := by
      simp only [BlockDensity.pairEnergy, Finset.mul_sum, Finset.sum_div, mul_div_assoc]
      conv_lhs => arg 2; ext first; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
    _ ≤ _ := by
      have haverage : (∑ point, input.weight point * BlockDensity.pairEnergy reference.weight reference.weight
          (fun first second => (channel point).weight (first, second))) ≤ bound := by
        calc
          _ ≤ ∑ point, input.weight point * bound :=
            Finset.sum_le_sum (fun point _ => mul_le_mul_of_nonneg_left (hbound point) (input.nonneg point))
          _ = bound := by rw [← Finset.sum_mul, input.sum_one, one_mul]
      have hnonneg : 0 ≤ input.expectation (fun point => score point ^ 2) :=
        Finset.sum_nonneg (fun point _ => mul_nonneg (input.nonneg point) (sq_nonneg (score point)))
      exact (mul_le_mul_of_nonneg_left haverage hnonneg).trans_eq (by ring)

def signedDiffusePair (security : ℕ) (scalar : Scalar security) (score : Palette security → ℝ)
    (first second : Palette security) : ℝ :=
  ∑ primary, (primaryLaw security).weight primary * score primary *
    (diffusePairAt security primary scalar).weight (first, second)

def signedMarkedPair (security : ℕ) (scalar : Scalar security) (score : Palette security → ℝ)
    (first second : Palette security) : ℝ :=
  activation security * (primaryLaw security).weight first * score first *
    (markedCompanionAt security first scalar).weight second

def signedPairAt (security : ℕ) (scalar : Scalar security) (score : Palette security → ℝ)
    (first second : Palette security) : ℝ :=
  ∑ primary, (primaryLaw security).weight primary * score primary * (pairAt security primary scalar).weight (first, second)

theorem markedPairAt_weight (security : ℕ) (primary : Palette security) (scalar : Scalar security)
    (first second : Palette security) :
    (markedPairAt security primary scalar).weight (first, second) =
      if primary = first then (markedCompanionAt security primary scalar).weight second else 0 := by
  classical
  unfold markedPairAt
  rw [FiniteDist.map_weight]
  by_cases hequal : primary = first
  · subst first
    simp only [Prod.mk.injEq, true_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · simp only [Prod.mk.injEq, hequal, false_and, if_false, Finset.sum_const_zero]

theorem signedPairAt_decomposition (security : ℕ) (scalar : Scalar security)
    (score : Palette security → ℝ) (first second : Palette security) :
    signedPairAt security scalar score first second =
      (1 - activation security) * signedDiffusePair security scalar score first second +
        signedMarkedPair security scalar score first second := by
  classical
  unfold signedPairAt signedDiffusePair signedMarkedPair
  simp only [pairAt, markedPairAt_weight, mul_add, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro primary _
    ring
  · simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring

theorem signedDiffusePair_energy (security : ℕ) (scalar : Scalar security) (score : Palette security → ℝ) :
    BlockDensity.pairEnergy (uniformReference security).weight (uniformReference security).weight
      (signedDiffusePair security scalar score) ≤
        (2 * (Parameters.modulus security : ℝ) / Parameters.anchorWidth security) *
          (primaryLaw security).expectation (fun primary => score primary ^ 2) := by
  apply pair_channel_energy_le
  · intro color
    rw [uniformReference_weight]
    exact one_div_pos.mpr (FirstResponse.modulus_pos security)
  · exact fun primary => diffusePairAt_energy security primary scalar

def primaryMaximum (security : ℕ) : ℝ :=
  (Parameters.dimension security : ℝ) / (markMass security * Parameters.modulus security)

theorem signedMarkedPair_energy (security : ℕ) (scalar : Scalar security) (score : Palette security → ℝ) :
    BlockDensity.pairEnergy (uniformReference security).weight (uniformReference security).weight
      (signedMarkedPair security scalar score) ≤
        (activation security ^ 2 * (Parameters.modulus security : ℝ) ^ 2 * primaryMaximum security /
          Parameters.anchorWidth security) * (primaryLaw security).expectation (fun primary => score primary ^ 2) := by
  have hq := FirstResponse.modulus_pos security
  have hw : (0 : ℝ) < Parameters.anchorWidth security := Nat.cast_pos.mpr (InwardAnchor.anchorWidth_pos security)
  have hp (color : Palette security) : 0 < (primaryLaw security).weight color :=
    (by positivity : (0 : ℝ) < 1 / (2 * (Parameters.modulus security : ℝ))).trans_le
      (by simpa only [primaryLaw] using primaryProfile_atom_lower security color)
  have h := BlockDensity.marked_pair_operator_energy_le (uniformReference security).weight
    (uniformReference security).weight (primaryLaw security).weight
    (fun primary => (primaryLaw security).weight primary * score primary)
    (fun primary => markedCompanionAt security primary scalar)
    (activation security) (1 / (Parameters.modulus security : ℝ)) (1 / (Parameters.modulus security : ℝ))
    (1 / (Parameters.anchorWidth security : ℝ)) (primaryMaximum security)
    (by positivity) (by positivity) (by positivity)
    (fun color => (uniformReference_weight security color).ge) (fun color => (uniformReference_weight security color).ge)
    (fun primary output => markedCompanionAt_height security primary scalar output) hp
    (GaussianHeights.primaryLaw_upper security)
  rw [profileSquareNorm_weight_mul] at h
  change _ ≤ _ * (primaryLaw security).expectation (fun primary => score primary ^ 2) at h
  convert h using 1
  · unfold signedMarkedPair
    congr 1
    funext first second
    ring
  · field_simp

theorem pairEnergy_smul (security : ℕ) (mass : Palette security → Palette security → ℝ) (scalar : ℝ) :
    BlockDensity.pairEnergy (uniformReference security).weight (uniformReference security).weight
      (fun first second => scalar * mass first second) = scalar ^ 2 *
        BlockDensity.pairEnergy (uniformReference security).weight (uniformReference security).weight mass := by
  simp only [BlockDensity.pairEnergy, mul_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  ring

def pairBudget (security : ℕ) : ℝ :=
  4 * (Parameters.modulus security : ℝ) / Parameters.anchorWidth security +
    2 * activation security ^ 2 * (Parameters.modulus security : ℝ) ^ 2 * primaryMaximum security /
      Parameters.anchorWidth security

/-- Actual fixed-source signed pair budget. The diffuse branch is
estimated before any sign conditioning of the score. The marked branch
retains the true primary maximum and the squared activation. -/
theorem signedPairAt_energy (security : ℕ) (scalar : Scalar security) (score : Palette security → ℝ) :
    BlockDensity.pairEnergy (uniformReference security).weight (uniformReference security).weight
      (signedPairAt security scalar score) ≤
        pairBudget security * (primaryLaw security).expectation (fun primary => score primary ^ 2) := by
  have hdiff := signedDiffusePair_energy security scalar score
  have hmark := signedMarkedPair_energy security scalar score
  have hnonnegative : 0 ≤ BlockDensity.pairEnergy (uniformReference security).weight (uniformReference security).weight
      (signedDiffusePair security scalar score) := by
    apply Finset.sum_nonneg
    intro first _
    apply Finset.sum_nonneg
    intro second _
    exact div_nonneg (sq_nonneg _) (mul_nonneg ((uniformReference security).nonneg _) ((uniformReference security).nonneg _))
  have hactivation : (1 - activation security) ^ 2 ≤ 1 := by
    have ha := activation_pos security
    have hb := activation_le_half security
    nlinarith
  have h := BlockDensity.pairEnergy_add_le (uniformReference security).weight
    (uniformReference security).nonneg
    (fun first second => (1 - activation security) * signedDiffusePair security scalar score first second)
    (signedMarkedPair security scalar score)
  simp_rw [← signedPairAt_decomposition] at h
  rw [pairEnergy_smul] at h
  have hscale := mul_le_mul_of_nonneg_right hactivation hnonnegative
  calc
    _ ≤ 2 * BlockDensity.pairEnergy (uniformReference security).weight (uniformReference security).weight
        (signedDiffusePair security scalar score) +
      2 * BlockDensity.pairEnergy (uniformReference security).weight (uniformReference security).weight
        (signedMarkedPair security scalar score) := by linarith only [h, hscale]
    _ ≤ 2 * ((2 * (Parameters.modulus security : ℝ) / Parameters.anchorWidth security) *
        (primaryLaw security).expectation (fun primary => score primary ^ 2)) +
      2 * ((activation security ^ 2 * (Parameters.modulus security : ℝ) ^ 2 * primaryMaximum security /
        Parameters.anchorWidth security) * (primaryLaw security).expectation (fun primary => score primary ^ 2)) :=
      add_le_add (mul_le_mul_of_nonneg_left hdiff (by norm_num))
        (mul_le_mul_of_nonneg_left hmark (by norm_num))
    _ = _ := by unfold pairBudget; ring

private theorem expectation_mix {Input Output : Type*} [Fintype Input] [Fintype Output]
    (law : FiniteDist Input) (kernel : Input → FiniteDist Output) (value : Output → ℝ) :
    (law.mix kernel).expectation value = law.expectation (fun input => (kernel input).expectation value) := by
  simp only [FiniteDist.expectation, FiniteDist.mix_weight, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, mul_assoc]

theorem diffuse_scalar_disintegration (security : ℕ) (primary : Palette security)
    (value : JointOutput security → ℝ) :
    (diffuseReferenceLaw security primary).expectation value =
      (scalarLaw security).expectation (fun scalar =>
        (diffusePairAt security primary scalar).expectation (fun pair => value (scalar, pair))) := by
  unfold diffuseReferenceLaw diffusePairAt
  simp_rw [expectation_mix, FiniteDist.expectation_map, Function.comp_def]
  conv_lhs => arg 2; ext coin; rw [actualSeedLaw, FiniteDist.expectation_prod]
  change (FiniteDist.uniform Bool).expectation (fun coin => (publicBlurLaw security).expectation
      (fun edge => (scalarLaw security).expectation (fun scalar =>
        (diffuseSeedPair security (InwardAnchor.positiveDirection security primary coin) (edge, scalar)).expectation
          (fun pair => value (scalar, pair))))) = _
  simp_rw [FiniteDist.expectation_comm (publicBlurLaw security) (scalarLaw security)]
  rw [FiniteDist.expectation_comm]

theorem marked_scalar_disintegration (security : ℕ) (primary : Palette security)
    (value : JointOutput security → ℝ) :
    (markedReferenceLaw security primary).expectation value =
      (scalarLaw security).expectation (fun scalar =>
        (markedPairAt security primary scalar).expectation (fun pair => value (scalar, pair))) := by
  unfold markedReferenceLaw markedPairAt markedCompanionAt
  simp_rw [expectation_mix, FiniteDist.expectation_map, Function.comp_def]
  rw [actualSeedLaw, FiniteDist.expectation_prod]
  change (publicBlurLaw security).expectation (fun edge =>
      (scalarLaw security).expectation (fun scalar =>
        (InwardAnchor.shiftedAnchorLaw security primary (-scalar.val) _).expectation (fun companion =>
          value (scalar, (primary, shiftEquiv security (edge.1.val - edge.2.val) companion))))) = _
  rw [FiniteDist.expectation_comm]
  simp_rw [expectation_mix, FiniteDist.expectation_map, Function.comp_def]

theorem pairAt_expectation (security : ℕ) (primary : Palette security) (scalar : Scalar security)
    (value : Pair security → ℝ) :
    (pairAt security primary scalar).expectation value =
      (1 - activation security) * (diffusePairAt security primary scalar).expectation value +
        activation security * (markedPairAt security primary scalar).expectation value := by
  simp only [FiniteDist.expectation, pairAt, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

/-- Exact disintegration of the previously constructed actual joint
reference. The scalar occurring in both pair and attachment is sampled
once and retained; it has not been replaced by independent copies. -/
theorem reference_scalar_disintegration (security : ℕ) (primary : Palette security)
    (value : JointOutput security → ℝ) :
    (referenceLaw security primary).expectation value =
      (scalarLaw security).expectation (fun scalar =>
        (pairAt security primary scalar).expectation (fun pair => value (scalar, pair))) := by
  rw [reference_expectation, diffuse_scalar_disintegration, marked_scalar_disintegration]
  simp only [pairAt_expectation, FiniteDist.expectation_add, FiniteDist.expectation_const_mul]

def attachmentAt (security : ℕ) (rootShift : ℤ) (scalar : Scalar security) : FiniteDist (Palette security) :=
  (safeLaw security).map (shiftEquiv security (rootShift + scalar.val))

theorem attachmentAt_height (security : ℕ) (rootShift : ℤ) (scalar : Scalar security)
    (output : Palette security) :
    (attachmentAt security rootShift scalar).weight output ≤ 4 / (Parameters.modulus security : ℝ) := by
  rw [attachmentAt, FiniteDist.map_equiv_weight]
  have hq := FirstResponse.modulus_pos security
  have hclear := Nat.cast_lt (α := ℝ).mpr (safe_clearance security)
  push_cast at hclear
  have hsafe : 0 < (Parameters.modulus security : ℝ) - 2 * Parameters.safeMargin security := by
    linarith [show (0 : ℝ) ≤ Parameters.safeMargin security from Nat.cast_nonneg _]
  have hheight : safeHeight security ≤ 4 / (Parameters.modulus security : ℝ) := by
    unfold safeHeight
    apply (div_le_div_iff₀ hsafe hq).mpr
    linarith [show (0 : ℝ) ≤ Parameters.safeMargin security from Nat.cast_nonneg _]
  exact (safeLaw_upper security _).trans hheight

theorem attachmentAt_energy (security : ℕ) (rootShift : ℤ) (scalar : Scalar security) :
    profileSquareNorm (uniformReference security).weight (attachmentAt security rootShift scalar).weight ≤ 4 := by
  have hq := FirstResponse.modulus_pos security
  have h := BlockDensity.profile_energy_le_ratio (uniformReference security).weight
    (attachmentAt security rootShift scalar).weight 4
    (fun color => by rw [uniformReference_weight]; exact one_div_pos.mpr hq)
    (attachmentAt security rootShift scalar).nonneg (fun color => by
      rw [uniformReference_weight]
      exact (attachmentAt_height security rootShift scalar color).trans_eq (by ring))
  simpa only [FiniteDist.sum_one, mul_one] using h

def tripleMassAt (security : ℕ) (rootShift : ℤ) (scalar : Scalar security)
    (score : Palette security → ℝ) (first second attached : Palette security) : ℝ :=
  signedPairAt security scalar score first second * (attachmentAt security rootShift scalar).weight attached

theorem tripleMassAt_energy (security : ℕ) (rootShift : ℤ) (scalar : Scalar security)
    (score : Palette security → ℝ) :
    BlockDensity.tripleEnergy (uniformReference security).weight (uniformReference security).weight
      (uniformReference security).weight (tripleMassAt security rootShift scalar score) ≤
        (4 * pairBudget security) * (primaryLaw security).expectation (fun primary => score primary ^ 2) := by
  have hfactor : BlockDensity.tripleEnergy (uniformReference security).weight (uniformReference security).weight
      (uniformReference security).weight (tripleMassAt security rootShift scalar score) =
        BlockDensity.pairEnergy (uniformReference security).weight (uniformReference security).weight
          (signedPairAt security scalar score) *
        profileSquareNorm (uniformReference security).weight (attachmentAt security rootShift scalar).weight := by
    unfold BlockDensity.tripleEnergy BlockDensity.pairEnergy profileSquareNorm tripleMassAt
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro first _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro second _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro attached _
    ring
  rw [hfactor]
  have hpairnonneg : 0 ≤ BlockDensity.pairEnergy (uniformReference security).weight (uniformReference security).weight
      (signedPairAt security scalar score) := by
    apply Finset.sum_nonneg
    intro first _
    apply Finset.sum_nonneg
    intro second _
    exact div_nonneg (sq_nonneg _) (mul_nonneg ((uniformReference security).nonneg _) ((uniformReference security).nonneg _))
  calc
    _ ≤ BlockDensity.pairEnergy (uniformReference security).weight (uniformReference security).weight
        (signedPairAt security scalar score) * 4 :=
      mul_le_mul_of_nonneg_left (attachmentAt_energy security rootShift scalar) hpairnonneg
    _ ≤ (pairBudget security * (primaryLaw security).expectation (fun primary => score primary ^ 2)) * 4 :=
      mul_le_mul_of_nonneg_right (signedPairAt_energy security scalar score) (by norm_num)
    _ = _ := by ring

/-- Every actual degree of the same-source signed triple, including
degrees two and three, is obtained by its genuine finite Hoeffding
projection. No tensor operator bound is supplied as a premise. -/
theorem triple_degree_energy (security : ℕ) (rootShift : ℤ) (scalar : Scalar security)
    (score : Palette security → ℝ) (degree : ℕ) :
    BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 3 => uniformReference security)
      (PhysicalBlockTensors.tripleMass (tripleMassAt security rootShift scalar score)) degree) ≤
        (32 * pairBudget security) * (primaryLaw security).expectation (fun primary => score primary ^ 2) := by
  have h := PhysicalBlockTensors.triple_degree_energy_le (uniformReference security)
    (fun color => by rw [uniformReference_weight]; exact one_div_pos.mpr (FirstResponse.modulus_pos security))
    (tripleMassAt security rootShift scalar score) degree
  have hbound := mul_le_mul_of_nonneg_left (tripleMassAt_energy security rootShift scalar score) (by norm_num : (0 : ℝ) ≤ 8)
  exact h.trans (hbound.trans_eq (by ring))

theorem tripleEnergy_average_le {Root Color : Type*} [Fintype Root] [Fintype Color]
    (source : FiniteDist Root) (reference : Color → ℝ) (hreference : ∀ color, 0 ≤ reference color)
    (mass : Root → Color → Color → Color → ℝ) :
    BlockDensity.tripleEnergy reference reference reference
      (fun first second attached => ∑ root, source.weight root * mass root first second attached) ≤
        ∑ root, source.weight root * BlockDensity.tripleEnergy reference reference reference (mass root) := by
  have h := profileSquareNorm_average_le source
    (fun output : (Color × Color) × Color => reference output.1.1 * reference output.1.2 * reference output.2)
    (fun output => mul_nonneg (mul_nonneg (hreference _) (hreference _)) (hreference _))
    (fun root output => mass root output.1.1 output.1.2 output.2)
  simpa only [profileSquareNorm, Fintype.sum_prod_type, BlockDensity.tripleEnergy] using h

def jointTripleMass {Root : Type*} [Fintype Root] (security : ℕ) (source : FiniteDist Root)
    (rootShift : Root → ℤ) (scalar : Root → Scalar security) (score : Root → Palette security → ℝ)
    (first second attached : Palette security) : ℝ :=
  ∑ root, source.weight root * tripleMassAt security (rootShift root) (scalar root) (score root) first second attached

/-- The same scalar can be one coordinate of an arbitrarily correlated
root record. The root weight stays inside the single joint input norm. -/
theorem jointTriple_degree_energy {Root : Type*} [Fintype Root]
    (security : ℕ) (source : FiniteDist Root) (rootShift : Root → ℤ) (scalar : Root → Scalar security)
    (score : Root → Palette security → ℝ) (degree : ℕ) :
    BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 3 => uniformReference security)
      (PhysicalBlockTensors.tripleMass (jointTripleMass security source rootShift scalar score)) degree) ≤
        (32 * pairBudget security) * source.expectation (fun root =>
          (primaryLaw security).expectation (fun primary => score root primary ^ 2)) := by
  have hprojection := PhysicalBlockTensors.triple_degree_energy_le (uniformReference security)
    (fun color => by rw [uniformReference_weight]; exact one_div_pos.mpr (FirstResponse.modulus_pos security))
    (jointTripleMass security source rootShift scalar score) degree
  have havg := tripleEnergy_average_le source (uniformReference security).weight
    (uniformReference security).nonneg (fun root => tripleMassAt security (rootShift root) (scalar root) (score root))
  have hbound : (∑ root, source.weight root * BlockDensity.tripleEnergy
      (uniformReference security).weight (uniformReference security).weight (uniformReference security).weight
      (tripleMassAt security (rootShift root) (scalar root) (score root))) ≤
        (4 * pairBudget security) * source.expectation (fun root =>
          (primaryLaw security).expectation (fun primary => score root primary ^ 2)) := by
    calc
      _ ≤ ∑ root, source.weight root * ((4 * pairBudget security) *
          (primaryLaw security).expectation (fun primary => score root primary ^ 2)) :=
        Finset.sum_le_sum (fun root _ => mul_le_mul_of_nonneg_left
          (tripleMassAt_energy security (rootShift root) (scalar root) (score root)) (source.nonneg root))
      _ = _ := by
        change (∑ root, source.weight root * ((4 * pairBudget security) *
          (primaryLaw security).expectation (fun primary => score root primary ^ 2))) =
            (4 * pairBudget security) * ∑ root, source.weight root *
              (primaryLaw security).expectation (fun primary => score root primary ^ 2)
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro root _
        ring
  exact hprojection.trans ((mul_le_mul_of_nonneg_left (havg.trans hbound)
    (by norm_num : (0 : ℝ) ≤ 8)).trans_eq (by ring))

/-- Finite Hilbert-valued retained coordinates are summed with their
actual reference weights. The kernel may jointly depend on every root,
retained coordinate, and primary input. -/
theorem joint_retained_triple_degree_energy {Root Retained : Type*} [Fintype Root] [Fintype Retained]
    (security : ℕ) (source : FiniteDist Root) (retained : FiniteDist Retained)
    (rootShift : Root → ℤ) (scalar : Root → Scalar security)
    (score : Root → Retained → Palette security → ℝ) (degree : ℕ) :
    (∑ coordinate, retained.weight coordinate *
      BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 3 => uniformReference security)
        (PhysicalBlockTensors.tripleMass
          (jointTripleMass security source rootShift scalar (fun root => score root coordinate))) degree)) ≤
        (32 * pairBudget security) * source.expectation (fun root => retained.expectation (fun coordinate =>
          (primaryLaw security).expectation (fun primary => score root coordinate primary ^ 2))) := by
  calc
    _ ≤ ∑ coordinate, retained.weight coordinate * ((32 * pairBudget security) *
        source.expectation (fun root => (primaryLaw security).expectation (fun primary => score root coordinate primary ^ 2))) :=
      Finset.sum_le_sum (fun coordinate _ => mul_le_mul_of_nonneg_left
        (jointTriple_degree_energy security source rootShift scalar (fun root => score root coordinate) degree)
        (retained.nonneg coordinate))
    _ = _ := by
      simp only [FiniteDist.expectation, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro root _
      apply Finset.sum_congr rfl
      intro coordinate _
      apply Finset.sum_congr rfl
      intro primary _
      ring

theorem activated_primaryMaximum (security : ℕ) :
    activation security ^ 2 * (Parameters.modulus security : ℝ) * primaryMaximum security ≤
      65537 * Real.exp Real.pi * (Parameters.base security : ℝ) ^ 31 := by
  have hq := FirstResponse.modulus_pos security
  have hb := FirstResponse.base_pos security
  have ha := activation_pos security
  have hl : (0 : ℝ) < Parameters.legCount security := by
    rw [Parameters.legCount_eq, Nat.cast_pow]
    exact pow_pos hb _
  have hcancel : activation security ^ 2 * (Parameters.modulus security : ℝ) * primaryMaximum security =
      activation security * ((Parameters.dimension security : ℝ) / Parameters.legCount security) := by
    unfold primaryMaximum markMass
    field_simp
  rw [hcancel]
  calc
    _ ≤ (Real.exp Real.pi / (2 * (Parameters.base security : ℝ))) *
        (131074 * (Parameters.base security : ℝ) ^ 32) :=
      mul_le_mul (GaussianHeights.activation_upper security) (GaussianHeights.dimension_leg_ratio security)
        (div_nonneg (Nat.cast_nonneg _) hl.le) (by positivity)
    _ = _ := by rw [pow_succ]; field_simp; ring

theorem modulus_anchor_ratio (security : ℕ) :
    (Parameters.modulus security : ℝ) / Parameters.anchorWidth security ≤
      131072 * (Parameters.base security : ℝ) ^ 16 := by
  have hwidth : (0 : ℝ) < Parameters.anchorWidth security := Nat.cast_pos.mpr (InwardAnchor.anchorWidth_pos security)
  apply (div_le_iff₀ hwidth).mpr
  have hq := Nat.cast_le (α := ℝ).mpr (Parameters.modulus_bounds security).2
  push_cast at hq
  convert hq using 1
  rw [anchorWidth_eq, Nat.cast_pow, mul_assoc, ← pow_add]

theorem pairBudget_polynomial (security : ℕ) :
    pairBudget security ≤ (524288 + 17180131328 * Real.exp Real.pi) * (Parameters.base security : ℝ) ^ 47 := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by exact_mod_cast (Parameters.base_ge_two security).trans' (by norm_num : 1 ≤ 2)
  have hratio := modulus_anchor_ratio security
  have hmax := activated_primaryMaximum security
  have hnonneg : 0 ≤ activation security ^ 2 * (Parameters.modulus security : ℝ) * primaryMaximum security := by
    apply mul_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
    exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg (markMass_pos security).le (Nat.cast_nonneg _))
  have hproduct := mul_le_mul hratio hmax hnonneg (by positivity : (0 : ℝ) ≤ 131072 * (Parameters.base security : ℝ) ^ 16)
  have hpower : (Parameters.base security : ℝ) ^ 16 ≤ (Parameters.base security : ℝ) ^ 47 :=
    pow_le_pow_right₀ hb1 (by omega)
  have hidentity : pairBudget security =
      4 * ((Parameters.modulus security : ℝ) / Parameters.anchorWidth security) +
        2 * (((Parameters.modulus security : ℝ) / Parameters.anchorWidth security) *
          (activation security ^ 2 * (Parameters.modulus security : ℝ) * primaryMaximum security)) := by
    unfold pairBudget
    ring
  rw [hidentity]
  have hpow : (Parameters.base security : ℝ) ^ 16 * (Parameters.base security : ℝ) ^ 31 =
      (Parameters.base security : ℝ) ^ 47 := by rw [← pow_add]
  calc
    _ ≤ 4 * (131072 * (Parameters.base security : ℝ) ^ 16) +
        2 * ((131072 * (Parameters.base security : ℝ) ^ 16) *
          (65537 * Real.exp Real.pi * (Parameters.base security : ℝ) ^ 31)) := by linarith only [hratio, hproduct]
    _ ≤ 4 * (131072 * (Parameters.base security : ℝ) ^ 47) +
        2 * ((131072 * (Parameters.base security : ℝ) ^ 16) *
          (65537 * Real.exp Real.pi * (Parameters.base security : ℝ) ^ 31)) := by linarith only [hpower]
    _ = _ := by
      have hproductIdentity : (131072 * (Parameters.base security : ℝ) ^ 16) *
        (65537 * Real.exp Real.pi * (Parameters.base security : ℝ) ^ 31) =
        (131072 * 65537 * Real.exp Real.pi) * ((Parameters.base security : ℝ) ^ 16 * (Parameters.base security : ℝ) ^ 31) := by ring
      rw [hproductIdentity, hpow]
      ring

end

end CurrentAFT.LocalReferenceEnergy
