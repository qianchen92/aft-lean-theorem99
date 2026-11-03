import AFT.BoundarySpike
import AFT.TrimmedPalette
import AFT.PrimaryCalibrationParameters

/-!
# Actual protected-input charts at the V7 parameter sizes
-/

namespace AFT.BoundaryCalibration

open Filter
open scoped BigOperators Classical Topology

noncomputable section

def protectedInputs (cutoff modulus : ℕ) :
    (GaussianSource.Window cutoff × GaussianSource.Window cutoff) → ZMod modulus × ZMod modulus :=
  fun input => ((input.1 : ℤ), (input.2 : ℤ))

theorem window_cast_injective (cutoff modulus : ℕ) (hsize : 2 * cutoff < modulus) :
    Function.Injective (fun value : GaussianSource.Window cutoff => ((value : ℤ) : ZMod modulus)) := by
  intro a b hab
  have hd : (modulus : ℤ) ∣ (b : ℤ) - (a : ℤ) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hab
  obtain ⟨ha0, ha1⟩ := Finset.mem_Icc.mp a.property
  obtain ⟨hb0, hb1⟩ := Finset.mem_Icc.mp b.property
  have hdiff : |(b : ℤ) - (a : ℤ)| < (modulus : ℤ) := by
    rw [abs_lt]
    constructor <;> omega
  have habs : ((b : ℤ) - (a : ℤ)).natAbs < (modulus : ℤ).natAbs := by
    rw [← Nat.cast_lt (α := ℤ), Int.natCast_natAbs, Int.natCast_natAbs]
    simpa only [Int.abs_natCast] using hdiff
  have hz := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd habs
  apply Subtype.ext
  omega

theorem protectedInputs_injective (cutoff modulus : ℕ) (hsize : 2 * cutoff < modulus) :
    Function.Injective (protectedInputs cutoff modulus) := by
  intro a b hab
  apply Prod.ext
  · exact window_cast_injective cutoff modulus hsize (congrArg Prod.fst hab)
  · exact window_cast_injective cutoff modulus hsize (congrArg Prod.snd hab)

theorem protectedInputs_card (cutoff : ℕ) :
    Fintype.card (GaussianSource.Window cutoff × GaussianSource.Window cutoff) = (2 * cutoff + 1) ^ 2 := by
  have hc : Fintype.card (GaussianSource.Window cutoff) = 2 * cutoff + 1 := by
    simp only [GaussianSource.Window, Fintype.card_coe, Int.card_Icc]
    omega
  rw [Fintype.card_prod, hc, pow_two]

def fieldPalette (modulus : ℕ) [NeZero modulus] (boundary shift : ℤ) : Finset (ZMod modulus) :=
  (TrimmedSlice.paletteSlice modulus boundary shift).map (ZMod.finEquiv modulus).toEquiv.toEmbedding

theorem fieldPalette_card (modulus : ℕ) [NeZero modulus] (boundary shift : ℤ) (hb : 0 ≤ boundary) :
    (fieldPalette modulus boundary shift).card = ((modulus : ℤ) - 2 * boundary - |shift|).toNat := by
  rw [fieldPalette, Finset.card_map, TrimmedSlice.paletteSlice_card modulus boundary shift hb]

def protectedPalettes (cutoff modulus : ℕ) [NeZero modulus] (boundary baseline : ℤ) :
    (GaussianSource.Window cutoff × GaussianSource.Window cutoff) → Finset (ZMod modulus) :=
  fun input => fieldPalette modulus boundary (baseline - (input.2 : ℤ))

theorem affineDeletionBudget_le {F I : Type*} [Fintype F] [Fintype I]
    (allowed : I → Finset F) (deleted : ℝ) (hcard : 0 < Fintype.card F)
    (hdeleted : ∀ i, (Fintype.card F : ℝ) - (allowed i).card ≤ deleted) :
    affineDeletionBudget allowed ≤
      (1 + (Fintype.card I : ℝ) * deleted) / (Fintype.card F : ℝ) := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast hcard
  have hsum : (∑ i : I, (1 - (allowed i).card / (Fintype.card F : ℝ))) ≤
      (Fintype.card I : ℝ) * (deleted / (Fintype.card F : ℝ)) := by
    calc
      _ ≤ ∑ _i : I, deleted / (Fintype.card F : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        rw [le_div_iff₀ hq]
        have hh := hdeleted i
        field_simp
        linarith
      _ = _ := by simp
  unfold affineDeletionBudget
  have heq : (1 + (Fintype.card I : ℝ) * deleted) / (Fintype.card F : ℝ) =
      (Fintype.card F : ℝ)⁻¹ + (Fintype.card I : ℝ) * (deleted / (Fintype.card F : ℝ)) := by ring
  rw [heq]
  exact add_le_add le_rfl hsum

theorem protectedPalette_budget (cutoff modulus : ℕ) [NeZero modulus]
    (boundary baseline shiftBound : ℤ) (hb : 0 ≤ boundary) (hs : |baseline| ≤ shiftBound)
    (hclear : 2 * boundary + shiftBound + cutoff < modulus) :
    affineDeletionBudget (protectedPalettes cutoff modulus boundary baseline) ≤
      (1 + ((2 * cutoff + 1 : ℕ) : ℝ) ^ 2 *
        (2 * (boundary : ℝ) + shiftBound + cutoff)) / modulus := by
  have hq : 0 < modulus := Nat.pos_of_ne_zero (NeZero.ne modulus)
  have hbound (input : GaussianSource.Window cutoff × GaussianSource.Window cutoff) :
      |baseline - (input.2 : ℤ)| ≤ shiftBound + cutoff := by
    have ha : |(input.2 : ℤ)| ≤ cutoff := abs_le.mpr (Finset.mem_Icc.mp input.2.property)
    exact (abs_sub _ _).trans (add_le_add hs ha)
  have hbudget := affineDeletionBudget_le
    (protectedPalettes cutoff modulus boundary baseline)
    (2 * (boundary : ℝ) + shiftBound + cutoff) (by simpa using hq)
    (by
      intro input
      rw [protectedPalettes, fieldPalette_card modulus boundary _ hb, ZMod.card]
      have hi : 0 ≤ (modulus : ℤ) - 2 * boundary - |baseline - (input.2 : ℤ)| := by
        have hh := hbound input
        omega
      have heq : (((modulus : ℤ) - 2 * boundary - |baseline - (input.2 : ℤ)|).toNat : ℤ) =
          (modulus : ℤ) - 2 * boundary - |baseline - (input.2 : ℤ)| := Int.toNat_of_nonneg hi
      have hh : (modulus : ℤ) - ((modulus : ℤ) - 2 * boundary - |baseline - (input.2 : ℤ)|).toNat ≤
          2 * boundary + shiftBound + cutoff := by rw [heq]; have := hbound input; omega
      exact_mod_cast hh)
  simpa only [ZMod.card, protectedInputs_card, Nat.cast_pow] using hbudget

end

end AFT.BoundaryCalibration

namespace AFT.BoundaryCalibration

open Filter
open scoped Topology

private theorem chartBudget_power_bound (x q k d a b : ℝ)
    (hx : 1 ≤ x) (hq : x ^ 40 ≤ q) (hk0 : 0 ≤ k) (hd0 : 0 ≤ d)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hk : k ≤ a * x ^ 3) (hd : d ≤ b * x ^ 32) :
    (2 * k + 1) * ((1 + k * d) / q) ≤ (2 * a + 1) * (1 + a * b) / x ^ 2 := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq
  have hfirst : 2 * k + 1 ≤ (2 * a + 1) * x ^ 3 := by
    nlinarith [one_le_pow₀ hx (n := 3)]
  have hsecond : 1 + k * d ≤ (1 + a * b) * x ^ 35 := by
    have hm := mul_le_mul hk hd hd0 (by positivity : 0 ≤ a * x ^ 3)
    have heq : (a * x ^ 3) * (b * x ^ 32) = a * b * x ^ 35 := by ring
    rw [heq] at hm
    nlinarith [one_le_pow₀ hx (n := 35)]
  calc
    _ ≤ ((2 * a + 1) * x ^ 3) * (((1 + a * b) * x ^ 35) / x ^ 40) := by
      exact mul_le_mul hfirst
        (div_le_div_of_nonneg_left (by positivity) (by positivity) hq |>.trans'
          (div_le_div_of_nonneg_right hsecond hq0.le))
        (by positivity) (by positivity)
    _ = _ := by field_simp

instance v7ModulusNeZero (parameter : ℕ) : NeZero (Parameters.modulus parameter) :=
  ⟨Nat.ne_of_gt (Parameters.modulus_prime parameter).pos⟩

instance v7ModulusPrime (parameter : ℕ) : Fact (Parameters.modulus parameter).Prime :=
  ⟨Parameters.modulus_prime parameter⟩

noncomputable def v7ProtectedPalettes (cutoffScale : ℝ) (parameter : ℕ) (boundary baseline : ℤ) :=
  protectedPalettes (GaussianSource.legCutoff cutoffScale parameter - 1)
    (Parameters.modulus parameter) boundary baseline

/-- The chart contraction condition follows from the actual V7 sizes,
uniformly over every legal boundary width and public baseline. -/
theorem v7_chart_budget_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) :
    ∀ᶠ parameter : ℕ in atTop, ∀ boundary baseline : ℤ,
      0 ≤ boundary → boundary ≤ Parameters.safeMargin parameter →
      |baseline| ≤ 3 * Parameters.anchorWidth parameter →
      (2 * Fintype.card (GaussianSource.Window (GaussianSource.legCutoff cutoffScale parameter - 1) ×
        GaussianSource.Window (GaussianSource.legCutoff cutoffScale parameter - 1)) + 1) *
        affineDeletionBudget (v7ProtectedPalettes cutoffScale parameter boundary baseline) ≤ 1 / 4 := by
  let a : ℝ := 4 * (cutoffScale + 1) ^ 2
  let b : ℝ := cutoffScale + 44
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hsmall := ((tendsto_const_div_pow ((2 * a + 1) * (1 + a * b)) 2 (by decide)).comp
    tendsto_natCast_atTop_atTop).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have hclear := v7_primaryCalibration_clearance_eventually cutoffScale hscale
    (fun parameter => Parameters.safeMargin parameter)
    (Filter.Eventually.of_forall fun parameter => ⟨by positivity, le_rfl⟩)
  filter_upwards [hsmall, hclear, eventually_ge_atTop 2] with parameter hsmall hclear hp
  intro boundary baseline hb0 hb1 hbase
  have hp1 : 1 ≤ parameter := by omega
  have hx : (1 : ℝ) ≤ parameter := by exact_mod_cast hp1
  have hc := GaussianSource.legCutoff_positive cutoffScale parameter hscale hp1
  have hcard : (Fintype.card
      (GaussianSource.Window (GaussianSource.legCutoff cutoffScale parameter - 1) ×
        GaussianSource.Window (GaussianSource.legCutoff cutoffScale parameter - 1)) : ℝ) ≤
        a * (parameter : ℝ) ^ 3 := by
    rw [protectedInputs_card]
    have heq : 2 * (GaussianSource.legCutoff cutoffScale parameter - 1) + 1 =
        2 * GaussianSource.legCutoff cutoffScale parameter - 1 := by omega
    rw [heq]
    have hh := GaussianSource.legFeatureCount_upper cutoffScale parameter hscale hp1
    have hpowers : (parameter : ℝ) ^ (9 / 4 : ℝ) ≤ (parameter : ℝ) ^ 3 := by
      simpa only [Real.rpow_natCast] using
        Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (9 / 4 : ℝ) ≤ (3 : ℕ))
    exact hh.trans (mul_le_mul_of_nonneg_left hpowers ha)
  have hcutoff := GaussianSource.legCutoff_le_quadratic cutoffScale parameter hscale hp1
  have hboundary : (boundary : ℝ) ≤ 20 * (parameter : ℝ) ^ 2 := by
    have hh := hb1
    simpa only [Parameters.safeMargin, Parameters.security_eq parameter hp, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_pow] using (show (boundary : ℝ) ≤ Parameters.safeMargin parameter by exact_mod_cast hh)
  have hpow : (parameter : ℝ) ^ 2 ≤ (parameter : ℝ) ^ 32 := pow_le_pow_right₀ hx (by decide)
  have hdeleted : 2 * (boundary : ℝ) + 3 * (Parameters.anchorWidth parameter : ℝ) +
      (GaussianSource.legCutoff cutoffScale parameter - 1 : ℕ) ≤ b * (parameter : ℝ) ^ 32 := by
    have hcc : ((GaussianSource.legCutoff cutoffScale parameter - 1 : ℕ) : ℝ) ≤
        GaussianSource.legCutoff cutoffScale parameter := by exact_mod_cast Nat.sub_le _ _
    simp only [Parameters.anchorWidth, Parameters.security_eq parameter hp, Nat.cast_pow]
    dsimp [b]
    have hm := mul_le_mul_of_nonneg_left hpow (show 0 ≤ cutoffScale + 41 by linarith)
    nlinarith
  have hq : (parameter : ℝ) ^ 40 ≤ Parameters.modulus parameter := by
    exact_mod_cast (show parameter ^ 40 ≤ Parameters.modulus parameter by
      simpa only [Parameters.security_eq parameter hp] using (Parameters.modulus_bounds parameter).1)
  have hclear' : 2 * boundary + 3 * (Parameters.anchorWidth parameter : ℤ) +
      (GaussianSource.legCutoff cutoffScale parameter - 1 : ℕ) < Parameters.modulus parameter := by
    have hqpos := (Parameters.modulus_prime parameter).pos
    omega
  have hbudget := protectedPalette_budget (GaussianSource.legCutoff cutoffScale parameter - 1)
    (Parameters.modulus parameter) boundary baseline (3 * Parameters.anchorWidth parameter) hb0 hbase hclear'
  have hstep := mul_le_mul_of_nonneg_left hbudget
    (by positivity : 0 ≤ 2 * (Fintype.card
      (GaussianSource.Window (GaussianSource.legCutoff cutoffScale parameter - 1) ×
        GaussianSource.Window (GaussianSource.legCutoff cutoffScale parameter - 1)) : ℝ) + 1)
  have hh := chartBudget_power_bound (parameter : ℝ) (Parameters.modulus parameter)
    (Fintype.card (GaussianSource.Window (GaussianSource.legCutoff cutoffScale parameter - 1) ×
      GaussianSource.Window (GaussianSource.legCutoff cutoffScale parameter - 1)))
    (2 * (boundary : ℝ) + 3 * (Parameters.anchorWidth parameter : ℝ) +
      (GaussianSource.legCutoff cutoffScale parameter - 1 : ℕ)) a b hx hq (by positivity)
    (by
      have : (0 : ℝ) ≤ boundary := by exact_mod_cast hb0
      positivity) ha hb hcard hdeleted
  simp only [protectedInputs_card, Nat.cast_pow, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] at hstep hh ⊢
  exact (hstep.trans hh).trans hsmall.le

end AFT.BoundaryCalibration

namespace AFT.BoundaryCalibration

open Filter
open scoped Topology

noncomputable local instance (parameter : ℕ) : DecidableEq (ZMod (Parameters.modulus parameter)) := Classical.decEq _

/-- The protected input alphabet uses the paper's strict integer cutoff. -/
abbrev V7Input (cutoffScale : ℝ) (parameter : ℕ) :=
  GaussianSource.Window (GaussianSource.legCutoff cutoffScale parameter - 1) ×
    GaussianSource.Window (GaussianSource.legCutoff cutoffScale parameter - 1)

/-- This predicate records the actual finite chart laws and their joint
support and marginal identities, including the separate public branch flag. -/
def V7ChartExists (cutoffScale : ℝ) (parameter : ℕ) (boundary baseline : ℤ)
    (mark : ZMod (Parameters.modulus parameter)) : Prop :=
  let inputs := protectedInputs (GaussianSource.legCutoff cutoffScale parameter - 1)
    (Parameters.modulus parameter)
  let allowed := v7ProtectedPalettes cutoffScale parameter boundary baseline
  let zero : V7Input cutoffScale parameter :=
    (GaussianSource.windowZero _, GaussianSource.windowZero _)
  let atom := chartAtom (V7Input cutoffScale parameter)
  ∃ interior spike law : FiniteDist (Chart (ZMod (Parameters.modulus parameter))),
    (∀ chart, law.weight chart = (1 - atom) * interior.weight chart + atom * spike.weight chart) ∧
    (∀ chart, ¬ (chart.2.1 ≠ 0 ∧
      ∀ i, feature (inputs i).1 (inputs i).2 chart ∈ allowed i) → interior.weight chart = 0) ∧
    (∀ chart, ¬ (feature (inputs zero).1 (inputs zero).2 chart = mark ∧ chart.2.1 ≠ 0 ∧
      ∀ i, i ≠ zero → feature (inputs i).1 (inputs i).2 chart ∈ allowed i) → spike.weight chart = 0) ∧
    (∀ c, (law.map (feature (inputs zero).1 (inputs zero).2)).weight c =
      (1 - atom) * (if c ∈ allowed zero then ((allowed zero).card : ℝ)⁻¹ else 0) +
        atom * (if c = mark then 1 else 0)) ∧
    (∀ i, i ≠ zero → ∀ c, (law.map (feature (inputs i).1 (inputs i).2)).weight c =
      if c ∈ allowed i then ((allowed i).card : ℝ)⁻¹ else 0)

/-- V7's actual parameters supply the marked affine chart at every legal
boundary and baseline. No deletion-budget or input-injectivity premise remains. -/
theorem v7_marked_chart_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) :
    ∀ᶠ parameter : ℕ in atTop, ∀ boundary baseline : ℤ,
      0 ≤ boundary → boundary ≤ Parameters.safeMargin parameter →
      |baseline| ≤ 3 * Parameters.anchorWidth parameter →
      ∀ mark : ZMod (Parameters.modulus parameter),
        V7ChartExists cutoffScale parameter boundary baseline mark := by
  have hclear := v7_primaryCalibration_clearance_eventually cutoffScale hscale
    (fun parameter => Parameters.safeMargin parameter)
    (Filter.Eventually.of_forall fun parameter => ⟨by positivity, le_rfl⟩)
  filter_upwards [v7_chart_budget_eventually cutoffScale hscale, hclear,
    eventually_ge_atTop 1] with parameter hbudget hclear hp
  intro boundary baseline hb0 hb1 hbase mark
  have hq := (Parameters.modulus_prime parameter).pos
  have hc := GaussianSource.legCutoff_positive cutoffScale parameter hscale hp
  have hinj := protectedInputs_injective (GaussianSource.legCutoff cutoffScale parameter - 1)
    (Parameters.modulus parameter) (by omega)
  let zero : V7Input cutoffScale parameter :=
    (GaussianSource.windowZero _, GaussianSource.windowZero _)
  have hatom := chartAtom_bounds zero
  simpa only [V7ChartExists, zero] using
    (affine_marked_chart _ hinj _ zero mark (hbudget boundary baseline hb0 hb1 hbase)
      _ hatom.1 hatom.2.1 hatom.2.2)

end AFT.BoundaryCalibration
