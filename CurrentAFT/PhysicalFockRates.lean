import CurrentAFT.ActualBlockFock

/-! # Actual public parameter budgets for the complete physical Fock norm -/

namespace CurrentAFT.PhysicalFockRates

open AFT ProposalPrimary ActualBlockFock BackgroundRates UniformBodyProfiles
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount Parameters.dimension
  BackgroundRates.radius UniformBodyProfiles.deviation

def normalizedScale (security : ℕ) (multiple : ℝ) : ℝ :=
  multiple * radius security / Real.sqrt (Parameters.dimension security : ℝ)

private theorem subtype_sum_le {Index : Type*} [Fintype Index] (selected : Finset Index)
    [Fintype selected] (value : Index → ℝ) (hvalue : ∀ index, 0 ≤ value index) :
    (∑ index : selected, value index.val) ≤ ∑ index : Index, value index := by
  rw [← Finset.sum_subtype selected (fun _ => Iff.rfl) value]
  exact Finset.sum_le_univ_sum_of_nonneg hvalue

def linearEnvelope (security : ℕ) (multiple : ℝ) : ℝ :=
  normalizedScale security multiple ^ 2 *
    ((Parameters.legCount security : ℝ) * firstConstant * (Parameters.base security : ℝ) ^ 31 +
      2 * (Parameters.bodySize security : ℝ) * deviation security ^ 2)

def nonlinearEnvelope (security : ℕ) (multiple : ℝ) : ℝ :=
  128 * (Parameters.legCount security : ℝ) *
    (normalizedScale security multiple ^ 2 +
      Real.sqrt (Parameters.dimension security : ℝ) * normalizedScale security multiple ^ 3) *
    (higherConstant * (Parameters.base security : ℝ) ^ 24)

theorem dimension_pos (security : ℕ) : (0 : ℝ) < Parameters.dimension security := by
  have h := (Parameters.dimension_bounds security).1
  have hb := Parameters.base_pos security
  exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < 65536 * Parameters.base security ^ 160) h)

theorem dimension_lower (security : ℕ) :
    (Parameters.base security : ℝ) ^ 160 ≤ Parameters.dimension security := by
  have h := Nat.cast_le (α := ℝ).mpr (Parameters.dimension_bounds security).1
  push_cast at h
  nlinarith [pow_nonneg (FirstResponse.base_pos security).le 160]

theorem radius_nonneg (security : ℕ) : 0 ≤ radius security := by
  unfold radius
  exact Real.rpow_nonneg (FirstResponse.base_pos security).le _

/-- The half-power saved by the sharp first coefficient is preserved. -/
theorem radius_square (security : ℕ) : radius security ^ 2 = Real.sqrt (Parameters.base security : ℝ) := by
  unfold radius
  rw [← Real.rpow_natCast, ← Real.rpow_mul (FirstResponse.base_pos security).le, Real.sqrt_eq_rpow]
  norm_num

theorem normalizedScale_nonneg (security : ℕ) (multiple : ℝ) (hmultiple : 0 ≤ multiple) :
    0 ≤ normalizedScale security multiple := by
  exact div_nonneg (mul_nonneg hmultiple (radius_nonneg security)) (Real.sqrt_nonneg _)

theorem normalizedScale_le (security : ℕ) (multiple : ℝ) (hmultiple : 0 ≤ multiple) :
    normalizedScale security multiple ≤ multiple / (Parameters.base security : ℝ) ^ 79 := by
  have hb := FirstResponse.base_pos security
  have hroot : (Parameters.base security : ℝ) ^ 80 ≤ Real.sqrt (Parameters.dimension security : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith only [dimension_lower security]
  calc
    _ ≤ multiple * (Parameters.base security : ℝ) / Real.sqrt (Parameters.dimension security : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (radius_le_base security) hmultiple) (Real.sqrt_nonneg _)
    _ ≤ multiple * (Parameters.base security : ℝ) / (Parameters.base security : ℝ) ^ 80 :=
      div_le_div_of_nonneg_left (mul_nonneg hmultiple hb.le) (pow_pos hb _) hroot
    _ = _ := by field_simp

theorem primary_first_scale_le (security : ℕ) (multiple : ℝ) :
    (Parameters.legCount security : ℝ) * normalizedScale security multiple ^ 2 *
      (Parameters.base security : ℝ) ^ 31 ≤ multiple ^ 2 := by
  have hb := FirstResponse.base_pos security
  have hd := dimension_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (Parameters.base_ge_two security).trans' (by norm_num : 1 ≤ 2)
  have hratio : (Parameters.base security : ℝ) ^ 159 / Parameters.dimension security ≤
      1 / (Parameters.base security : ℝ) := by
    apply (div_le_div_of_nonneg_left (pow_nonneg hb.le _) (pow_pos hb _) (dimension_lower security)).trans_eq
    field_simp
  have hR : radius security ^ 2 ≤ Parameters.base security := by
    rw [radius_square]
    apply Real.sqrt_le_iff.mpr
    exact ⟨hb.le, by nlinarith⟩
  calc
    _ = (multiple ^ 2 * radius security ^ 2) *
        ((Parameters.base security : ℝ) ^ 159 / Parameters.dimension security) := by
      rw [normalizedScale, div_pow, Real.sq_sqrt hd.le, Parameters.legCount_eq, Nat.cast_pow]
      ring
    _ ≤ (multiple ^ 2 * (Parameters.base security : ℝ)) * (1 / (Parameters.base security : ℝ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hR (sq_nonneg _)) hratio
        (div_nonneg (pow_nonneg hb.le _) hd.le) (by positivity)
    _ = _ := by field_simp

theorem primary_higher_scale_le (security : ℕ) (multiple : ℝ) (hmultiple : 0 ≤ multiple) :
    (Parameters.legCount security : ℝ) * normalizedScale security multiple ^ 4 *
      (Parameters.base security : ℝ) ^ 47 ≤ multiple ^ 4 := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (Parameters.base_ge_two security).trans' (by norm_num : 1 ≤ 2)
  have hscale4 := pow_le_pow_left₀ (normalizedScale_nonneg security multiple hmultiple)
    (normalizedScale_le security multiple hmultiple) 4
  calc
    _ ≤ (Parameters.legCount security : ℝ) * (multiple / (Parameters.base security : ℝ) ^ 79) ^ 4 *
        (Parameters.base security : ℝ) ^ 47 := by gcongr
    _ = multiple ^ 4 / (Parameters.base security : ℝ) ^ 141 := by
      rw [Parameters.legCount_eq, Nat.cast_pow]
      field_simp
    _ ≤ multiple ^ 4 := (div_le_self (by positivity) (one_le_pow₀ hb1))

theorem normalizedScale_le_one_eventually (multiple : ℝ) (hmultiple : 0 ≤ multiple) :
    ∃ threshold : ℕ, ∀ security ≥ threshold, normalizedScale security multiple ≤ 1 := by
  refine ⟨Nat.ceil multiple + 1, ?_⟩
  intro security hsecurity
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (Parameters.base_ge_two security).trans' (by norm_num : 1 ≤ 2)
  have hlarge : multiple ≤ (Parameters.base security : ℝ) := by
    have hn : Nat.ceil multiple ≤ Parameters.base security := by rw [Parameters.base]; omega
    exact (Nat.le_ceil multiple).trans (by exact_mod_cast hn)
  apply (normalizedScale_le security multiple hmultiple).trans
  apply (div_le_one (pow_pos hb 79)).mpr
  exact hlarge.trans (le_self_pow₀ hb1 (by decide))

theorem normalizedScale_bodyFactor_le (security : ℕ) (multiple : ℝ) (hmultiple : 0 ≤ multiple) :
    normalizedScale security multiple ^ 2 ≤ multiple ^ 2 * BackgroundRates.bodyFactor security ^ 2 := by
  have hpool : ordinaryPool security ≤ Parameters.dimension security := by
    unfold ordinaryPool
    have := ActualCycleMeanMGF.bodySize_le_dimension security
    omega
  have hroot : Real.sqrt (ordinaryPool security : ℝ) ≤ Real.sqrt (Parameters.dimension security : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hpool)
  have hrootpos := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (ordinaryPool_pos security) : (0 : ℝ) < ordinaryPool security)
  have hscale : normalizedScale security multiple ≤ multiple * bodyFactor security := by
    calc
      _ ≤ multiple * radius security / Real.sqrt (ordinaryPool security : ℝ) :=
        div_le_div_of_nonneg_left (mul_nonneg hmultiple (radius_nonneg security)) hrootpos hroot
      _ = _ := by unfold bodyFactor; ring
  exact (pow_le_pow_left₀ (normalizedScale_nonneg security multiple hmultiple) hscale 2).trans_eq (by ring)

theorem primaryFactor_square (security : ℕ) :
    primaryFactor security ^ 2 = 1 / (Parameters.legCount security : ℝ) := by
  unfold primaryFactor
  rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  simp only [one_div]

theorem linearEnvelope_le (security : ℕ) (multiple : ℝ) :
    linearEnvelope security multiple ≤
      multiple ^ 2 * (firstConstant + 33282) / Real.sqrt (Parameters.base security : ℝ) := by
  have hb := FirstResponse.base_pos security
  have hd := dimension_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (Parameters.base_ge_two security).trans' (by norm_num : 1 ≤ 2)
  have hlegs : (Parameters.legCount security : ℝ) = (Parameters.base security : ℝ) ^ 128 := by
    rw [Parameters.legCount_eq, Nat.cast_pow]
  have hratio : (Parameters.base security : ℝ) ^ 159 / Parameters.dimension security ≤
      1 / (Parameters.base security : ℝ) := by
    apply (div_le_div_of_nonneg_left (pow_nonneg hb.le _) (pow_pos hb _) (dimension_lower security)).trans_eq
    field_simp
  have hprimary : normalizedScale security multiple ^ 2 *
      ((Parameters.legCount security : ℝ) * firstConstant * (Parameters.base security : ℝ) ^ 31) ≤
      multiple ^ 2 * firstConstant / Real.sqrt (Parameters.base security : ℝ) := by
    calc
      _ = (multiple ^ 2 * firstConstant * radius security ^ 2) *
          ((Parameters.base security : ℝ) ^ 159 / Parameters.dimension security) := by
        rw [normalizedScale, div_pow, Real.sq_sqrt hd.le, hlegs]
        ring
      _ ≤ (multiple ^ 2 * firstConstant * radius security ^ 2) *
          (1 / (Parameters.base security : ℝ)) :=
        mul_le_mul_of_nonneg_left hratio (mul_nonneg (mul_nonneg (sq_nonneg _) firstConstant_nonneg) (sq_nonneg _))
      _ = _ := by
        rw [radius_square]
        field_simp
        rw [Real.sq_sqrt hb.le]
  have hbodyRatio : (Parameters.bodySize security : ℝ) / Parameters.dimension security ≤ 1 := by
    apply (div_le_one hd).mpr
    exact_mod_cast ActualCycleMeanMGF.bodySize_le_dimension security
  have hbody : normalizedScale security multiple ^ 2 *
      (2 * (Parameters.bodySize security : ℝ) * deviation security ^ 2) ≤
      33282 * multiple ^ 2 / (Parameters.base security : ℝ) ^ 60 := by
    calc
      _ = (2 * (multiple ^ 2 * radius security ^ 2 * deviation security ^ 2)) *
          ((Parameters.bodySize security : ℝ) / Parameters.dimension security) := by
        rw [normalizedScale, div_pow, Real.sq_sqrt hd.le]
        ring
      _ ≤ 2 * (multiple ^ 2 * radius security ^ 2 * deviation security ^ 2) :=
        (mul_le_mul_of_nonneg_left hbodyRatio (by positivity)).trans_eq (by ring)
      _ ≤ _ := (mul_le_mul_of_nonneg_left
        (ActualCycleMeanMGF.radius_deviation_budget security (multiple ^ 2) (sq_nonneg _))
        (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)
  have hroot : Real.sqrt (Parameters.base security : ℝ) ≤ (Parameters.base security : ℝ) ^ 60 := by
    have hsqrt : Real.sqrt (Parameters.base security : ℝ) ≤ Parameters.base security := by
      apply Real.sqrt_le_iff.mpr
      exact ⟨hb.le, by nlinarith⟩
    exact hsqrt.trans (le_self_pow₀ hb1 (by decide))
  have hbody' : normalizedScale security multiple ^ 2 *
      (2 * (Parameters.bodySize security : ℝ) * deviation security ^ 2) ≤
      33282 * multiple ^ 2 / Real.sqrt (Parameters.base security : ℝ) :=
    hbody.trans (div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr hb) hroot)
  unfold linearEnvelope
  rw [mul_add]
  exact (add_le_add hprimary hbody').trans_eq (by ring)

theorem nonlinearEnvelope_le (security : ℕ) (multiple : ℝ) (hmultiple : 0 ≤ multiple) :
    nonlinearEnvelope security multiple ≤
      (128 * higherConstant * (multiple ^ 2 + multiple ^ 3)) / (Parameters.base security : ℝ) := by
  have hb := FirstResponse.base_pos security
  have hd := dimension_pos security
  have hsqrt := Real.sqrt_pos.mpr hd
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (Parameters.base_ge_two security).trans' (by norm_num : 1 ≤ 2)
  have hlegs : (Parameters.legCount security : ℝ) = (Parameters.base security : ℝ) ^ 128 := by
    rw [Parameters.legCount_eq, Nat.cast_pow]
  have hratio : (Parameters.base security : ℝ) ^ 152 / Parameters.dimension security ≤
      1 / (Parameters.base security : ℝ) ^ 8 := by
    apply (div_le_div_of_nonneg_left (pow_nonneg hb.le _) (pow_pos hb _) (dimension_lower security)).trans_eq
    field_simp
  have hr2 := pow_le_pow_left₀ (radius_nonneg security) (radius_le_base security) 2
  have hr3 := pow_le_pow_left₀ (radius_nonneg security) (radius_le_base security) 3
  have hquadratic : (Parameters.legCount security : ℝ) * normalizedScale security multiple ^ 2 *
      (Parameters.base security : ℝ) ^ 24 ≤ multiple ^ 2 / (Parameters.base security : ℝ) ^ 6 := by
    calc
      _ = (multiple ^ 2 * radius security ^ 2) *
          ((Parameters.base security : ℝ) ^ 152 / Parameters.dimension security) := by
        rw [normalizedScale, div_pow, Real.sq_sqrt hd.le, hlegs]
        ring
      _ ≤ (multiple ^ 2 * (Parameters.base security : ℝ) ^ 2) *
          (1 / (Parameters.base security : ℝ) ^ 8) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hr2 (sq_nonneg _)) hratio
          (div_nonneg (pow_nonneg hb.le _) hd.le) (by positivity)
      _ = _ := by field_simp
  have hcubic : (Parameters.legCount security : ℝ) * Real.sqrt (Parameters.dimension security : ℝ) *
      normalizedScale security multiple ^ 3 * (Parameters.base security : ℝ) ^ 24 ≤
      multiple ^ 3 / (Parameters.base security : ℝ) ^ 5 := by
    calc
      _ = (multiple ^ 3 * radius security ^ 3) *
          ((Parameters.base security : ℝ) ^ 152 / Parameters.dimension security) := by
        rw [normalizedScale, div_pow, hlegs]
        field_simp
        rw [Real.sq_sqrt hd.le]
        ring
      _ ≤ (multiple ^ 3 * (Parameters.base security : ℝ) ^ 3) *
          (1 / (Parameters.base security : ℝ) ^ 8) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hr3 (pow_nonneg hmultiple _)) hratio
          (div_nonneg (pow_nonneg hb.le _) hd.le) (by positivity)
      _ = _ := by field_simp
  have hbase6 : (Parameters.base security : ℝ) ≤ (Parameters.base security : ℝ) ^ 6 := le_self_pow₀ hb1 (by decide)
  have hbase5 : (Parameters.base security : ℝ) ≤ (Parameters.base security : ℝ) ^ 5 := le_self_pow₀ hb1 (by decide)
  have hc0 : 0 ≤ higherConstant := le_trans (by norm_num) higherConstant_one_le
  calc
    _ = 128 * higherConstant *
        (((Parameters.legCount security : ℝ) * normalizedScale security multiple ^ 2 *
          (Parameters.base security : ℝ) ^ 24) +
        ((Parameters.legCount security : ℝ) * Real.sqrt (Parameters.dimension security : ℝ) *
          normalizedScale security multiple ^ 3 * (Parameters.base security : ℝ) ^ 24)) := by
      unfold nonlinearEnvelope
      ring
    _ ≤ 128 * higherConstant *
        (multiple ^ 2 / (Parameters.base security : ℝ) ^ 6 + multiple ^ 3 / (Parameters.base security : ℝ) ^ 5) :=
      mul_le_mul_of_nonneg_left (add_le_add hquadratic hcubic) (by positivity)
    _ ≤ 128 * higherConstant *
        (multiple ^ 2 / (Parameters.base security : ℝ) + multiple ^ 3 / (Parameters.base security : ℝ)) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (div_le_div_of_nonneg_left (sq_nonneg _) hb hbase6)
        (div_le_div_of_nonneg_left (pow_nonneg hmultiple _) hb hbase5)) (by positivity)
    _ = _ := by ring

/-- Both complete-product local conditions hold uniformly in all fixed
roots and queue values at any fixed multiple of the analysis radius. -/
theorem envelopes_eventually (multiple : ℝ) (hmultiple : 0 ≤ multiple) :
    ∃ threshold : ℕ, ∀ security ≥ threshold,
      linearEnvelope security multiple ≤ 1 / 8 ∧ nonlinearEnvelope security multiple ≤ 1 / 2 := by
  let linearSize := 8 * (firstConstant + 33282) * multiple ^ 2
  let nonlinearSize := 256 * higherConstant * (multiple ^ 2 + multiple ^ 3)
  have hlinear0 : 0 ≤ linearSize := by dsimp [linearSize]; have := firstConstant_nonneg; positivity
  have hnonlinear0 : 0 ≤ nonlinearSize := by
    dsimp [nonlinearSize]
    have := higherConstant_one_le
    positivity
  refine ⟨Nat.ceil (linearSize ^ 2 + nonlinearSize) + 1, ?_⟩
  intro security hsecurity
  have hb := FirstResponse.base_pos security
  have hbase : linearSize ^ 2 + nonlinearSize ≤ (Parameters.base security : ℝ) := by
    have hceil := Nat.le_ceil (linearSize ^ 2 + nonlinearSize)
    have hn : Nat.ceil (linearSize ^ 2 + nonlinearSize) ≤ Parameters.base security := by
      have hs : security ≤ Parameters.base security := by rw [Parameters.base]; omega
      omega
    exact hceil.trans (by exact_mod_cast hn)
  have hroot : linearSize ≤ Real.sqrt (Parameters.base security : ℝ) :=
    Real.le_sqrt_of_sq_le (by linarith)
  constructor
  · apply (linearEnvelope_le security multiple).trans
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hb)).mpr
    dsimp [linearSize] at hroot
    nlinarith
  · apply (nonlinearEnvelope_le security multiple hmultiple).trans
    apply (div_le_iff₀ hb).mpr
    dsimp [nonlinearSize] at hbase
    nlinarith [sq_nonneg linearSize]

theorem blockCount_le_dimension (security : ℕ) :
    Fintype.card (BlockIndex security) ≤ Parameters.dimension security := by
  have hroom := population_room security
  simp only [BlockIndex, Fintype.card_sum, Fintype.card_fin]
  unfold centerCount
  rw [Parameters.dimension]
  omega

/-- The complete, all-degree physical product satisfies its Gaussian Fock
bound after the actual local conditions have been discharged. Only its
actual aggregate first coefficient remains in the exponential. -/
theorem current_product_fock_eventually (multiple : ℝ) (hmultiple : 0 ≤ multiple) :
    ∃ threshold : ℕ, ∀ security ≥ threshold,
      ∀ ar : Fin (Parameters.legCount security) → ℤ,
      ∀ cr : Fin (centerCount security) → ℤ,
      ∀ qr : Fin (Parameters.modulus security) → ℤ, ∀ queue : ℤ,
      productFockEnergy (Slots security) (LocalReferenceEnergy.uniformReference security)
        (blockLawAt security ar cr qr queue) (multiple * radius security) ≤
        16 * Real.exp (8 * ∑ color, (∑ index, BlockProducts.normalizedLinear
          (Slots security) (LocalReferenceEnergy.uniformReference security)
          (blockLawAt security ar cr qr queue) (normalizedScale security multiple) index color) ^ 2) := by
  obtain ⟨threshold, hthreshold⟩ := envelopes_eventually multiple hmultiple
  refine ⟨threshold, ?_⟩
  intro security hsecurity ar cr qr queue
  obtain ⟨hlinear, hnonlinear⟩ := hthreshold security hsecurity
  have h := productFockEnergy_le (Slots security) (LocalReferenceEnergy.uniformReference security)
    (blockLawAt security ar cr qr queue) (slots_card_le_three security)
    (Parameters.dimension security) (multiple * radius security)
    ((Finset.card_le_univ _).trans (blockCount_le_dimension security))
    (by
      rw [physical_card]
      exact (linearActivity_le security ar cr qr (normalizedScale security multiple) queue).trans hlinear)
    (by
      rw [physical_card]
      exact (nonlinearActivity_le security ar cr qr queue (normalizedScale security multiple)
        (normalizedScale_nonneg security multiple hmultiple) (Parameters.dimension security)).trans hnonlinear)
  simpa only [physical_card] using h

/-- Deleting any collection of physical blocks preserves the actual local
conditions, at the unchanged full-population normalization. This is the
complement estimate required by arbitrary joint tagged insertions. -/
theorem current_subproduct_conditions_eventually (multiple : ℝ) (hmultiple : 0 ≤ multiple) :
    ∃ threshold : ℕ, ∀ security ≥ threshold,
      ∀ ar : Fin (Parameters.legCount security) → ℤ,
      ∀ cr : Fin (centerCount security) → ℤ,
      ∀ qr : Fin (Parameters.modulus security) → ℤ, ∀ queue : ℤ,
      ∀ selected : Finset (BlockIndex security),
      BlockProducts.CubicBlockConditions (fun index : selected => Slots security index.val)
        (LocalReferenceEnergy.uniformReference security)
        (fun index : selected => blockLawAt security ar cr qr queue index.val)
        (Parameters.dimension security) (Parameters.dimension security) (multiple * radius security) := by
  have hm : 0 ≤ Real.sqrt 2 * multiple := mul_nonneg (Real.sqrt_nonneg _) hmultiple
  obtain ⟨threshold, hthreshold⟩ := envelopes_eventually (Real.sqrt 2 * multiple) hm
  refine ⟨threshold, ?_⟩
  intro security hsecurity ar cr qr queue selected
  obtain ⟨hlinear, hnonlinear⟩ := hthreshold security hsecurity
  have hscale : Real.sqrt 2 * (multiple * radius security / Real.sqrt (Parameters.dimension security : ℝ)) =
      normalizedScale security (Real.sqrt 2 * multiple) := by unfold normalizedScale; ring
  apply BlockProducts.CubicBlockConditions_of_scaled
    (fun index : selected => Slots security index.val) (LocalReferenceEnergy.uniformReference security)
    (fun index : selected => blockLawAt security ar cr qr queue index.val)
    (Parameters.dimension security) (Parameters.dimension security) (multiple * radius security)
  · simpa only [Fintype.card_coe] using (Finset.card_le_univ selected).trans (blockCount_le_dimension security)
  · rw [hscale]
    have hsubset : (∑ index : selected, ∑ color, BlockProducts.normalizedLinear
        (fun index : selected => Slots security index.val) (LocalReferenceEnergy.uniformReference security)
        (fun index : selected => blockLawAt security ar cr qr queue index.val)
        (normalizedScale security (Real.sqrt 2 * multiple)) index color ^ 2) ≤
        ∑ index : BlockIndex security, ∑ color, BlockProducts.normalizedLinear
          (Slots security) (LocalReferenceEnergy.uniformReference security) (blockLawAt security ar cr qr queue)
          (normalizedScale security (Real.sqrt 2 * multiple)) index color ^ 2 := by
      change (∑ index : selected, (fun index : BlockIndex security => ∑ color, BlockProducts.normalizedLinear
        (Slots security) (LocalReferenceEnergy.uniformReference security) (blockLawAt security ar cr qr queue)
        (normalizedScale security (Real.sqrt 2 * multiple)) index color ^ 2) index.val) ≤ _
      exact subtype_sum_le selected _ (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    exact hsubset.trans ((linearActivity_le security ar cr qr _ queue).trans hlinear)
  · rw [hscale]
    have hsubset : (∑ index : selected, (128 * SelectionBound.localPairNorm
        (BlockProducts.normalizedQuadratic (fun index : selected => Slots security index.val)
          (LocalReferenceEnergy.uniformReference security)
          (fun index : selected => blockLawAt security ar cr qr queue index.val)
          (normalizedScale security (Real.sqrt 2 * multiple))) index +
        128 * Real.sqrt (Parameters.dimension security : ℝ) * SelectionBound.localTripleNorm
          (BlockProducts.normalizedCubic (fun index : selected => Slots security index.val)
            (LocalReferenceEnergy.uniformReference security)
            (fun index : selected => blockLawAt security ar cr qr queue index.val)
            (normalizedScale security (Real.sqrt 2 * multiple))) index)) ≤
        ∑ index : BlockIndex security, (128 * SelectionBound.localPairNorm
          (BlockProducts.normalizedQuadratic (Slots security) (LocalReferenceEnergy.uniformReference security)
            (blockLawAt security ar cr qr queue) (normalizedScale security (Real.sqrt 2 * multiple))) index +
          128 * Real.sqrt (Parameters.dimension security : ℝ) * SelectionBound.localTripleNorm
            (BlockProducts.normalizedCubic (Slots security) (LocalReferenceEnergy.uniformReference security)
              (blockLawAt security ar cr qr queue) (normalizedScale security (Real.sqrt 2 * multiple))) index) := by
      change (∑ index : selected, (fun index : BlockIndex security =>
        128 * SelectionBound.localPairNorm
          (BlockProducts.normalizedQuadratic (Slots security) (LocalReferenceEnergy.uniformReference security)
            (blockLawAt security ar cr qr queue) (normalizedScale security (Real.sqrt 2 * multiple))) index +
        128 * Real.sqrt (Parameters.dimension security : ℝ) * SelectionBound.localTripleNorm
          (BlockProducts.normalizedCubic (Slots security) (LocalReferenceEnergy.uniformReference security)
            (blockLawAt security ar cr qr queue) (normalizedScale security (Real.sqrt 2 * multiple))) index) index.val) ≤ _
      apply subtype_sum_le selected (fun index : BlockIndex security =>
        128 * SelectionBound.localPairNorm
          (BlockProducts.normalizedQuadratic (Slots security) (LocalReferenceEnergy.uniformReference security)
            (blockLawAt security ar cr qr queue) (normalizedScale security (Real.sqrt 2 * multiple))) index +
        128 * Real.sqrt (Parameters.dimension security : ℝ) * SelectionBound.localTripleNorm
          (BlockProducts.normalizedCubic (Slots security) (LocalReferenceEnergy.uniformReference security)
            (blockLawAt security ar cr qr queue) (normalizedScale security (Real.sqrt 2 * multiple))) index)
      intro index
      unfold SelectionBound.localPairNorm SelectionBound.localTripleNorm
      positivity
    exact hsubset.trans ((nonlinearActivity_le security ar cr qr queue _
      (normalizedScale_nonneg security _ hm) (Parameters.dimension security)).trans hnonlinear)

end

end CurrentAFT.PhysicalFockRates
