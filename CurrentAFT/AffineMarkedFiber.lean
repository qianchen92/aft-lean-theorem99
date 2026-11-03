import CurrentAFT.AffineFlagCalibration

/-!
# The actual one-dimensional marked affine fiber

Marked charts have intercept `mark`, shear zero, and a uniformly sampled
surviving nonzero scale.  The survival and marginal bounds below are proved
from finite affine bijections and the palette deletion budget.
-/

namespace CurrentAFT.AffineFlagCalibration

open AFT AFT.BoundaryCalibration
open scoped BigOperators Classical

noncomputable section

variable {F I : Type*} [Field F] [Fintype F] [Fintype I]

def markedEvaluationEquiv (mark first : F) (hfirst : first ≠ 0) : F ≃ F where
  toFun scale := mark + scale * first
  invFun color := (color - mark) / first
  left_inv scale := by field_simp; ring
  right_inv color := by field_simp; ring

def markedScaleSafe (inputs : I → F × F) (allowed : I → Finset F)
    (mark scale : F) : Prop :=
  scale ≠ 0 ∧ ∀ i, (inputs i).1 ≠ 0 → mark + scale * (inputs i).1 ∈ allowed i

def markedSurvival (inputs : I → F × F) (allowed : I → Finset F) (mark : F) : ℝ :=
  eventMass (FiniteDist.uniform F) (markedScaleSafe inputs allowed mark)

theorem marked_scale_deletion (inputs : I → F × F) (allowed : I → Finset F) (mark : F) :
    expectation (FiniteDist.uniform F) (badIndicator (markedScaleSafe inputs allowed mark)) ≤
      affineDeletionBudget allowed := by
  let Off := {i : I // (inputs i).1 ≠ 0}
  let features : Off → F → F := fun i scale => mark + scale * (inputs i.val).1
  let palettes : Off → Finset F := fun i => allowed i.val
  let auxAllowed : Finset F := Finset.univ.erase 0
  have hfeatures (i : Off) : (FiniteDist.uniform F).map (features i) = FiniteDist.uniform F :=
    FiniteDist.uniform_map_equiv (markedEvaluationEquiv mark (inputs i.val).1 i.property)
  have hsafe : markedScaleSafe inputs allowed mark = legalChart id auxAllowed features palettes := by
    funext scale
    apply propext
    simp only [markedScaleSafe, legalChart, auxAllowed, Finset.mem_erase,
      Finset.mem_univ, and_true, id_eq]
    constructor
    · rintro ⟨hn, hh⟩
      exact ⟨hn, fun i => hh i.val i.property⟩
    · rintro ⟨hn, hh⟩
      exact ⟨hn, fun i hi => hh ⟨i, hi⟩⟩
  have hb := legalChart_global_budget (FiniteDist.uniform F) id auxAllowed features palettes
    (FiniteDist.uniform_map_equiv (Equiv.refl F)) hfeatures
  rw [← hsafe] at hb
  apply hb.trans
  rw [show expectation (FiniteDist.uniform F) (paletteFailure auxAllowed) =
      (Fintype.card F : ℝ)⁻¹ from nonzero_palette_failure]
  unfold affineDeletionBudget
  apply add_le_add le_rfl
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun i : I => (inputs i).1 ≠ 0)
    (fun i => expectation (FiniteDist.uniform F) (paletteFailure (allowed i)))
  have hnonneg : 0 ≤ ∑ i : {i : I // ¬ (inputs i).1 ≠ 0},
      expectation (FiniteDist.uniform F) (paletteFailure (allowed i.val)) := by
    apply Finset.sum_nonneg
    intro i _
    rw [expectation_apply]
    apply Finset.sum_nonneg
    intro c _
    exact mul_nonneg (FiniteDist.uniform F |>.nonneg c)
      (by unfold paletteFailure; split_ifs <;> norm_num)
  simp only [uniform_palette_failure] at hsplit ⊢
  simp only [uniform_palette_failure, palettes] at *
  linarith

theorem markedSurvival_lower (inputs : I → F × F) (allowed : I → Finset F) (mark : F) :
    1 - affineDeletionBudget allowed ≤ markedSurvival inputs allowed mark := by
  have h := marked_scale_deletion inputs allowed mark
  have he : eventIndicator (markedScaleSafe inputs allowed mark) =
      (1 : F → ℝ) - badIndicator (markedScaleSafe inputs allowed mark) := by
    funext scale
    simp only [eventIndicator, badIndicator, Pi.sub_apply, Pi.one_apply]
    split_ifs <;> norm_num
  change _ ≤ expectation (FiniteDist.uniform F) (eventIndicator _)
  rw [he, map_sub, show expectation (FiniteDist.uniform F) (1 : F → ℝ) = 1 from
    expectation_const _ 1]
  linarith

def markedScaleLaw (inputs : I → F × F) (allowed : I → Finset F) (mark : F)
    (hpos : 0 < markedSurvival inputs allowed mark) : FiniteDist F :=
  densityLaw (FiniteDist.uniform F)
    (restrictedDensity (FiniteDist.uniform F) (markedScaleSafe inputs allowed mark))
    (restrictedDensity_nonneg _ _) (restrictedDensity_mean _ _ hpos)

def markedChartLaw (inputs : I → F × F) (allowed : I → Finset F) (mark : F)
    (hpos : 0 < markedSurvival inputs allowed mark) : FiniteDist (Chart F) :=
  (markedScaleLaw inputs allowed mark hpos).map (fun scale => (mark, scale, 0))

omit [Fintype I] in
theorem markedChartLaw_support (inputs : I → F × F) (allowed : I → Finset F) (mark : F)
    (hpos : 0 < markedSurvival inputs allowed mark) (chart : Chart F)
    (hchart : ¬ (chart.1 = mark ∧ chart.2.2 = 0 ∧ chart.2.1 ≠ 0 ∧
      ∀ i, (inputs i).1 ≠ 0 → feature (inputs i).1 (inputs i).2 chart ∈ allowed i)) :
    (markedChartLaw inputs allowed mark hpos).weight chart = 0 := by
  rw [markedChartLaw, FiniteDist.map_weight]
  apply Finset.sum_eq_zero
  intro scale _
  by_cases he : (mark, scale, (0 : F)) = chart
  · subst chart
    have hn : ¬ markedScaleSafe inputs allowed mark scale := by
      intro hs
      apply hchart
      refine ⟨rfl, rfl, hs.1, ?_⟩
      intro i hi
      simpa only [feature, zero_mul, add_zero] using hs.2 i hi
    simp [markedScaleLaw, densityLaw, restrictedDensity, eventIndicator, hn]
  · simp only [if_neg he]

omit [Fintype I] in
theorem markedChartLaw_line (inputs : I → F × F) (allowed : I → Finset F) (mark : F)
    (hpos : 0 < markedSurvival inputs allowed mark) (i : I) (hi : (inputs i).1 = 0) (c : F) :
    ((markedChartLaw inputs allowed mark hpos).map (feature (inputs i).1 (inputs i).2)).weight c =
      if c = mark then 1 else 0 := by
  rw [markedChartLaw, FiniteDist.map_map, FiniteDist.map_weight]
  simp only [feature, hi, mul_zero, zero_mul, add_zero]
  by_cases hc : c = mark
  · subst c
    simpa only [if_pos rfl] using (markedScaleLaw inputs allowed mark hpos).sum_one
  · simp [Ne.symm hc, hc]

omit [Fintype I] in
theorem markedChartLaw_offLine_bound (inputs : I → F × F) (allowed : I → Finset F) (mark : F)
    (hpos : 0 < markedSurvival inputs allowed mark) (i : I) (hi : (inputs i).1 ≠ 0) (c : F) :
    ((markedChartLaw inputs allowed mark hpos).map (feature (inputs i).1 (inputs i).2)).weight c ≤
      (Fintype.card F : ℝ)⁻¹ / markedSurvival inputs allowed mark := by
  rw [markedChartLaw, FiniteDist.map_map]
  have hf : (fun a : F => feature (inputs i).1 (inputs i).2 (mark, a, 0)) =
      markedEvaluationEquiv mark (inputs i).1 hi := by
    funext a
    simp only [feature, zero_mul, add_zero, markedEvaluationEquiv, Equiv.coe_fn_mk]
  rw [hf]
  rw [FiniteDist.map_equiv_weight]
  change (Fintype.card F : ℝ)⁻¹ *
    (eventIndicator (markedScaleSafe inputs allowed mark) _ / markedSurvival inputs allowed mark) ≤ _
  unfold eventIndicator
  split_ifs
  · simp only [div_eq_mul_inv, one_mul, le_refl]
  · simp only [zero_div, mul_zero]
    positivity

section Density
variable {Ω C : Type*} [Fintype Ω] [Nonempty Ω] [Fintype C]

/-- Convert a literal probability law into its density against the full
uniform coefficient table. -/
def uniformDensity (law : FiniteDist Ω) : Ω → ℝ :=
  fun x => (Fintype.card Ω : ℝ) * law.weight x

omit [Nonempty Ω] in
theorem uniformDensity_nonneg (law : FiniteDist Ω) (x : Ω) : 0 ≤ uniformDensity law x :=
  mul_nonneg (Nat.cast_nonneg _) (law.nonneg x)

theorem uniformDensity_mean (law : FiniteDist Ω) :
    expectation (FiniteDist.uniform Ω) (uniformDensity law) = 1 := by
  have hq : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [expectation_apply, FiniteDist.uniform_weight, uniformDensity,
    ← mul_assoc, inv_mul_cancel₀ hq, one_mul]
  exact law.sum_one

theorem uniformDensity_conditional (law : FiniteDist Ω) (f : Ω → C) (c : C) :
    conditional (FiniteDist.uniform Ω) f (uniformDensity law) c =
      (Fintype.card C : ℝ) * (law.map f).weight c := by
  have hq : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [conditional_apply, expectation_apply, FiniteDist.uniform_weight,
    uniformDensity, FiniteDist.map_weight, mul_ite, mul_zero,
    ← mul_assoc, inv_mul_cancel₀ hq, one_mul]

end Density

theorem markedDensity_bound (inputs : I → F × F) (allowed : I → Finset F) (mark : F)
    (δ : ℝ) (hδ : δ < 1) (hbudget : affineDeletionBudget allowed ≤ δ)
    (hpos : 0 < markedSurvival inputs allowed mark) (i : I) (hi : (inputs i).1 ≠ 0) (c : F) :
    conditional (FiniteDist.uniform (Chart F)) (feature (inputs i).1 (inputs i).2)
      (uniformDensity (markedChartLaw inputs allowed mark hpos)) c ≤ 1 / (1 - δ) := by
  rw [uniformDensity_conditional]
  have hq : (0 : ℝ) < Fintype.card F := Nat.cast_pos.mpr Fintype.card_pos
  have hm := mul_le_mul_of_nonneg_left
    (markedChartLaw_offLine_bound inputs allowed mark hpos i hi c) hq.le
  have hl : 1 - δ ≤ markedSurvival inputs allowed mark :=
    (by linarith : 1 - δ ≤ 1 - affineDeletionBudget allowed).trans
      (markedSurvival_lower inputs allowed mark)
  calc
    _ ≤ (Fintype.card F : ℝ) * ((Fintype.card F : ℝ)⁻¹ / markedSurvival inputs allowed mark) := hm
    _ = 1 / markedSurvival inputs allowed mark := by rw [← mul_div_assoc, mul_inv_cancel₀ hq.ne']
    _ ≤ _ := one_div_le_one_div_of_le (by linarith) hl

end
end CurrentAFT.AffineFlagCalibration
