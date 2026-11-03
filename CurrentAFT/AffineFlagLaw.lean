import CurrentAFT.AffineMarkedFiber

/-!
# One positive public affine-map law for all protected inputs

This is the current marked-line theorem.  The public law is a distribution
on complete `(flag, intercept, scale, shear)` tuples, constructed before any
protected input is supplied.  The hypotheses are the manuscript's finite
palette budgets; no response inverse or positive map law is assumed.
-/

namespace CurrentAFT.AffineFlagCalibration

open AFT AFT.BoundaryCalibration
open scoped BigOperators Classical

noncomputable section

variable {F I : Type*} [Field F] [Fintype F] [Fintype I]

theorem affine_flag_law (inputs : I → F × F) (hinj : Function.Injective inputs)
    (allowed : I → Finset F) (mark : F)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hbudget : affineDeletionBudget allowed ≤ δ)
    (hsmall : (2 * Fintype.card I + 1) * δ ≤ 1 / 4)
    (hpositivity : (Fintype.card I : ℝ) / (1 - δ) *
      (δ + ((2 * Fintype.card I + 1) * δ) /
        (1 - (2 * Fintype.card I + 1) * δ)) ≤ 1 / 3)
    (atom : ℝ) (ha0 : 0 ≤ atom) (haHalf : atom ≤ 1 / 2) :
    ∃ regular marked : FiniteDist (Chart F),
      ∃ law : FiniteDist (Bool × Chart F),
      law = flagLaw atom ha0 (by linarith) regular marked ∧
      (∀ chart, ¬ (chart.2.1 ≠ 0 ∧
        ∀ i, feature (inputs i).1 (inputs i).2 chart ∈ allowed i) → regular.weight chart = 0) ∧
      (∀ chart, chart.2.1 ≠ 0 →
        (∀ i, feature (inputs i).1 (inputs i).2 chart ∈ allowed i) →
          (Fintype.card (Chart F) : ℝ)⁻¹ / 3 ≤ regular.weight chart) ∧
      (∀ chart, ¬ (chart.1 = mark ∧ chart.2.2 = 0 ∧ chart.2.1 ≠ 0 ∧
        ∀ i, (inputs i).1 ≠ 0 → feature (inputs i).1 (inputs i).2 chart ∈ allowed i) →
          marked.weight chart = 0) ∧
      (∀ flag, (law.map Prod.fst).weight flag = if flag then atom else 1 - atom) ∧
      (∀ i, (inputs i).1 = 0 → ∀ c,
        (law.map (fun point => feature (inputs i).1 (inputs i).2 point.2)).weight c =
          (1 - atom) * (if c ∈ allowed i then ((allowed i).card : ℝ)⁻¹ else 0) +
            atom * (if c = mark then 1 else 0)) ∧
      (∀ i, (inputs i).1 ≠ 0 → ∀ c,
        (law.map (fun point => feature (inputs i).1 (inputs i).2 point.2)).weight c =
          if c ∈ allowed i then ((allowed i).card : ℝ)⁻¹ else 0) := by
  let p := FiniteDist.uniform (Chart F)
  let features := fun i => feature (inputs i).1 (inputs i).2
  let auxiliary := fun chart : Chart F => chart.2.1
  let auxAllowed : Finset F := Finset.univ.erase 0
  let safe := legalChart auxiliary auxAllowed features allowed
  have hfeature (i : I) : p.map (features i) = FiniteDist.uniform F := feature_uniform _ _
  have hpair (i j : I) (hij : i ≠ j) : p.map (fun x => (features i x, features j x)) =
      (FiniteDist.uniform F).prod (FiniteDist.uniform F) :=
    feature_pair_uniform (inputs i) (inputs j) (fun h => hij (hinj h))
  have hauxpair (i : I) : p.map (fun x => (features i x, auxiliary x)) =
      (FiniteDist.uniform F).prod (FiniteDist.uniform F) := feature_scale_uniform _ _
  have hbudgetFormula : expectation (FiniteDist.uniform F) (paletteFailure auxAllowed) +
      ∑ i, expectation (FiniteDist.uniform F) (paletteFailure (allowed i)) =
        affineDeletionBudget allowed := by
    rw [show expectation (FiniteDist.uniform F) (paletteFailure auxAllowed) =
        (Fintype.card F : ℝ)⁻¹ from nonzero_palette_failure]
    simp only [uniform_palette_failure, affineDeletionBudget]
  have hglobal : expectation p (badIndicator safe) ≤ δ := by
    apply le_trans _ hbudget
    rw [← hbudgetFormula]
    exact legalChart_global_budget p auxiliary auxAllowed features allowed scale_uniform hfeature
  have hconditional : ∀ i c, c ∈ allowed i → conditional p (features i) (badIndicator safe) c ≤ δ := by
    intro i c hc
    apply le_trans _ hbudget
    rw [← hbudgetFormula]
    exact legalChart_conditional_budget p auxiliary auxAllowed features allowed
      hfeature hpair hauxpair i c hc
  have hsurvival : 0 < markedSurvival inputs allowed mark := by
    have hl := markedSurvival_lower inputs allowed mark
    linarith
  let marked := markedChartLaw inputs allowed mark hsurvival
  let spike := uniformDensity marked
  have hsmean : expectation p spike = 1 := uniformDensity_mean marked
  have hsnonneg (chart : Chart F) : 0 ≤ spike chart := uniformDensity_nonneg marked chart
  have hsallowed (i : I) (hi : ¬ (inputs i).1 = 0) (chart : Chart F)
      (hc : features i chart ∉ allowed i) : spike chart = 0 := by
    have hz : marked.weight chart = 0 := markedChartLaw_support inputs allowed mark hsurvival chart
      (by rintro ⟨_, _, _, hh⟩; exact hc (hh i hi))
    simp only [spike, uniformDensity, hz, mul_zero]
  have hsbound (i : I) (hi : ¬ (inputs i).1 = 0) (c : F) :
      conditional p (features i) spike c ≤ 1 / (1 - δ) :=
    markedDensity_bound inputs allowed mark δ hδ1 hbudget hsurvival i hi c
  obtain ⟨density, hdmean, hdnonneg, hdzero, hdlower, hdline, hdoff⟩ :=
    regular_branch p features allowed (fun i => (inputs i).1 = 0) hfeature hpair safe
      (fun i chart hc => hc.2 i) δ hδ0 hδ1 hglobal hconditional hsmall hpositivity
      atom ha0 haHalf spike hsmean hsnonneg hsallowed hsbound
  let regular := densityLaw p density hdnonneg hdmean
  let law := flagLaw atom ha0 (by linarith : atom ≤ 1) regular marked
  have hregular (i : I) (hi : (inputs i).1 = 0) (c : F) :
      (regular.map (features i)).weight c =
        if c ∈ allowed i then ((allowed i).card : ℝ)⁻¹ else 0 := by
    rw [densityLaw_marginal, hdline i hi]
    split_ifs
    · have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      field_simp
    · simp
  refine ⟨regular, marked, law, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro chart hc
    have hn : ¬ safe chart := by
      simpa only [safe, legalChart, auxiliary, auxAllowed, features, Finset.mem_erase,
        Finset.mem_univ, and_true] using hc
    simp only [regular, densityLaw, hdzero chart hn, mul_zero]
  · intro chart hn hc
    have hs : safe chart := by
      simpa only [safe, legalChart, auxiliary, auxAllowed, features, Finset.mem_erase,
        Finset.mem_univ, and_true] using And.intro hn hc
    change (Fintype.card (Chart F) : ℝ)⁻¹ / 3 ≤
      (Fintype.card (Chart F) : ℝ)⁻¹ * density chart
    have hh := mul_le_mul_of_nonneg_left (hdlower chart hs)
      (inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card (Chart F)) : (0 : ℝ) ≤ _))
    simpa only [div_eq_mul_inv, one_mul] using hh
  · exact markedChartLaw_support inputs allowed mark hsurvival
  · exact flagLaw_flag atom ha0 (by linarith) regular marked
  · intro i hi c
    rw [flagLaw_feature, hregular i hi c,
      markedChartLaw_line inputs allowed mark hsurvival i hi c]
  · intro i hi c
    rw [flagLaw_feature, densityLaw_marginal]
    have hm := uniformDensity_conditional marked (features i) c
    have hf := hdoff i hi c
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hf
    change (1 - atom) * (conditional p (features i) density c / Fintype.card F) +
      atom * (marked.map (features i)).weight c = _
    change conditional p (features i) spike c = _ at hm
    rw [hm] at hf
    have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    split_ifs at hf ⊢ <;> field_simp <;> nlinarith [hf]

end
end CurrentAFT.AffineFlagCalibration
