import AFT.BoundarySpike

/-! # The exact Neumann formula of the positive marked chart

These statements expose the explicit densities already used in the chart
proof, so that the rational program can approximate the same construction.
-/
namespace AFT.BoundaryCalibration
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Ω C I : Type*} [Fintype Ω] [Fintype C] [Fintype I]

theorem explicit_positive_chart_density [Nonempty Ω] [Nonempty C] (p : FiniteDist Ω)
    (features : I → Ω → C) (allowed : I → Finset C)
    (hfeature : ∀ i, p.map (features i) = FiniteDist.uniform C)
    (hpair : ∀ i j, i ≠ j → p.map (fun x => (features i x, features j x)) =
      (FiniteDist.uniform C).prod (FiniteDist.uniform C))
    (safe : Ω → Prop) [DecidablePred safe]
    (hallowed : ∀ i x, safe x → features i x ∈ allowed i)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hglobal : expectation p (badIndicator safe) ≤ ε)
    (hconditional : ∀ i c, c ∈ allowed i →
      conditional p (features i) (badIndicator safe) c ≤ ε)
    (hsmall : (2 * Fintype.card I + 1) * ε ≤ 1 / 4)
    (hcontract : ‖deletion (chartProjection p features allowed) safe‖ < 1) :
    ∃ w : Ω → ℝ,
      w = safeMask safe (neumannSolve (deletion (chartProjection p features allowed) safe) hcontract 1) ∧
      expectation p w = 1 ∧ (∀ x, 0 ≤ w x) ∧
      (∀ x, ¬ safe x → w x = 0) ∧ (∀ x, safe x → 2 / 3 ≤ w x) ∧
      (∀ i c, conditional p (features i) w c =
        if c ∈ allowed i then (Fintype.card C : ℝ) / (allowed i).card else 0) := by
  let P := chartProjection p features allowed
  have hquarter : ‖deletion P safe‖ ≤ 1 / 4 :=
    (chartDeletion_norm p features allowed safe ε hε hglobal hconditional).trans hsmall
  have hD : ‖deletion P safe‖ < 1 := lt_of_le_of_lt hquarter (by norm_num)
  let w := safeMask safe (neumannSolve (deletion P safe) hD 1)
  have hproj : P w = 1 := safe_neumann_projection P safe
    (chartProjection_idempotent p features allowed hfeature hpair) hD 1
    (combinedProjection_one p features allowed hfeature)
  have hmean : expectation p w = 1 := by
    have hm := combinedProjection_mean p features allowed hfeature w
    change expectation p (P w) = expectation p w at hm
    rw [hproj] at hm
    change expectation p (fun _ => 1) = expectation p w at hm
    rw [expectation_const p 1] at hm
    exact hm.symm
  have hzero : ∀ x, ¬ safe x → w x = 0 := by
    intro x hx
    simp [w, hx]
  have hpos : ∀ x, safe x → 2 / 3 ≤ w x :=
    interior_density_lower P safe hD hquarter
  refine ⟨w, rfl, hmean, ?_, hzero, hpos, ?_⟩
  · intro x
    by_cases hx : safe x
    · exact (by norm_num : (0 : ℝ) ≤ 2 / 3).trans (hpos x hx)
    · rw [hzero x hx]
  · intro i c
    have hi : featureProjection p (features i) (allowed i) w = 0 := by
      rw [← featureProjection_combined p features allowed hfeature hpair i w]
      change featureProjection p (features i) (allowed i) (P w) = 0
      rw [hproj]
      exact featureProjection_const p (features i) (hfeature i) (allowed i) 1
    have hc := congrArg (conditional p (features i)) hi
    change conditional p (features i) (fun x => centerAllowed (allowed i)
      (conditional p (features i) w) (features i x)) = conditional p (features i) 0 at hc
    rw [conditional_same p (features i) (hfeature i), map_zero] at hc
    have hz : ∀ c ∉ allowed i, conditional p (features i) w c = 0 :=
      conditional_outside_zero p (features i) (allowed i) safe w hzero (hallowed i)
    rw [centerAllowed_zero_profile (allowed i) _ hc hz c, conditional_sum, hmean, mul_one]

theorem explicit_marked_repaired_density [Nonempty Ω] [Nonempty C] (p : FiniteDist Ω)
    (features : I → Ω → C) (allowed : I → Finset C) (zero : I)
    (hfeature : ∀ i, p.map (features i) = FiniteDist.uniform C)
    (hpair : ∀ i j, i ≠ j → p.map (fun x => (features i x, features j x)) =
      (FiniteDist.uniform C).prod (FiniteDist.uniform C))
    (safe : Ω → Prop) [DecidablePred safe]
    (hallowed : ∀ i x, safe x → features i x ∈ allowed i)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hglobal : expectation p (badIndicator safe) ≤ ε)
    (hconditional : ∀ i c, c ∈ allowed i → conditional p (features i) (badIndicator safe) c ≤ ε)
    (hsmall : (2 * Fintype.card I + 1) * ε ≤ 1 / 4)
    (atom : ℝ) (hatom : 0 ≤ atom) (hatom100 : atom ≤ 1 / 100)
    (hsize : 4 * atom * Fintype.card I ≤ 1 / 25)
    (spike : Ω → ℝ) (hspikemean : expectation p spike = 1)
    (hspike : ∀ x, 0 ≤ spike x)
    (hspikeallowed : ∀ i, i ≠ zero → ∀ x, features i x ∉ allowed i → spike x = 0)
    (hspikebound : ∀ i, i ≠ zero → ∀ c, conditional p (features i) spike c ≤ 2)
    (hcontract : ‖deletion (chartProjection p features allowed) safe‖ < 1) :
    ∃ repaired : Ω → ℝ,
      repaired = safeMask safe (neumannSolve (deletion (chartProjection p features allowed) safe) hcontract 1) -
        (1-atom)⁻¹ • safeMask safe (neumannSolve (deletion (chartProjection p features allowed) safe) hcontract
          (spikeDefect p features allowed zero atom spike)) ∧
      expectation p repaired = 1 ∧ (∀ x, 0 ≤ repaired x) ∧
      (∀ x, ¬ safe x → repaired x = 0) ∧
      (∀ c, conditional p (features zero) repaired c =
        if c ∈ allowed zero then (Fintype.card C : ℝ) / (allowed zero).card else 0) ∧
      (∀ i, i ≠ zero → ∀ c,
        conditional p (features i) ((1 - atom) • repaired + atom • spike) c =
          if c ∈ allowed i then (Fintype.card C : ℝ) / (allowed i).card else 0) := by
  obtain ⟨base, hbaseformula, hbasemean, hbase, hbasezero, hbaselower, hbasemarg⟩ :=
    explicit_positive_chart_density p features allowed hfeature hpair safe hallowed ε hε hglobal hconditional hsmall hcontract
  let P := chartProjection p features allowed
  let defect := spikeDefect p features allowed zero atom spike
  have hquarter : ‖deletion P safe‖ ≤ 1 / 4 :=
    (chartDeletion_norm p features allowed safe ε hε hglobal hconditional).trans hsmall
  have hD : ‖deletion P safe‖ < 1 := lt_of_le_of_lt hquarter (by norm_num)
  let raw := neumannSolve (deletion P safe) hD defect
  let repair := safeMask safe raw
  have hdefect : ‖defect‖ ≤ 1 / 25 :=
    spikeDefect_norm p features allowed zero atom spike hatom hspike hspikebound hsize
  have hrepairnorm : ‖raw‖ ≤ 4 / 75 := repair_density_norm P safe hD hquarter defect hdefect
  have hproject : P repair = defect := safe_neumann_projection P safe
    (chartProjection_idempotent p features allowed hfeature hpair) hD defect
    (spikeDefect_projected p features allowed zero atom spike hfeature hpair)
  have hrepairmean : expectation p repair = 0 := by
    have h := combinedProjection_mean p features allowed hfeature repair
    change expectation p (P repair) = expectation p repair at h
    rw [hproject, spikeDefect_mean p features allowed zero atom spike hfeature] at h
    exact h.symm
  have hrepairzero (x : Ω) (hx : ¬ safe x) : repair x = 0 := by simp [repair, hx]
  have hcomponent (i : I) : featureProjection p (features i) (allowed i) repair =
      if i = zero then 0 else atom • featureProjection p (features i) (allowed i) spike := by
    rw [← featureProjection_combined p features allowed hfeature hpair i repair]
    change featureProjection p (features i) (allowed i) (P repair) = _
    rw [hproject]
    exact spikeDefect_component p features allowed zero atom spike hfeature hpair i
  have hbasecomp (i : I) : featureProjection p (features i) (allowed i) base = 0 := by
    change liftFeature (features i) (centerAllowed (allowed i) (conditional p (features i) base)) = 0
    have hprof : conditional p (features i) base = fun c =>
        if c ∈ allowed i then (Fintype.card C : ℝ) / (allowed i).card else 0 := funext (hbasemarg i)
    rw [hprof, centerAllowed_masked_const, map_zero]
  have hden : 0 < 1 - atom := by linarith
  let repaired := base - (1 - atom)⁻¹ • repair
  have hrmean : expectation p repaired = 1 := by
    simp only [repaired, map_sub, map_smul, hbasemean, hrepairmean, smul_zero, sub_zero]
  have hrzero (x : Ω) (hx : ¬ safe x) : repaired x = 0 := by
    simp [repaired, hbasezero x hx, hrepairzero x hx]
  have hrnonneg (x : Ω) : 0 ≤ repaired x := by
    by_cases hx : safe x
    · have hb := hbaselower x hx
      have hu : raw x ≤ 4 / 75 :=
        (le_abs_self _).trans ((norm_le_pi_norm raw x).trans hrepairnorm)
      have hsmallrepair : repair x / (1 - atom) ≤ 1 / 15 := by
        rw [div_le_iff₀ hden]
        rw [show repair x = raw x by simp [repair, hx]]
        nlinarith
      change 0 ≤ base x - (1 - atom)⁻¹ * repair x
      rw [← div_eq_inv_mul]
      linarith
    · rw [hrzero x hx]
  have hzeroMarg (c : C) : conditional p (features zero) repair c = 0 := by
    have hc := hcomponent zero
    rw [if_pos rfl] at hc
    have hs := conditional_outside_zero p (features zero) (allowed zero) safe repair hrepairzero
      (hallowed zero)
    rw [component_zero_marginal p (features zero) (hfeature zero) (allowed zero) repair hc hs c,
      hrepairmean, mul_zero, zero_div]
    split_ifs <;> rfl
  refine ⟨repaired, ?_, hrmean, hrnonneg, hrzero, ?_, ?_⟩
  · dsimp only [repaired, repair, raw]
    rw [hbaseformula]
  · intro c
    change conditional p (features zero) (base - (1 - atom)⁻¹ • repair) c = _
    simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      hzeroMarg, mul_zero, sub_zero, hbasemarg]
  · intro i hi c
    let final := (1 - atom) • repaired + atom • spike
    have hf : final = (1 - atom) • base - repair + atom • spike := by
      dsimp [final, repaired]
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hden.ne', one_smul]
    have hfmean : expectation p final = 1 := by
      simp only [final, map_add, map_smul, hrmean, hspikemean, smul_eq_mul, mul_one]
      ring
    have hfcomp : featureProjection p (features i) (allowed i) final = 0 := by
      rw [hf, map_add, map_sub, map_smul, map_smul, hbasecomp, hcomponent i, if_neg hi]
      simp
    have hfzero (x : Ω) (hx : features i x ∉ allowed i) : final x = 0 := by
      have hn : ¬ safe x := fun hs => hx (hallowed i x hs)
      simp [final, hrzero x hn, hspikeallowed i hi x hx]
    have hs := conditional_outside_zero p (features i) (allowed i)
      (fun x => features i x ∈ allowed i) final hfzero (fun _ h => h)
    rw [component_zero_marginal p (features i) (hfeature i) (allowed i) final hfcomp hs c,
      hfmean, mul_one]


end
end AFT.BoundaryCalibration
