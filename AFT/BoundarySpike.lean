import AFT.BoundaryCalibration

/-!
# The isolated mark in the positive boundary chart

The spike is a normalized restriction of the genuine unrestricted chart law
onto the surviving marked fiber.  Its positive mass and marginal bounds follow
from uniform pairwise-independent features and the public deletion budget.
-/
namespace AFT
namespace BoundaryCalibration

open scoped BigOperators Classical

section RestrictedFiber
variable {Ω C J : Type*} [Fintype Ω] [Fintype C] [Nonempty C] [Fintype J]

/-- An event as a real-valued chart density. -/
noncomputable def eventIndicator (event : Ω → Prop) : Ω → ℝ :=
  fun x => if event x then 1 else 0

omit [Fintype Ω] in
@[simp] theorem eventIndicator_nonneg (event : Ω → Prop) (x : Ω) :
    0 ≤ eventIndicator event x := by unfold eventIndicator; split_ifs <;> norm_num

/-- Unrestricted probability of a finite chart event. -/
noncomputable def eventMass (p : FiniteDist Ω) (event : Ω → Prop) : ℝ :=
  expectation p (eventIndicator event)

theorem eventMass_nonneg (p : FiniteDist Ω) (event : Ω → Prop) :
    0 ≤ eventMass p event :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (p.nonneg x) (eventIndicator_nonneg event x))

/-- A literal conditioning density relative to the unrestricted chart law. -/
noncomputable def restrictedDensity (p : FiniteDist Ω) (event : Ω → Prop) : Ω → ℝ :=
  fun x => eventIndicator event x / eventMass p event

theorem restrictedDensity_nonneg (p : FiniteDist Ω) (event : Ω → Prop) (x : Ω) :
    0 ≤ restrictedDensity p event x :=
  div_nonneg (eventIndicator_nonneg event x) (eventMass_nonneg p event)

theorem restrictedDensity_mean (p : FiniteDist Ω) (event : Ω → Prop)
    (hpos : 0 < eventMass p event) : expectation p (restrictedDensity p event) = 1 := by
  simp only [expectation_apply, restrictedDensity, ← mul_div_assoc, ← Finset.sum_div]
  exact div_self hpos.ne'

/-- Converting conditional densities back to event probabilities is exact. -/
theorem conditional_eventMass (p : FiniteDist Ω) (feature : Ω → C)
    (event : Ω → Prop) (c : C) :
    eventMass p (fun x => feature x = c ∧ event x) =
      conditional p feature (eventIndicator event) c / Fintype.card C := by
  rw [conditional_apply]
  have hC : (Fintype.card C : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [mul_div_cancel_left₀ _ hC]
  unfold eventMass
  apply congrArg (expectation p)
  funext x
  simp only [eventIndicator]
  split_ifs <;> simp_all

/-- The exact surviving-fiber mass follows from the conditional deletion probability. -/
theorem survivingFiber_mass (p : FiniteDist Ω) (feature : Ω → C)
    (hfeature : p.map feature = FiniteDist.uniform C) (safe : Ω → Prop) (mark : C) :
    eventMass p (fun x => feature x = mark ∧ safe x) =
      (1 - conditional p feature (badIndicator safe) mark) / Fintype.card C := by
  rw [conditional_eventMass]
  have he : eventIndicator safe = (fun _ => (1 : ℝ)) - badIndicator safe := by
    funext x
    simp only [eventIndicator, badIndicator, Pi.sub_apply]
    split_ifs <;> norm_num
  rw [he, map_sub]
  have hc := conditional_same p feature hfeature (fun _ : C => (1 : ℝ))
  change conditional p feature (fun _ => (1 : ℝ)) = (fun _ => 1) at hc
  rw [hc]
  rfl

/-- Uniform pairwise independence supplies the exact two-feature atom probability. -/
theorem pair_eventMass (p : FiniteDist Ω) (first second : Ω → C)
    (hpair : p.map (fun x => (first x, second x)) =
      (FiniteDist.uniform C).prod (FiniteDist.uniform C)) (a b : C) :
    eventMass p (fun x => first x = a ∧ second x = b) =
      (Fintype.card C : ℝ)⁻¹ * (Fintype.card C : ℝ)⁻¹ := by
  have h := congrArg (fun law : FiniteDist (C × C) => law.weight (a, b)) hpair
  simpa [eventMass, expectation_apply, eventIndicator, FiniteDist.map_weight,
    FiniteDist.prod_weight, FiniteDist.uniform_weight, Prod.mk.injEq, mul_ite] using h

omit [Nonempty C] in
/-- A marginal of a restricted density is a joint-event mass divided by the
actual restriction mass, with the uniform feature normalization. -/
theorem conditional_restrictedDensity (p : FiniteDist Ω) (feature : Ω → C)
    (event : Ω → Prop) (c : C) :
    conditional p feature (restrictedDensity p event) c =
      (Fintype.card C : ℝ) * eventMass p (fun x => feature x = c ∧ event x) /
        eventMass p event := by
  rw [conditional_apply]
  have he : (fun x => if feature x = c then restrictedDensity p event x else (0 : ℝ)) =
      fun x => eventIndicator (fun y => feature y = c ∧ event y) x / eventMass p event := by
    funext x
    simp only [restrictedDensity, eventIndicator]
    split_ifs <;> simp_all
  rw [he]
  simp only [expectation_apply, ← mul_div_assoc, ← Finset.sum_div, eventMass]

omit [Fintype J] in
/-- The true surviving marked fiber is a probability density, emits the mark
exactly, and has all other conditional marginal densities bounded by two. -/
theorem surviving_fiber_density (p : FiniteDist Ω) (first : Ω → C)
    (hfirst : p.map first = FiniteDist.uniform C)
    (others : J → Ω → C)
    (hpair : ∀ j, p.map (fun x => (first x, others j x)) =
      (FiniteDist.uniform C).prod (FiniteDist.uniform C))
    (safe : Ω → Prop) (mark : C)
    (hbad : conditional p first (badIndicator safe) mark ≤ 1 / 2) :
    ∃ spike : Ω → ℝ,
      expectation p spike = 1 ∧ (∀ x, 0 ≤ spike x) ∧
      (∀ x, ¬ (first x = mark ∧ safe x) → spike x = 0) ∧
      (∀ c, conditional p first spike c =
        if c = mark then (Fintype.card C : ℝ) else 0) ∧
      (∀ j c, conditional p (others j) spike c ≤ 2) := by
  let event := fun x => first x = mark ∧ safe x
  have hC : 0 < (Fintype.card C : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hmass := survivingFiber_mass p first hfirst safe mark
  have hpos : 0 < eventMass p event := by
    rw [hmass]
    exact div_pos (by linarith) hC
  let spike := restrictedDensity p event
  have hmean : expectation p spike = 1 := restrictedDensity_mean p event hpos
  have hzero : ∀ x, ¬ event x → spike x = 0 := by
    intro x hx
    simp [spike, restrictedDensity, eventIndicator, hx]
  refine ⟨spike, hmean, restrictedDensity_nonneg p event, hzero, ?_, ?_⟩
  · intro c
    rw [conditional_apply]
    by_cases hc : c = mark
    · subst c
      have heq : (fun x => if first x = mark then spike x else (0 : ℝ)) = spike := by
        funext x
        by_cases hx : first x = mark
        · simp [hx]
        · simp [hx, hzero x (by simp [event, hx])]
      rw [heq, hmean, if_pos rfl, mul_one]
    · have heq : (fun x => if first x = c then spike x else (0 : ℝ)) = 0 := by
        funext x
        by_cases hx : first x = c
        · have hn : ¬ event x := by rintro ⟨hm, _⟩; exact hc (hx.symm.trans hm)
          simp [hx, hzero x hn]
        · simp [hx]
      rw [heq, map_zero, mul_zero, if_neg hc]
  · intro j c
    rw [conditional_restrictedDensity]
    have hnum : eventMass p (fun x => others j x = c ∧ event x) ≤
        (Fintype.card C : ℝ)⁻¹ * (Fintype.card C : ℝ)⁻¹ := by
      rw [← pair_eventMass p first (others j) (hpair j) mark c]
      apply expectation_mono
      intro x
      unfold eventIndicator
      split_ifs with ht hf
      · exact le_rfl
      · exact False.elim (hf ⟨ht.2.1, ht.1⟩)
      · norm_num
      · norm_num
    apply (div_le_iff₀ hpos).mpr
    have hm : 1 / 2 ≤ (Fintype.card C : ℝ) * eventMass p event := by
      rw [hmass]
      field_simp
      linarith
    have hn := mul_le_mul_of_nonneg_left hnum hC.le
    have hcancel : (Fintype.card C : ℝ) *
        ((Fintype.card C : ℝ)⁻¹ * (Fintype.card C : ℝ)⁻¹) = (Fintype.card C : ℝ)⁻¹ := by
      field_simp
    rw [hcancel] at hn
    have hl : (Fintype.card C : ℝ)⁻¹ ≤ 2 * eventMass p event := by
      nlinarith [mul_inv_cancel₀ hC.ne']
    exact hn.trans hl

end RestrictedFiber
section SpikeRepair
variable {Ω C I : Type*} [Fintype Ω] [Fintype C] [Nonempty C] [Fintype I]

/-- The complete projection fixes each of its feature components. -/
theorem combinedProjection_feature (p : FiniteDist Ω)
    (features : I → Ω → C) (allowed : I → Finset C)
    (hfeature : ∀ i, p.map (features i) = FiniteDist.uniform C)
    (hpair : ∀ i j, i ≠ j → p.map (fun x => (features i x, features j x)) =
      (FiniteDist.uniform C).prod (FiniteDist.uniform C)) (i : I) (f : Ω → ℝ) :
    combinedProjection p features allowed (featureProjection p (features i) (allowed i) f) =
      featureProjection p (features i) (allowed i) f := by
  have hcomp (j : I) : featureProjection p (features j) (allowed j)
      (featureProjection p (features i) (allowed i) f) =
      if j = i then featureProjection p (features i) (allowed i) f else 0 := by
    by_cases hij : j = i
    · subst j
      simpa using congrArg (fun L : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) => L f)
        (featureProjection_idempotent p (features i) (hfeature i) (allowed i))
    · rw [if_neg hij]
      exact congrArg (fun L : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) => L f)
        (featureProjection_orthogonal p (features j) (features i) (hpair j i hij)
          (allowed j) (allowed i))
  simp only [combinedProjection, LinearMap.add_apply, LinearMap.sum_apply]
  have hc : constantProjection p (featureProjection p (features i) (allowed i) f) = 0 := by
    funext x
    exact featureProjection_mean p (features i) (hfeature i) (allowed i) f
  rw [hc]
  simp only [hcomp, Finset.sum_ite_eq', Finset.mem_univ, if_true, zero_add]

/-- The exact defect used in V7: no correction is demanded on the marked feature. -/
noncomputable def spikeDefect (p : FiniteDist Ω) (features : I → Ω → C)
    (allowed : I → Finset C) (zero : I) (atom : ℝ) (spike : Ω → ℝ) : Ω → ℝ :=
  atom • ∑ i, if i = zero then 0 else featureProjection p (features i) (allowed i) spike

/-- The defect has no mass component. -/
theorem spikeDefect_mean (p : FiniteDist Ω) (features : I → Ω → C)
    (allowed : I → Finset C) (zero : I) (atom : ℝ) (spike : Ω → ℝ)
    (hfeature : ∀ i, p.map (features i) = FiniteDist.uniform C) :
    expectation p (spikeDefect p features allowed zero atom spike) = 0 := by
  rw [spikeDefect, map_smul, map_sum]
  have h (i : I) : expectation p
      (if i = zero then 0 else featureProjection p (features i) (allowed i) spike) = 0 := by
    split_ifs
    · exact map_zero _
    · exact featureProjection_mean p (features i) (hfeature i) (allowed i) spike
  simp only [h, Finset.sum_const_zero, smul_zero]

/-- The defect belongs to the concrete projection's range. -/
theorem spikeDefect_projected (p : FiniteDist Ω) (features : I → Ω → C)
    (allowed : I → Finset C) (zero : I) (atom : ℝ) (spike : Ω → ℝ)
    (hfeature : ∀ i, p.map (features i) = FiniteDist.uniform C)
    (hpair : ∀ i j, i ≠ j → p.map (fun x => (features i x, features j x)) =
      (FiniteDist.uniform C).prod (FiniteDist.uniform C)) :
    combinedProjection p features allowed (spikeDefect p features allowed zero atom spike) =
      spikeDefect p features allowed zero atom spike := by
  rw [spikeDefect, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs
  · exact map_zero _
  · exact combinedProjection_feature p features allowed hfeature hpair i spike

/-- Every non-marked response is precisely the atom-weighted spike response,
while the marked feature's response is exactly zero. -/
theorem spikeDefect_component (p : FiniteDist Ω) (features : I → Ω → C)
    (allowed : I → Finset C) (zero : I) (atom : ℝ) (spike : Ω → ℝ)
    (hfeature : ∀ i, p.map (features i) = FiniteDist.uniform C)
    (hpair : ∀ i j, i ≠ j → p.map (fun x => (features i x, features j x)) =
      (FiniteDist.uniform C).prod (FiniteDist.uniform C)) (i : I) :
    featureProjection p (features i) (allowed i) (spikeDefect p features allowed zero atom spike) =
      if i = zero then 0 else atom • featureProjection p (features i) (allowed i) spike := by
  rw [spikeDefect, map_smul, map_sum]
  have hs : (∑ j, featureProjection p (features i) (allowed i)
      (if j = zero then 0 else featureProjection p (features j) (allowed j) spike)) =
      if i = zero then 0 else featureProjection p (features i) (allowed i) spike := by
    rw [Finset.sum_eq_single i]
    · by_cases hi : i = zero
      · simp [hi]
      · rw [if_neg hi]
        exact congrArg (fun L : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) => L spike)
          (featureProjection_idempotent p (features i) (hfeature i) (allowed i))
    · intro j _ hji
      by_cases hj : j = zero
      · simp [hj]
      · rw [if_neg hj]
        exact congrArg (fun L : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) => L spike)
          (featureProjection_orthogonal p (features i) (features j) (hpair i j hji.symm)
            (allowed i) (allowed j))
    · simp
  rw [hs]
  split_ifs <;> simp

omit [Nonempty C] in
/-- A spike with marginal density at most two gives component norm at most four. -/
theorem spike_component_norm (p : FiniteDist Ω) (feature : Ω → C) (allowed : Finset C)
    (spike : Ω → ℝ) (hspike : ∀ x, 0 ≤ spike x)
    (hbound : ∀ c, conditional p feature spike c ≤ 2) :
    ‖featureProjection p feature allowed spike‖ ≤ 4 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
  intro x
  change |centerAllowed allowed (conditional p feature spike) (feature x)| ≤ 4
  have hnonneg (c : C) : 0 ≤ conditional p feature spike c := by
    rw [conditional_apply]
    apply mul_nonneg (Nat.cast_nonneg _)
    exact Finset.sum_nonneg (fun y _ => mul_nonneg (p.nonneg y)
      (by dsimp only; split_ifs <;> simp [hspike]))
  have hc (c : C) (_ : c ∈ allowed) : |conditional p feature spike c| ≤ 2 := by
    rw [abs_of_nonneg (hnonneg c)]
    exact hbound c
  convert centerAllowed_abs_le allowed _ 2 (by norm_num) hc (feature x) using 1
  norm_num

omit [Nonempty C] in
/-- The actual atom budget gives the `1/25` defect required by positive repair. -/
theorem spikeDefect_norm (p : FiniteDist Ω) (features : I → Ω → C)
    (allowed : I → Finset C) (zero : I) (atom : ℝ) (spike : Ω → ℝ)
    (hatom : 0 ≤ atom) (hspike : ∀ x, 0 ≤ spike x)
    (hbound : ∀ i, i ≠ zero → ∀ c, conditional p (features i) spike c ≤ 2)
    (hsize : 4 * atom * Fintype.card I ≤ 1 / 25) :
    ‖spikeDefect p features allowed zero atom spike‖ ≤ 1 / 25 := by
  have hnorm (i : I) : ‖(if i = zero then 0 else
      featureProjection p (features i) (allowed i) spike)‖ ≤ (4 : ℝ) := by
    split_ifs with hi
    · exact (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)).mpr
        (fun x => by change ‖(0 : ℝ)‖ ≤ 4; norm_num)
    · exact spike_component_norm p (features i) (allowed i) spike hspike (hbound i hi)
  rw [spikeDefect, norm_smul, Real.norm_eq_abs, abs_of_nonneg hatom]
  calc
    _ ≤ atom * ∑ i, ‖(if i = zero then 0 else
        featureProjection p (features i) (allowed i) spike)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) hatom
    _ ≤ atom * ∑ _i : I, (4 : ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hnorm i)) hatom
    _ ≤ 1 / 25 := by simpa [mul_assoc, mul_comm, mul_left_comm] using hsize

omit [Fintype C] [Nonempty C] in
/-- A constant profile on the allowed palette is killed by its centering operator. -/
theorem centerAllowed_masked_const (allowed : Finset C) (r : ℝ) :
    centerAllowed allowed (fun c => if c ∈ allowed then r else 0) = 0 := by
  funext c
  rw [centerAllowed_apply]
  by_cases hc : c ∈ allowed
  · have hcard : (allowed.card : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨c, hc⟩)
    simp only [if_pos hc, Finset.sum_ite_of_true (fun a ha => ha)]
    simp [hcard]
  · simp [hc]

/-- A zero feature component, palette support and the total density mass
already determine the complete conditional marginal. -/
theorem component_zero_marginal (p : FiniteDist Ω) (feature : Ω → C)
    (hfeature : p.map feature = FiniteDist.uniform C) (allowed : Finset C) (f : Ω → ℝ)
    (hcomponent : featureProjection p feature allowed f = 0)
    (hsupport : ∀ c ∉ allowed, conditional p feature f c = 0) (c : C) :
    conditional p feature f c =
      if c ∈ allowed then (Fintype.card C : ℝ) * expectation p f / allowed.card else 0 := by
  have hc := congrArg (conditional p feature) hcomponent
  change conditional p feature (fun x => centerAllowed allowed (conditional p feature f)
    (feature x)) = conditional p feature 0 at hc
  rw [conditional_same p feature hfeature, map_zero] at hc
  rw [centerAllowed_zero_profile allowed _ hc hsupport c, conditional_sum]

/-- A positive repaired interior branch preserves the marked feature's
uniform marginal and cancels the spike's responses on every other feature.
Mixing this branch with the spike using an independent Bernoulli atom therefore
has the exact marginal specification of the boundary-chart lemma. -/
theorem marked_repaired_density [Nonempty Ω] (p : FiniteDist Ω)
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
    (hspikebound : ∀ i, i ≠ zero → ∀ c, conditional p (features i) spike c ≤ 2) :
    ∃ repaired : Ω → ℝ,
      expectation p repaired = 1 ∧ (∀ x, 0 ≤ repaired x) ∧
      (∀ x, ¬ safe x → repaired x = 0) ∧
      (∀ c, conditional p (features zero) repaired c =
        if c ∈ allowed zero then (Fintype.card C : ℝ) / (allowed zero).card else 0) ∧
      (∀ i, i ≠ zero → ∀ c,
        conditional p (features i) ((1 - atom) • repaired + atom • spike) c =
          if c ∈ allowed i then (Fintype.card C : ℝ) / (allowed i).card else 0) := by
  obtain ⟨base, hbasemean, hbase, hbasezero, hbaselower, hbasemarg⟩ :=
    positive_chart_density p features allowed hfeature hpair safe hallowed ε hε hglobal hconditional hsmall
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
  refine ⟨repaired, hrmean, hrnonneg, hrzero, ?_, ?_⟩
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

end SpikeRepair
section AffineMarkedChart
variable {F I : Type*} [Field F] [Fintype F] [Fintype I]

/-- The complete marked affine-chart construction.  The output law is explicitly
a Bernoulli mixture of two positive probability laws.  The interior branch keeps
all features trimmed; the spike branch emits the prescribed distinguished mark
and keeps every other feature trimmed. -/
theorem affine_marked_chart (inputs : I → F × F) (hinj : Function.Injective inputs)
    (allowed : I → Finset F) (zero : I) (mark : F)
    (hsmall : (2 * Fintype.card I + 1) * affineDeletionBudget allowed ≤ 1 / 4)
    (atom : ℝ) (hatom : 0 ≤ atom) (hatom100 : atom ≤ 1 / 100)
    (hsize : 4 * atom * Fintype.card I ≤ 1 / 25) :
    ∃ interior spike law : FiniteDist (Chart F),
      (∀ chart, law.weight chart =
        (1 - atom) * interior.weight chart + atom * spike.weight chart) ∧
      (∀ chart, ¬ (chart.2.1 ≠ 0 ∧
        ∀ i, feature (inputs i).1 (inputs i).2 chart ∈ allowed i) → interior.weight chart = 0) ∧
      (∀ chart, ¬ (feature (inputs zero).1 (inputs zero).2 chart = mark ∧ chart.2.1 ≠ 0 ∧
        ∀ i, i ≠ zero → feature (inputs i).1 (inputs i).2 chart ∈ allowed i) → spike.weight chart = 0) ∧
      (∀ c, (law.map (feature (inputs zero).1 (inputs zero).2)).weight c =
        (1 - atom) * (if c ∈ allowed zero then ((allowed zero).card : ℝ)⁻¹ else 0) +
          atom * (if c = mark then 1 else 0)) ∧
      (∀ i, i ≠ zero → ∀ c, (law.map (feature (inputs i).1 (inputs i).2)).weight c =
        if c ∈ allowed i then ((allowed i).card : ℝ)⁻¹ else 0) := by
  let p := FiniteDist.uniform (Chart F)
  let features := fun i => feature (inputs i).1 (inputs i).2
  let auxiliary := fun chart : Chart F => chart.2.1
  let auxAllowed := Finset.univ.erase (0 : F)
  let safe := legalChart auxiliary auxAllowed features allowed
  let otherAllowed := fun i => if i = zero then Finset.univ else allowed i
  let otherSafe := legalChart auxiliary auxAllowed features otherAllowed
  have hfeature (i : I) : p.map (features i) = FiniteDist.uniform F := feature_uniform _ _
  have hpair (i j : I) (hij : i ≠ j) : p.map (fun x => (features i x, features j x)) =
      (FiniteDist.uniform F).prod (FiniteDist.uniform F) :=
    feature_pair_uniform (inputs i) (inputs j) (fun h => hij (hinj h))
  have hauxpair (i : I) : p.map (fun x => (features i x, auxiliary x)) =
      (FiniteDist.uniform F).prod (FiniteDist.uniform F) := feature_scale_uniform _ _
  have hbudget : expectation (FiniteDist.uniform F) (paletteFailure auxAllowed) +
      ∑ i, expectation (FiniteDist.uniform F) (paletteFailure (allowed i)) =
        affineDeletionBudget allowed := by
    change expectation (FiniteDist.uniform F) (paletteFailure (Finset.univ.erase (0 : F))) + _ = _
    rw [nonzero_palette_failure]
    simp only [uniform_palette_failure, affineDeletionBudget]
  have hglobal : expectation p (badIndicator safe) ≤ affineDeletionBudget allowed := by
    rw [← hbudget]
    exact legalChart_global_budget p auxiliary auxAllowed features allowed scale_uniform hfeature
  have hconditional : ∀ i c, c ∈ allowed i →
      conditional p (features i) (badIndicator safe) c ≤ affineDeletionBudget allowed := by
    intro i c hc
    rw [← hbudget]
    exact legalChart_conditional_budget p auxiliary auxAllowed features allowed hfeature hpair hauxpair i c hc
  have hε : 0 ≤ affineDeletionBudget allowed := by
    apply le_trans _ hglobal
    exact Finset.sum_nonneg (fun x _ => mul_nonneg (p.nonneg x)
      (by unfold badIndicator; split_ifs <;> norm_num))
  have hεhalf : affineDeletionBudget allowed ≤ 1 / 2 := by
    have hcard : 0 ≤ (Fintype.card I : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg hcard hε]
  have hotherBudget : expectation (FiniteDist.uniform F) (paletteFailure auxAllowed) +
      ∑ i, expectation (FiniteDist.uniform F) (paletteFailure (otherAllowed i)) ≤
        affineDeletionBudget allowed := by
    rw [← hbudget]
    apply add_le_add_right
    apply Finset.sum_le_sum
    intro i _
    apply expectation_mono
    intro c
    by_cases hi : i = zero
    · simp [otherAllowed, hi, paletteFailure]
      split_ifs <;> norm_num
    · simp [otherAllowed, hi]
  have hbad : conditional p (features zero) (badIndicator otherSafe) mark ≤ 1 / 2 := by
    have hb := legalChart_conditional_budget p auxiliary auxAllowed features otherAllowed
      hfeature hpair hauxpair zero mark (by simp [otherAllowed])
    exact hb.trans (hotherBudget.trans hεhalf)
  let others := fun i : {i : I // i ≠ zero} => features i.1
  obtain ⟨spikeDensity, hspikemean, hspikenonneg, hspikezero, hspikemarg, hspikebound⟩ :=
    surviving_fiber_density p (features zero) (hfeature zero) others
      (fun i => hpair zero i.1 i.2.symm) otherSafe mark hbad
  have hsallowed (i : I) (hi : i ≠ zero) (x : Chart F) (hx : features i x ∉ allowed i) :
      spikeDensity x = 0 := by
    apply hspikezero
    intro hs
    have hg := hs.2.2 i
    exact hx (by simpa [otherAllowed, hi] using hg)
  obtain ⟨repaired, hrmean, hrnonneg, hrzero, hrfirst, hrothers⟩ :=
    marked_repaired_density p features allowed zero hfeature hpair safe
      (fun i x hx => hx.2 i) (affineDeletionBudget allowed) hε hglobal hconditional hsmall
      atom hatom hatom100 hsize spikeDensity hspikemean hspikenonneg hsallowed
      (fun i hi c => hspikebound ⟨i, hi⟩ c)
  let final := (1 - atom) • repaired + atom • spikeDensity
  have hfmean : expectation p final = 1 := by
    simp only [final, map_add, map_smul, hrmean, hspikemean, smul_eq_mul, mul_one]
    ring
  have hfnonneg (x : Chart F) : 0 ≤ final x := by
    exact add_nonneg (mul_nonneg (by linarith) (hrnonneg x))
      (mul_nonneg hatom (hspikenonneg x))
  refine ⟨densityLaw p repaired hrnonneg hrmean,
    densityLaw p spikeDensity hspikenonneg hspikemean,
    densityLaw p final hfnonneg hfmean, ?_, ?_, ?_, ?_, ?_⟩
  · intro chart
    change p.weight chart * ((1 - atom) * repaired chart + atom * spikeDensity chart) = _
    simp only [densityLaw]
    ring
  · intro chart hbad
    have hn : ¬ safe chart := by
      simpa [safe, legalChart, auxiliary, auxAllowed, features] using hbad
    simp [densityLaw, hrzero chart hn]
  · intro chart hbad
    have hn : ¬ (features zero chart = mark ∧ otherSafe chart) := by
      intro hs
      apply hbad
      refine ⟨hs.1, ?_, ?_⟩
      · simpa [auxiliary, auxAllowed] using hs.2.1
      · intro i hi
        simpa [features, otherAllowed, hi] using hs.2.2 i
    simp [densityLaw, hspikezero chart hn]
  · intro c
    rw [densityLaw_marginal]
    change conditional p (features zero) ((1 - atom) • repaired + atom • spikeDensity) c /
      Fintype.card F = _
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hrfirst, hspikemarg]
    have hF : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    split_ifs <;> field_simp
    all_goals ring
  · intro i hi c
    rw [densityLaw_marginal, hrothers i hi c]
    have hF : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    split_ifs <;> field_simp
    all_goals ring

/-- The exact public atom weight chosen in V7. -/
noncomputable def chartAtom (I : Type*) [Fintype I] : ℝ :=
  (100 * (Fintype.card I : ℝ))⁻¹

/-- No separate atom-smallness assumptions are needed for the paper's choice. -/
theorem chartAtom_bounds (zero : I) :
    0 ≤ chartAtom I ∧ chartAtom I ≤ 1 / 100 ∧
      4 * chartAtom I * Fintype.card I ≤ 1 / 25 := by
  letI : Nonempty I := ⟨zero⟩
  have hI : 0 < (Fintype.card I : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hI1 : (1 : ℝ) ≤ Fintype.card I := by exact_mod_cast Fintype.card_pos
  unfold chartAtom
  refine ⟨by positivity, ?_, ?_⟩
  · rw [← one_div]
    apply (div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 100)).mpr
    nlinarith
  · field_simp
    norm_num

end AffineMarkedChart
end BoundaryCalibration
end AFT
