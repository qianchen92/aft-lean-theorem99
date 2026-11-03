import AFT.BoundarySpike

/-!
# The current simultaneous flag and affine-map calibration

The marked branch is allowed on an entire set of protected inputs.  In
particular this is not the older one-feature, small-atom chart theorem.
The deletion operator below is the actual masked feature projection.  Its
inverse is controlled by the manuscript's one-sided marked-defect budget.
-/

namespace CurrentAFT.AffineFlagCalibration

open AFT AFT.BoundaryCalibration
open scoped BigOperators Classical

noncomputable section

variable {Ω C I : Type*} [Fintype Ω] [Fintype C] [Fintype I]

/-- The exact geometric bound, with a variable contraction budget. -/
theorem solve_sub_norm_le (D : (Ω → ℝ) →L[ℝ] (Ω → ℝ))
    (hD : ‖D‖ < 1) (b : ℝ) (hb : b < 1) (hDb : ‖D‖ ≤ b)
    (f : Ω → ℝ) :
    ‖neumannSolve D hD f - f‖ ≤ b / (1 - b) * ‖f‖ := by
  let h := neumannSolve D hD f
  have heq : h - f = D h := by
    have hs := neumannSolve_equation D hD f
    change h - D h = f at hs
    rw [← hs]
    abel
  have htri : ‖h‖ ≤ ‖h - f‖ + ‖f‖ := by
    simpa only [sub_add_cancel] using norm_add_le (h - f) f
  have hop : ‖h - f‖ ≤ b * ‖h‖ := by
    rw [heq]
    exact (D.le_opNorm h).trans
      (mul_le_mul_of_nonneg_right hDb (norm_nonneg _))
  have hb0 : 0 ≤ b := (norm_nonneg D).trans hDb
  have hh : (1 - b) * ‖h - f‖ ≤ b * ‖f‖ := by
    nlinarith [mul_le_mul_of_nonneg_left htri hb0]
  change ‖h - f‖ ≤ _
  rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith : 0 < 1 - b)]
  nlinarith

/-- A one-sided defect estimate survives the actual inverse. -/
theorem solve_pointwise_upper (D : (Ω → ℝ) →L[ℝ] (Ω → ℝ))
    (hD : ‖D‖ < 1) (b : ℝ) (hb : b < 1) (hDb : ‖D‖ ≤ b)
    (f : Ω → ℝ) (upper magnitude : ℝ)
    (hf : ∀ x, f x ≤ upper) (hnorm : ‖f‖ ≤ magnitude) (x : Ω) :
    neumannSolve D hD f x ≤ upper + b / (1 - b) * magnitude := by
  have hb0 : 0 ≤ b := (norm_nonneg D).trans hDb
  have hpoint := (norm_le_pi_norm (neumannSolve D hD f - f) x).trans
    (solve_sub_norm_le D hD b hb hDb f)
  change |neumannSolve D hD f x - f x| ≤ _ at hpoint
  have hm := mul_le_mul_of_nonneg_left hnorm
    (div_nonneg hb0 (by linarith : 0 ≤ 1 - b))
  linarith [(abs_le.mp hpoint).2, hf x]

/-- The density correction deliberately leaves every marked-line component
unchanged, rather than only one distinguished input. -/
def offLineDefect (p : FiniteDist Ω) (features : I → Ω → C)
    (allowed : I → Finset C) (line : I → Prop) (spike : Ω → ℝ) : Ω → ℝ :=
  ∑ i, if line i then 0 else featureProjection p (features i) (allowed i) spike

theorem offLineDefect_mean [Nonempty C] (p : FiniteDist Ω)
    (features : I → Ω → C) (allowed : I → Finset C) (line : I → Prop)
    (spike : Ω → ℝ)
    (hfeature : ∀ i, p.map (features i) = FiniteDist.uniform C) :
    expectation p (offLineDefect p features allowed line spike) = 0 := by
  rw [offLineDefect, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  split_ifs
  · exact map_zero _
  · exact featureProjection_mean p _ (hfeature i) _ spike

theorem offLineDefect_projected [Nonempty C] (p : FiniteDist Ω)
    (features : I → Ω → C) (allowed : I → Finset C) (line : I → Prop)
    (spike : Ω → ℝ)
    (hfeature : ∀ i, p.map (features i) = FiniteDist.uniform C)
    (hpair : ∀ i j, i ≠ j → p.map (fun x => (features i x, features j x)) =
      (FiniteDist.uniform C).prod (FiniteDist.uniform C)) :
    combinedProjection p features allowed (offLineDefect p features allowed line spike) =
      offLineDefect p features allowed line spike := by
  rw [offLineDefect, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs
  · exact map_zero _
  · exact combinedProjection_feature p features allowed hfeature hpair i spike

theorem offLineDefect_component [Nonempty C] (p : FiniteDist Ω)
    (features : I → Ω → C) (allowed : I → Finset C) (line : I → Prop)
    (spike : Ω → ℝ)
    (hfeature : ∀ i, p.map (features i) = FiniteDist.uniform C)
    (hpair : ∀ i j, i ≠ j → p.map (fun x => (features i x, features j x)) =
      (FiniteDist.uniform C).prod (FiniteDist.uniform C)) (i : I) :
    featureProjection p (features i) (allowed i)
      (offLineDefect p features allowed line spike) =
      if line i then 0 else featureProjection p (features i) (allowed i) spike := by
  rw [offLineDefect, map_sum, Finset.sum_eq_single i]
  · split_ifs
    · exact map_zero _
    · exact congrArg (fun L : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) => L spike)
        (featureProjection_idempotent p (features i) (hfeature i) (allowed i))
  · intro j _ hji
    split_ifs
    · exact map_zero _
    · exact congrArg (fun L : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) => L spike)
        (featureProjection_orthogonal p (features i) (features j) (hpair i j hji.symm)
          (allowed i) (allowed j))
  · simp

/-- A normalized supported color density has average at least one on its
allowed palette.  This is the extra one-sided gain needed at atom `1/2`. -/
theorem centered_palette_bounds [Nonempty C] (allowed : Finset C)
    (g : C → ℝ) (M : ℝ) (hM : 1 ≤ M)
    (hg0 : ∀ c, 0 ≤ g c) (hgM : ∀ c, g c ≤ M)
    (hzero : ∀ c ∉ allowed, g c = 0)
    (hsum : ∑ c, g c = Fintype.card C) (c : C) :
    |centerAllowed allowed g c| ≤ M ∧ centerAllowed allowed g c ≤ M - 1 := by
  have hsumA : ∑ a ∈ allowed, g a = (Fintype.card C : ℝ) := by
    rw [← hsum]
    exact Finset.sum_subset (Finset.subset_univ _) (fun a _ ha => hzero a ha)
  have hcard : 0 < allowed.card := by
    by_contra hn
    have he : allowed = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [he] at hsumA
    simp only [Finset.sum_empty] at hsumA
    exact (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) hsumA.symm
  have hcR : (0 : ℝ) < allowed.card := Nat.cast_pos.mpr hcard
  have havg1 : 1 ≤ (∑ a ∈ allowed, g a) / allowed.card := by
    rw [hsumA, le_div_iff₀ hcR, one_mul]
    exact_mod_cast (Finset.card_le_card (Finset.subset_univ allowed))
  have havgM : (∑ a ∈ allowed, g a) / allowed.card ≤ M := by
    apply (div_le_iff₀ hcR).mpr
    calc
      _ ≤ ∑ _a ∈ allowed, M := Finset.sum_le_sum (fun a _ => hgM a)
      _ = _ := by simp; ring
  rw [centerAllowed_apply]
  split_ifs with hc
  · constructor
    · apply abs_le.mpr
      constructor <;> linarith [hg0 c, hgM c]
    · linarith [hgM c]
  · exact ⟨by simpa using (le_trans (by norm_num : (0 : ℝ) ≤ 1) hM), by linarith⟩

/-- The manuscript's two separate bounds: the upper defect is smaller by the
deleted fraction, while its absolute norm may be of order the input count. -/
theorem offLineDefect_bounds [Nonempty Ω] [Nonempty C] (p : FiniteDist Ω)
    (features : I → Ω → C) (allowed : I → Finset C) (line : I → Prop)
    (spike : Ω → ℝ) (hmean : expectation p spike = 1)
    (hspike : ∀ x, 0 ≤ spike x)
    (hallowed : ∀ i, ¬ line i → ∀ x, features i x ∉ allowed i → spike x = 0)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hbound : ∀ i, ¬ line i → ∀ c, conditional p (features i) spike c ≤ 1 / (1 - δ)) :
    ‖offLineDefect p features allowed line spike‖ ≤ Fintype.card I / (1 - δ) ∧
      ∀ x, offLineDefect p features allowed line spike x ≤
        Fintype.card I * δ / (1 - δ) := by
  have hM : 1 ≤ 1 / (1 - δ) := by
    apply (le_div_iff₀ (by linarith : 0 < 1 - δ)).mpr
    linarith
  have hcomp (i : I) (hi : ¬ line i) (x : Ω) :
      |featureProjection p (features i) (allowed i) spike x| ≤ 1 / (1 - δ) ∧
      featureProjection p (features i) (allowed i) spike x ≤ 1 / (1 - δ) - 1 := by
    apply centered_palette_bounds (allowed i) (conditional p (features i) spike) _ hM
    · intro c
      rw [conditional_apply, expectation_apply]
      apply mul_nonneg (Nat.cast_nonneg _)
      apply Finset.sum_nonneg
      intro a _
      exact mul_nonneg (p.nonneg a) (by split_ifs; exacts [hspike a, le_rfl])
    · exact hbound i hi
    · intro c hc
      exact conditional_outside_zero p (features i) (allowed i)
        (fun x => features i x ∈ allowed i) spike
        (fun x hx => hallowed i hi x hx) (fun _ hx => hx) c hc
    · rw [conditional_sum, hmean, mul_one]
  have habs (x : Ω) : |offLineDefect p features allowed line spike x| ≤
      (Fintype.card I : ℝ) * (1 / (1 - δ)) := by
    rw [offLineDefect, Finset.sum_apply]
    calc
      _ ≤ ∑ i : I, |(if line i then 0 else
          featureProjection p (features i) (allowed i) spike) x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : I, (1 / (1 - δ) : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : line i
        · simp only [if_pos hi, Pi.zero_apply, abs_zero]; positivity
        · simpa only [if_neg hi] using (hcomp i hi x).1
      _ = _ := by simp
  constructor
  · rw [← mul_one_div]
    exact (pi_norm_le_iff_of_nonneg (by positivity)).mpr habs
  · intro x
    rw [offLineDefect, Finset.sum_apply]
    calc
      _ ≤ ∑ _i : I, (1 / (1 - δ) - 1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : line i
        · simp only [if_pos hi, Pi.zero_apply]; linarith
        · simpa only [if_neg hi] using (hcomp i hi x).2
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp [show 1 - δ ≠ 0 by linarith]
        ring

/- The current positive regular branch, simultaneously calibrated at every
protected input.  Only concrete deletion probabilities and marked color
counts are premises; invertibility and positivity are conclusions. -/
/-- The exact regular-branch witness. Its formula is public and contains
no hidden protected input. The proof argument only certifies the already
computed finite deletion response. -/
def regularDensity (p : FiniteDist Ω) (features : I → Ω → C)
    (allowed : I → Finset C) (line : I → Prop) (safe : Ω → Prop) [DecidablePred safe]
    (atom : ℝ) (spike : Ω → ℝ)
    (hD : ‖deletion (chartProjection p features allowed) safe‖ < 1) : Ω → ℝ :=
  safeMask safe (neumannSolve (deletion (chartProjection p features allowed) safe) hD
    (1 - (atom / (1 - atom)) • offLineDefect p features allowed line spike))

theorem regularDensity_properties [Nonempty Ω] [Nonempty C] (p : FiniteDist Ω)
    (features : I → Ω → C) (allowed : I → Finset C) (line : I → Prop)
    (hfeature : ∀ i, p.map (features i) = FiniteDist.uniform C)
    (hpair : ∀ i j, i ≠ j → p.map (fun x => (features i x, features j x)) =
      (FiniteDist.uniform C).prod (FiniteDist.uniform C))
    (safe : Ω → Prop) [DecidablePred safe]
    (hallowed : ∀ i x, safe x → features i x ∈ allowed i)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hglobal : expectation p (badIndicator safe) ≤ δ)
    (hconditional : ∀ i c, c ∈ allowed i →
      conditional p (features i) (badIndicator safe) c ≤ δ)
    (hsmall : (2 * Fintype.card I + 1) * δ ≤ 1 / 4)
    (hpositivity : (Fintype.card I : ℝ) / (1 - δ) *
      (δ + ((2 * Fintype.card I + 1) * δ) /
        (1 - (2 * Fintype.card I + 1) * δ)) ≤ 1 / 3)
    (atom : ℝ) (ha0 : 0 ≤ atom) (haHalf : atom ≤ 1 / 2)
    (spike : Ω → ℝ) (hsmean : expectation p spike = 1)
    (hsnonneg : ∀ x, 0 ≤ spike x)
    (hsallowed : ∀ i, ¬ line i → ∀ x, features i x ∉ allowed i → spike x = 0)
    (hsbound : ∀ i, ¬ line i → ∀ c,
      conditional p (features i) spike c ≤ 1 / (1 - δ))
    (hD' : ‖deletion (chartProjection p features allowed) safe‖ < 1) :
    let regular := regularDensity p features allowed line safe atom spike hD';
      expectation p regular = 1 ∧ (∀ x, 0 ≤ regular x) ∧
      (∀ x, ¬ safe x → regular x = 0) ∧
      (∀ x, safe x → 1 / 3 ≤ regular x) ∧
      (∀ i, line i → ∀ c, conditional p (features i) regular c =
        if c ∈ allowed i then (Fintype.card C : ℝ) / (allowed i).card else 0) ∧
      (∀ i, ¬ line i → ∀ c,
        conditional p (features i) ((1 - atom) • regular + atom • spike) c =
          if c ∈ allowed i then (Fintype.card C : ℝ) / (allowed i).card else 0) := by
  let P := chartProjection p features allowed
  let D := deletion P safe
  let b : ℝ := (2 * Fintype.card I + 1) * δ
  let η : ℝ := (Fintype.card I : ℝ) / (1 - δ) * (δ + b / (1 - b))
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hbQuarter : b ≤ 1 / 4 := hsmall
  have hb1 : b < 1 := by linarith
  have hDb : ‖D‖ ≤ b := chartDeletion_norm p features allowed safe δ hδ0 hglobal hconditional
  have hD : ‖D‖ < 1 := hDb.trans_lt hb1
  let defect := offLineDefect p features allowed line spike
  have hdef := offLineDefect_bounds p features allowed line spike hsmean hsnonneg hsallowed
    δ hδ0 hδ1 hsbound
  have hη : η ≤ 1 / 3 := hpositivity
  have hη0 : 0 ≤ η := by
    dsimp only [η]
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (by linarith))
      (add_nonneg hδ0 (div_nonneg hb0 (by linarith)))
  let odds := atom / (1 - atom)
  have hden : 0 < 1 - atom := by linarith
  have hodds0 : 0 ≤ odds := div_nonneg ha0 hden.le
  have hodds1 : odds ≤ 1 := by
    dsimp [odds]
    rw [div_le_iff₀ hden, one_mul]
    linarith
  let target : Ω → ℝ := 1 - odds • defect
  let raw := neumannSolve D hD target
  let regular := safeMask safe raw
  have htarget : P target = target := by
    change combinedProjection p features allowed (1 - odds • defect) = _
    rw [map_sub, map_smul, combinedProjection_one p features allowed hfeature,
      offLineDefect_projected p features allowed line spike hfeature hpair]
  have hproject : P regular = target :=
    safe_neumann_projection P safe
      (chartProjection_idempotent p features allowed hfeature hpair) hD target htarget
  have hmean : expectation p regular = 1 := by
    have hm := combinedProjection_mean p features allowed hfeature regular
    change expectation p (P regular) = expectation p regular at hm
    rw [hproject] at hm
    dsimp only [target] at hm
    have hone : expectation p (1 : Ω → ℝ) = 1 := expectation_const p 1
    rw [map_sub, map_smul, hone,
      offLineDefect_mean p features allowed line spike hfeature, smul_zero, sub_zero] at hm
    exact hm.symm
  have hzero (x : Ω) (hx : ¬ safe x) : regular x = 0 := by
    simp [regular, hx]
  have hlower (x : Ω) (hx : safe x) : 1 / 3 ≤ regular x := by
    have hbase := solve_sub_norm_le D hD b hb1 hDb (1 : Ω → ℝ)
    rw [norm_one] at hbase
    have hbasepoint := (norm_le_pi_norm (neumannSolve D hD 1 - 1) x).trans hbase
    change |neumannSolve D hD 1 x - 1| ≤ b / (1 - b) * 1 at hbasepoint
    have hrepair := solve_pointwise_upper D hD b hb1 hDb defect
      ((Fintype.card I : ℝ) * δ / (1 - δ))
      ((Fintype.card I : ℝ) / (1 - δ)) hdef.2 hdef.1 x
    have hηformula : (Fintype.card I : ℝ) * δ / (1 - δ) +
        b / (1 - b) * (Fintype.card I / (1 - δ)) = η := by dsimp [η]; ring
    rw [hηformula] at hrepair
    have hratio : b / (1 - b) ≤ 1 / 3 := by
      rw [div_le_iff₀ (by linarith : 0 < 1 - b)]
      linarith
    have hscaled : odds * neumannSolve D hD defect x ≤ 1 / 3 := by
      calc
        _ ≤ odds * η := mul_le_mul_of_nonneg_left hrepair hodds0
        _ ≤ η := (mul_le_mul_of_nonneg_right hodds1 hη0).trans_eq (one_mul η)
        _ ≤ _ := hη
    have hlinear : raw = neumannSolve D hD 1 - odds • neumannSolve D hD defect := by
      dsimp [raw, target, neumannSolve]
      rw [map_sub, map_smul]
    rw [show regular x = raw x by simp [regular, hx], hlinear]
    change 1 / 3 ≤ neumannSolve D hD 1 x - odds * neumannSolve D hD defect x
    linarith [(abs_le.mp hbasepoint).1]
  have hnonneg (x : Ω) : 0 ≤ regular x := by
    by_cases hx : safe x
    · linarith [hlower x hx]
    · rw [hzero x hx]
  have hcomponent (i : I) : featureProjection p (features i) (allowed i) regular =
      -odds • (if line i then 0 else featureProjection p (features i) (allowed i) spike) := by
    rw [← featureProjection_combined p features allowed hfeature hpair i regular]
    change featureProjection p (features i) (allowed i) (P regular) = _
    rw [hproject]
    dsimp only [target]
    have hone : featureProjection p (features i) (allowed i) (1 : Ω → ℝ) = 0 :=
      featureProjection_const p (features i) (hfeature i) (allowed i) 1
    rw [map_sub, map_smul, hone,
      offLineDefect_component p features allowed line spike hfeature hpair]
    split_ifs <;> simp
  dsimp only
  rw [show regularDensity p features allowed line safe atom spike hD' = regular from rfl]
  refine ⟨hmean, hnonneg, hzero, hlower, ?_, ?_⟩
  · intro i hi c
    have hc : featureProjection p (features i) (allowed i) regular = 0 := by
      rw [hcomponent i, if_pos hi, smul_zero]
    have hs := conditional_outside_zero p (features i) (allowed i) safe regular hzero (hallowed i)
    rw [component_zero_marginal p (features i) (hfeature i) (allowed i) regular hc hs c,
      hmean, mul_one]
  · intro i hi c
    let final := (1 - atom) • regular + atom • spike
    have hfmean : expectation p final = 1 := by
      change expectation p ((1 - atom) • regular + atom • spike) = 1
      rw [map_add, map_smul, map_smul, hmean, hsmean]
      simp
    have hfcomp : featureProjection p (features i) (allowed i) final = 0 := by
      dsimp [final]
      rw [map_add, map_smul, map_smul, hcomponent i, if_neg hi, smul_smul,
        ← add_smul]
      have hc : (1 - atom) * -odds + atom = 0 := by
        dsimp [odds]
        field_simp
        ring
      rw [hc, zero_smul]
    have hfzero (x : Ω) (hx : features i x ∉ allowed i) : final x = 0 := by
      have hn : ¬ safe x := fun h => hx (hallowed i x h)
      simp [final, hzero x hn, hsallowed i hi x hx]
    have hs := conditional_outside_zero p (features i) (allowed i)
      (fun x => features i x ∈ allowed i) final hfzero (fun _ h => h)
    rw [component_zero_marginal p (features i) (hfeature i) (allowed i) final hfcomp hs c,
      hfmean, mul_one]

theorem regular_branch [Nonempty Ω] [Nonempty C] (p : FiniteDist Ω)
    (features : I → Ω → C) (allowed : I → Finset C) (line : I → Prop)
    (hfeature : ∀ i, p.map (features i) = FiniteDist.uniform C)
    (hpair : ∀ i j, i ≠ j → p.map (fun x => (features i x, features j x)) =
      (FiniteDist.uniform C).prod (FiniteDist.uniform C))
    (safe : Ω → Prop) [DecidablePred safe]
    (hallowed : ∀ i x, safe x → features i x ∈ allowed i)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hglobal : expectation p (badIndicator safe) ≤ δ)
    (hconditional : ∀ i c, c ∈ allowed i →
      conditional p (features i) (badIndicator safe) c ≤ δ)
    (hsmall : (2 * Fintype.card I + 1) * δ ≤ 1 / 4)
    (hpositivity : (Fintype.card I : ℝ) / (1 - δ) *
      (δ + ((2 * Fintype.card I + 1) * δ) /
        (1 - (2 * Fintype.card I + 1) * δ)) ≤ 1 / 3)
    (atom : ℝ) (ha0 : 0 ≤ atom) (haHalf : atom ≤ 1 / 2)
    (spike : Ω → ℝ) (hsmean : expectation p spike = 1)
    (hsnonneg : ∀ x, 0 ≤ spike x)
    (hsallowed : ∀ i, ¬ line i → ∀ x, features i x ∉ allowed i → spike x = 0)
    (hsbound : ∀ i, ¬ line i → ∀ c,
      conditional p (features i) spike c ≤ 1 / (1 - δ)) :
    ∃ regular : Ω → ℝ,
      expectation p regular = 1 ∧ (∀ x, 0 ≤ regular x) ∧
      (∀ x, ¬ safe x → regular x = 0) ∧
      (∀ x, safe x → 1 / 3 ≤ regular x) ∧
      (∀ i, line i → ∀ c, conditional p (features i) regular c =
        if c ∈ allowed i then (Fintype.card C : ℝ) / (allowed i).card else 0) ∧
      (∀ i, ¬ line i → ∀ c,
        conditional p (features i) ((1 - atom) • regular + atom • spike) c =
          if c ∈ allowed i then (Fintype.card C : ℝ) / (allowed i).card else 0) := by
  have hquarter : ‖deletion (chartProjection p features allowed) safe‖ ≤ 1 / 4 :=
    (chartDeletion_norm p features allowed safe δ hδ0 hglobal hconditional).trans hsmall
  have hD : ‖deletion (chartProjection p features allowed) safe‖ < 1 :=
    hquarter.trans_lt (by norm_num)
  exact ⟨regularDensity p features allowed line safe atom spike hD,
    regularDensity_properties p features allowed line hfeature hpair safe hallowed δ hδ0 hδ1
      hglobal hconditional hsmall hpositivity atom ha0 haHalf spike hsmean hsnonneg hsallowed hsbound hD⟩

/-- The complete public flag and map distribution.  Neither its inputs nor
its support depend on the protected hidden source. -/
def flagLaw (atom : ℝ) (ha0 : 0 ≤ atom) (ha1 : atom ≤ 1)
    (regular marked : FiniteDist Ω) : FiniteDist (Bool × Ω) where
  weight point := if point.1 then atom * marked.weight point.2 else
    (1 - atom) * regular.weight point.2
  nonneg point := by
    split_ifs
    · exact mul_nonneg ha0 (marked.nonneg _)
    · exact mul_nonneg (by linarith) (regular.nonneg _)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, Bool.false_eq_true, if_false, if_true,
      ← Finset.mul_sum, regular.sum_one, marked.sum_one, mul_one]
    ring

theorem flagLaw_flag (atom : ℝ) (ha0 : 0 ≤ atom) (ha1 : atom ≤ 1)
    (regular marked : FiniteDist Ω) (flag : Bool) :
    ((flagLaw atom ha0 ha1 regular marked).map Prod.fst).weight flag =
      if flag then atom else 1 - atom := by
  rw [FiniteDist.map_weight, Fintype.sum_prod_type]
  cases flag <;>
    simp [flagLaw, ← Finset.mul_sum, regular.sum_one, marked.sum_one]

theorem flagLaw_feature (atom : ℝ) (ha0 : 0 ≤ atom) (ha1 : atom ≤ 1)
    (regular marked : FiniteDist Ω) (feature : Ω → C) (c : C) :
    ((flagLaw atom ha0 ha1 regular marked).map (fun point => feature point.2)).weight c =
      (1 - atom) * (regular.map feature).weight c + atom * (marked.map feature).weight c := by
  simp only [FiniteDist.map_weight, Fintype.sum_prod_type, flagLaw,
    Fintype.sum_bool, Bool.false_eq_true, if_false, if_true]
  simp_rw [Finset.mul_sum, mul_ite, mul_zero]
  exact add_comm _ _

end
end CurrentAFT.AffineFlagCalibration
