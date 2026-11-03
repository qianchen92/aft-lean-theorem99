import AFT.FiniteProbability
import Mathlib

/-!
# Positive repair on the safe affine-chart set

This file formalizes the finite-dimensional Neumann repair in V7's
`accuracy-boundary-chart` proof, including its pointwise positivity constants.
The affine-feature equivalences below supply the exact unrestricted uniform
and pairwise-independence statements used by that construction.
-/
namespace AFT
namespace BoundaryCalibration

open scoped BigOperators

section FiniteRepair
variable {Ω : Type*} [Fintype Ω]

/-- Restrict a chart density to the public safe set. -/
noncomputable def safeMask (safe : Ω → Prop) [DecidablePred safe] :
    (Ω → ℝ) →L[ℝ] (Ω → ℝ) :=
  ContinuousLinearMap.pi fun x => if safe x then ContinuousLinearMap.proj x else 0

omit [Fintype Ω] in
@[simp] theorem safeMask_apply (safe : Ω → Prop) [DecidablePred safe]
    (f : Ω → ℝ) (x : Ω) :
    safeMask safe f x = if safe x then f x else 0 := by
  simp only [safeMask, ContinuousLinearMap.pi_apply]
  split_ifs <;> simp

/-- The actual deletion operator `P(1_{safeᶜ} f)`. -/
noncomputable def deletion (P : (Ω → ℝ) →L[ℝ] (Ω → ℝ))
    (safe : Ω → Prop) [DecidablePred safe] : (Ω → ℝ) →L[ℝ] (Ω → ℝ) :=
  P * (ContinuousLinearMap.id ℝ (Ω → ℝ) - safeMask safe)

omit [Fintype Ω] in
@[simp] theorem deletion_apply (P : (Ω → ℝ) →L[ℝ] (Ω → ℝ))
    (safe : Ω → Prop) [DecidablePred safe] (f : Ω → ℝ) :
    deletion P safe f = P (f - safeMask safe f) := rfl

/-- Invert `Id - D` by its norm-convergent geometric series. -/
noncomputable def neumannSolve (D : (Ω → ℝ) →L[ℝ] (Ω → ℝ))
    (hD : ‖D‖ < 1) (f : Ω → ℝ) : Ω → ℝ :=
  (↑((Units.oneSub D hD)⁻¹) : (Ω → ℝ) →L[ℝ] (Ω → ℝ)) f

/-- The constructed inverse solves the required equation exactly. -/
theorem neumannSolve_equation (D : (Ω → ℝ) →L[ℝ] (Ω → ℝ))
    (hD : ‖D‖ < 1) (f : Ω → ℝ) :
    neumannSolve D hD f - D (neumannSolve D hD f) = f := by
  have h := congrArg (fun T : (Ω → ℝ) →L[ℝ] (Ω → ℝ) => T f)
    (Units.val_inv (Units.oneSub D hD))
  change ((1 - D) * (↑((Units.oneSub D hD)⁻¹) : (Ω → ℝ) →L[ℝ] (Ω → ℝ))) f = f at h
  simpa only [ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, neumannSolve] using h

/-- The quarter-contraction budget gives a one-third relative perturbation. -/
theorem neumannSolve_sub_norm (D : (Ω → ℝ) →L[ℝ] (Ω → ℝ))
    (hD : ‖D‖ < 1) (hquarter : ‖D‖ ≤ 1 / 4) (f : Ω → ℝ) :
    ‖neumannSolve D hD f - f‖ ≤ ‖f‖ / 3 := by
  let h := neumannSolve D hD f
  have heq : h - f = D h := by
    have hs := neumannSolve_equation D hD f
    change h - D h = f at hs
    exact sub_eq_iff_eq_add.mpr (by rw [← hs]; abel)
  have hnorm : ‖h‖ ≤ ‖h - f‖ + ‖f‖ := by
    simpa only [sub_add_cancel] using norm_add_le (h - f) f
  have hop : ‖h - f‖ ≤ (1 / 4) * ‖h‖ := by
    rw [heq]
    exact (D.le_opNorm h).trans (mul_le_mul_of_nonneg_right hquarter (norm_nonneg _))
  change ‖h - f‖ ≤ _
  nlinarith

/-- Inverse amplification is at most `4/3`, with no unknown matrix constant. -/
theorem neumannSolve_norm (D : (Ω → ℝ) →L[ℝ] (Ω → ℝ))
    (hD : ‖D‖ < 1) (hquarter : ‖D‖ ≤ 1 / 4) (f : Ω → ℝ) :
    ‖neumannSolve D hD f‖ ≤ (4 / 3) * ‖f‖ := by
  have hb := neumannSolve_sub_norm D hD hquarter f
  have ht := norm_add_le (neumannSolve D hD f - f) f
  rw [sub_add_cancel] at ht
  linarith

/-- If `P` is a projection and the desired response is in its range, restricting
the Neumann solution to safe charts has exactly that response. -/
theorem safe_neumann_projection (P : (Ω → ℝ) →L[ℝ] (Ω → ℝ))
    (safe : Ω → Prop) [DecidablePred safe] (hP : P * P = P)
    (hD : ‖deletion P safe‖ < 1) (f : Ω → ℝ) (hf : P f = f) :
    P (safeMask safe (neumannSolve (deletion P safe) hD f)) = f := by
  let h := neumannSolve (deletion P safe) hD f
  have heq : h - P (h - safeMask safe h) = f :=
    neumannSolve_equation (deletion P safe) hD f
  have hp := congrArg P heq
  have hPid (g : Ω → ℝ) : P (P g) = P g := by
    exact congrArg (fun T : (Ω → ℝ) →L[ℝ] (Ω → ℝ) => T g) hP
  simp only [map_sub, hPid, hf] at hp
  change P (safeMask safe h) = f
  convert hp using 1
  abel

/-- The base chart density is at least `2/3` on each safe chart. -/
theorem interior_density_lower [Nonempty Ω] (P : (Ω → ℝ) →L[ℝ] (Ω → ℝ))
    (safe : Ω → Prop) [DecidablePred safe]
    (hD : ‖deletion P safe‖ < 1) (hquarter : ‖deletion P safe‖ ≤ 1 / 4)
    (x : Ω) (hx : safe x) :
    2 / 3 ≤ safeMask safe (neumannSolve (deletion P safe) hD 1) x := by
  rw [safeMask_apply, if_pos hx]
  have hb := neumannSolve_sub_norm (deletion P safe) hD hquarter (1 : Ω → ℝ)
  rw [norm_one] at hb
  have hxbound := (norm_le_pi_norm (neumannSolve (deletion P safe) hD 1 - 1) x).trans hb
  change |neumannSolve (deletion P safe) hD 1 x - 1| ≤ 1 / 3 at hxbound
  linarith [(abs_le.mp hxbound).1]

/-- The spike defect budget `1/25` yields the paper's `4/75` repair bound. -/
theorem repair_density_norm (P : (Ω → ℝ) →L[ℝ] (Ω → ℝ))
    (safe : Ω → Prop) [DecidablePred safe]
    (hD : ‖deletion P safe‖ < 1) (hquarter : ‖deletion P safe‖ ≤ 1 / 4)
    (defect : Ω → ℝ) (hdefect : ‖defect‖ ≤ 1 / 25) :
    ‖neumannSolve (deletion P safe) hD defect‖ ≤ 4 / 75 := by
  have h := neumannSolve_norm (deletion P safe) hD hquarter defect
  linarith

/-- Subtracting the spike repair preserves strict positivity on every safe
chart, uniformly for the actual mark budget `atom ≤ 1/100`. -/
theorem repaired_density_positive [Nonempty Ω] (P : (Ω → ℝ) →L[ℝ] (Ω → ℝ))
    (safe : Ω → Prop) [DecidablePred safe]
    (hD : ‖deletion P safe‖ < 1) (hquarter : ‖deletion P safe‖ ≤ 1 / 4)
    (defect : Ω → ℝ) (hdefect : ‖defect‖ ≤ 1 / 25)
    (atom : ℝ) (hatom100 : atom ≤ 1 / 100)
    (x : Ω) (hx : safe x) :
    3 / 5 ≤ safeMask safe (neumannSolve (deletion P safe) hD 1) x -
      safeMask safe (neumannSolve (deletion P safe) hD defect) x / (1 - atom) := by
  have hi := interior_density_lower P safe hD hquarter x hx
  have hr := (norm_le_pi_norm (neumannSolve (deletion P safe) hD defect) x).trans
    (repair_density_norm P safe hD hquarter defect hdefect)
  have hden : 0 < 1 - atom := by linarith
  have hsmall :
      safeMask safe (neumannSolve (deletion P safe) hD defect) x / (1 - atom) ≤ 1 / 15 := by
    rw [safeMask_apply, if_pos hx, div_le_iff₀ hden]
    have hu : neumannSolve (deletion P safe) hD defect x ≤ 4 / 75 :=
      (le_abs_self _).trans hr
    nlinarith
  linarith

end FiniteRepair
section FeatureProjections
open scoped Classical
variable {Ω C I : Type*} [Fintype Ω] [Fintype C] [Fintype I]

/-- Exact expectation as a linear functional on finite chart densities. -/
noncomputable def expectation (p : FiniteDist Ω) : (Ω → ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∑ x, p.weight x * f x
  map_add' f g := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' r f := by simp [mul_left_comm, ← Finset.mul_sum]

@[simp] theorem expectation_apply (p : FiniteDist Ω) (f : Ω → ℝ) :
    expectation p f = ∑ x, p.weight x * f x := rfl

@[simp] theorem expectation_const (p : FiniteDist Ω) (r : ℝ) :
    expectation p (fun _ => r) = r := by
  simp [expectation, ← Finset.sum_mul, p.sum_one]

/-- Pushforward is exact at the level of every test function. -/
theorem expectation_map (p : FiniteDist Ω) (feature : Ω → C) (g : C → ℝ) :
    expectation (p.map feature) g = expectation p (fun x => g (feature x)) := by
  simp only [expectation_apply, FiniteDist.map_weight, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [ite_mul]

/-- Normalized expectation conditioned on an equidistributed feature value. -/
noncomputable def conditional (p : FiniteDist Ω) (feature : Ω → C) :
    (Ω → ℝ) →ₗ[ℝ] (C → ℝ) where
  toFun f color := (Fintype.card C : ℝ) *
    expectation p (fun x => if feature x = color then f x else 0)
  map_add' f g := by
    funext color
    change (Fintype.card C : ℝ) * expectation p
      (fun x => if feature x = color then f x + g x else 0) = _
    have he : (fun x => if feature x = color then f x + g x else (0 : ℝ)) =
        (fun x => if feature x = color then f x else 0) +
          (fun x => if feature x = color then g x else 0) := by
      funext x
      split_ifs <;> simp_all
    rw [he, map_add, mul_add]
    rfl
  map_smul' r f := by
    funext color
    change (Fintype.card C : ℝ) * expectation p
      (fun x => if feature x = color then r * f x else 0) = _
    have he : (fun x => if feature x = color then r * f x else (0 : ℝ)) =
        r • (fun x => if feature x = color then f x else 0) := by
      funext x
      split_ifs <;> simp_all
    rw [he, map_smul]
    change (Fintype.card C : ℝ) * (r * _) = r * ((Fintype.card C : ℝ) * _)
    ring

@[simp] theorem conditional_apply (p : FiniteDist Ω) (feature : Ω → C)
    (f : Ω → ℝ) (color : C) :
    conditional p feature f color = (Fintype.card C : ℝ) *
      expectation p (fun x => if feature x = color then f x else 0) := rfl

/-- Conditioning a feature on itself recovers the exact color profile. -/
theorem conditional_same [Nonempty C] (p : FiniteDist Ω) (feature : Ω → C)
    (hfeature : p.map feature = FiniteDist.uniform C) (g : C → ℝ) :
    conditional p feature (fun x => g (feature x)) = g := by
  funext color
  rw [conditional_apply]
  have he := expectation_map p feature (fun c => if c = color then g c else 0)
  rw [hfeature] at he
  rw [← he]
  simp [expectation_apply, FiniteDist.uniform_weight, mul_ite,
    Fintype.card_ne_zero]

/-- Conditioning on an independent uniform feature gives a constant profile. -/
theorem conditional_other [Nonempty C] (p : FiniteDist Ω) (first second : Ω → C)
    (hpair : p.map (fun x => (first x, second x)) =
      (FiniteDist.uniform C).prod (FiniteDist.uniform C)) (g : C → ℝ) :
    conditional p first (fun x => g (second x)) =
      fun _ => expectation (FiniteDist.uniform C) g := by
  funext color
  rw [conditional_apply]
  have he := expectation_map p (fun x => (first x, second x))
    (fun pair => if pair.1 = color then g pair.2 else 0)
  rw [hpair] at he
  rw [← he]
  have hC : (Fintype.card C : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [expectation_apply, FiniteDist.prod_weight, FiniteDist.uniform_weight,
    Fintype.sum_prod_type, mul_ite, ← Finset.mul_sum]
  field_simp

/-- Keep a color profile on its allowed set and subtract its allowed-set mean. -/
noncomputable def centerAllowed (allowed : Finset C) : (C → ℝ) →ₗ[ℝ] (C → ℝ) where
  toFun g c := if c ∈ allowed then g c - (∑ a ∈ allowed, g a) / allowed.card else 0
  map_add' f g := by
    funext c
    simp only [Pi.add_apply]
    split_ifs <;> simp [Finset.sum_add_distrib, add_div]
    ring
  map_smul' r g := by
    funext c
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp [← Finset.mul_sum, mul_sub, mul_div_assoc]

omit [Fintype C] in
@[simp] theorem centerAllowed_apply (allowed : Finset C) (g : C → ℝ) (c : C) :
    centerAllowed allowed g c =
      if c ∈ allowed then g c - (∑ a ∈ allowed, g a) / allowed.card else 0 := rfl

omit [Fintype C] in
@[simp] theorem centerAllowed_const (allowed : Finset C) (r : ℝ) :
    centerAllowed allowed (fun _ => r) = 0 := by
  funext c
  rw [centerAllowed_apply]
  by_cases hc : c ∈ allowed
  · have hcard : (allowed.card : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨c, hc⟩)
    simp [hc, hcard]
  · simp [hc]

/-- Centering on the allowed palette removes all mass. -/
theorem centerAllowed_sum (allowed : Finset C) (g : C → ℝ) :
    ∑ c, centerAllowed allowed g c = 0 := by
  simp only [centerAllowed_apply, ← Finset.sum_filter]
  simp only [Finset.filter_univ_mem]
  by_cases ha : allowed = ∅
  · simp [ha]
  · have hcard : (allowed.card : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr ha))
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    field_simp
    ring

/-- Centering twice is exactly the same projection. -/
theorem centerAllowed_idempotent (allowed : Finset C) (g : C → ℝ) :
    centerAllowed allowed (centerAllowed allowed g) = centerAllowed allowed g := by
  have hsum : ∑ a ∈ allowed, centerAllowed allowed g a = 0 := by
    rw [← centerAllowed_sum allowed g]
    exact Finset.sum_subset (Finset.subset_univ _) (fun c _ hc => by simp [hc])
  funext c
  rw [centerAllowed_apply, hsum, zero_div, sub_zero]
  split_ifs with hc
  · rfl
  · simp [hc]

/-- Pull a color profile back to the corresponding chart feature. -/
def liftFeature (feature : Ω → C) : (C → ℝ) →ₗ[ℝ] (Ω → ℝ) where
  toFun g x := g (feature x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual centered feature projection from the boundary-chart proof. -/
noncomputable def featureProjection (p : FiniteDist Ω) (feature : Ω → C)
    (allowed : Finset C) : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) :=
  (liftFeature feature).comp ((centerAllowed allowed).comp (conditional p feature))

@[simp] theorem featureProjection_apply (p : FiniteDist Ω) (feature : Ω → C)
    (allowed : Finset C) (f : Ω → ℝ) (x : Ω) :
    featureProjection p feature allowed f x =
      centerAllowed allowed (conditional p feature f) (feature x) := rfl

/-- Each feature component is an exact projection. -/
theorem featureProjection_idempotent [Nonempty C] (p : FiniteDist Ω)
    (feature : Ω → C) (hfeature : p.map feature = FiniteDist.uniform C)
    (allowed : Finset C) :
    (featureProjection p feature allowed).comp (featureProjection p feature allowed) =
      featureProjection p feature allowed := by
  apply LinearMap.ext
  intro f
  change liftFeature feature (centerAllowed allowed
    (conditional p feature (fun x => centerAllowed allowed
      (conditional p feature f) (feature x)))) = _
  rw [conditional_same p feature hfeature, centerAllowed_idempotent]
  rfl

/-- Different feature projections annihilate each other by exact pairwise independence. -/
theorem featureProjection_orthogonal [Nonempty C] (p : FiniteDist Ω)
    (first second : Ω → C)
    (hpair : p.map (fun x => (first x, second x)) =
      (FiniteDist.uniform C).prod (FiniteDist.uniform C)) (A B : Finset C) :
    (featureProjection p first A).comp (featureProjection p second B) = 0 := by
  apply LinearMap.ext
  intro f
  change liftFeature first (centerAllowed A
    (conditional p first (fun x => centerAllowed B
      (conditional p second f) (second x)))) = 0
  rw [conditional_other p first second hpair, centerAllowed_const, map_zero]

/-- Projection onto the constant chart densities. -/
noncomputable def constantProjection (p : FiniteDist Ω) : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) where
  toFun f _ := expectation p f
  map_add' _ _ := by funext x; simp only [map_add, Pi.add_apply]
  map_smul' _ _ := by funext x; simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

@[simp] theorem constantProjection_apply (p : FiniteDist Ω) (f : Ω → ℝ) (x : Ω) :
    constantProjection p f x = expectation p f := rfl

@[simp] theorem constantProjection_idempotent (p : FiniteDist Ω) :
    constantProjection p * constantProjection p = constantProjection p := by
  apply LinearMap.ext
  intro f
  funext x
  exact expectation_const p (expectation p f)

/-- Feature centering annihilates constants. -/
theorem featureProjection_const [Nonempty C] (p : FiniteDist Ω) (feature : Ω → C)
    (hfeature : p.map feature = FiniteDist.uniform C) (allowed : Finset C) (r : ℝ) :
    featureProjection p feature allowed (fun _ => r) = 0 := by
  change liftFeature feature (centerAllowed allowed
    (conditional p feature (fun x => (fun _ : C => r) (feature x)))) = 0
  rw [conditional_same p feature hfeature (fun _ : C => r), centerAllowed_const, map_zero]

/-- Each centered feature has zero unrestricted mean. -/
theorem featureProjection_mean [Nonempty C] (p : FiniteDist Ω) (feature : Ω → C)
    (hfeature : p.map feature = FiniteDist.uniform C) (allowed : Finset C) (f : Ω → ℝ) :
    expectation p (featureProjection p feature allowed f) = 0 := by
  change expectation p (fun x =>
    centerAllowed allowed (conditional p feature f) (feature x)) = 0
  rw [← expectation_map, hfeature]
  simp only [expectation_apply, FiniteDist.uniform_weight, ← Finset.mul_sum,
    centerAllowed_sum, mul_zero]

theorem featureProjection_constantProjection [Nonempty C] (p : FiniteDist Ω)
    (feature : Ω → C) (hfeature : p.map feature = FiniteDist.uniform C) (allowed : Finset C) :
    featureProjection p feature allowed * constantProjection p = 0 := by
  apply LinearMap.ext
  intro f
  funext x
  exact congrFun (featureProjection_const p feature hfeature allowed (expectation p f)) x

theorem constantProjection_featureProjection [Nonempty C] (p : FiniteDist Ω)
    (feature : Ω → C) (hfeature : p.map feature = FiniteDist.uniform C) (allowed : Finset C) :
    constantProjection p * featureProjection p feature allowed = 0 := by
  apply LinearMap.ext
  intro f
  funext x
  exact featureProjection_mean p feature hfeature allowed f

/-- The paper's projection: constants plus all allowed centered feature components. -/
noncomputable def combinedProjection (p : FiniteDist Ω) (features : I → Ω → C)
    (allowed : I → Finset C) : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) :=
  constantProjection p + ∑ i, featureProjection p (features i) (allowed i)

/-- Pairwise-independent unrestricted features make the concrete sum operator
an exact projection. -/
theorem combinedProjection_idempotent [Nonempty C] (p : FiniteDist Ω)
    (features : I → Ω → C) (allowed : I → Finset C)
    (hfeature : ∀ i, p.map (features i) = FiniteDist.uniform C)
    (hpair : ∀ i j, i ≠ j → p.map (fun x => (features i x, features j x)) =
      (FiniteDist.uniform C).prod (FiniteDist.uniform C)) :
    combinedProjection p features allowed * combinedProjection p features allowed =
      combinedProjection p features allowed := by
  have hcomp (i j : I) :
      featureProjection p (features i) (allowed i) * featureProjection p (features j) (allowed j) =
        if i = j then featureProjection p (features i) (allowed i) else 0 := by
    by_cases hij : i = j
    · subst j
      simpa using featureProjection_idempotent p (features i) (hfeature i) (allowed i)
    · rw [if_neg hij]
      exact featureProjection_orthogonal p (features i) (features j) (hpair i j hij)
        (allowed i) (allowed j)
  unfold combinedProjection
  rw [add_mul, mul_add, mul_add]
  simp_rw [Finset.mul_sum, Finset.sum_mul,
    constantProjection_idempotent,
    constantProjection_featureProjection p _ (hfeature _),
    featureProjection_constantProjection p _ (hfeature _), hcomp]
  simp

@[simp] theorem combinedProjection_one [Nonempty C] (p : FiniteDist Ω)
    (features : I → Ω → C) (allowed : I → Finset C)
    (hfeature : ∀ i, p.map (features i) = FiniteDist.uniform C) :
    combinedProjection p features allowed 1 = 1 := by
  have hc : constantProjection p 1 = (1 : Ω → ℝ) := by
    funext x
    exact expectation_const p 1
  have hf (i : I) : featureProjection p (features i) (allowed i) 1 = 0 :=
    featureProjection_const p (features i) (hfeature i) (allowed i) 1
  simp [combinedProjection, LinearMap.sum_apply, hc, hf]

/-- Constants are an independent component: the projection preserves mass. -/
theorem combinedProjection_mean [Nonempty C] (p : FiniteDist Ω)
    (features : I → Ω → C) (allowed : I → Finset C)
    (hfeature : ∀ i, p.map (features i) = FiniteDist.uniform C) (f : Ω → ℝ) :
    expectation p (combinedProjection p features allowed f) = expectation p f := by
  simp only [combinedProjection, LinearMap.add_apply, LinearMap.sum_apply,
    map_add, map_sum]
  have hc : expectation p (constantProjection p f) = expectation p f :=
    expectation_const p _
  rw [hc]
  simp_rw [featureProjection_mean p _ (hfeature _)]
  simp

/-- The concrete finite feature projection as a bounded operator for Neumann repair. -/
noncomputable def chartProjection (p : FiniteDist Ω) (features : I → Ω → C)
    (allowed : I → Finset C) : (Ω → ℝ) →L[ℝ] (Ω → ℝ) :=
  (combinedProjection p features allowed).toContinuousLinearMap

@[simp] theorem chartProjection_apply (p : FiniteDist Ω) (features : I → Ω → C)
    (allowed : I → Finset C) (f : Ω → ℝ) (x : Ω) :
    chartProjection p features allowed f x = expectation p f +
      ∑ i, centerAllowed (allowed i) (conditional p (features i) f) (features i x) := by
  simp [chartProjection, combinedProjection]

/-- Idempotence of the bounded operator used by the actual safe-set deletion. -/
theorem chartProjection_idempotent [Nonempty C] (p : FiniteDist Ω)
    (features : I → Ω → C) (allowed : I → Finset C)
    (hfeature : ∀ i, p.map (features i) = FiniteDist.uniform C)
    (hpair : ∀ i j, i ≠ j → p.map (fun x => (features i x, features j x)) =
      (FiniteDist.uniform C).prod (FiniteDist.uniform C)) :
    chartProjection p features allowed * chartProjection p features allowed =
      chartProjection p features allowed := by
  ext f x
  exact congrFun (congrArg (fun L : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) => L f)
    (combinedProjection_idempotent p features allowed hfeature hpair)) x

/-- A nonnegative weighting controls arbitrary signed tests by their sup norm. -/
theorem expectation_abs_mul_le (p : FiniteDist Ω) (weight f : Ω → ℝ)
    (hw : ∀ x, 0 ≤ weight x) :
    |expectation p (fun x => weight x * f x)| ≤ ‖f‖ * expectation p weight := by
  calc
    _ ≤ ∑ x, |p.weight x * (weight x * f x)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, p.weight x * weight x * |f x| := by
      apply Finset.sum_congr rfl
      intro x _
      rw [abs_mul, abs_mul, abs_of_nonneg (p.nonneg x), abs_of_nonneg (hw x)]
      ring
    _ ≤ ∑ x, p.weight x * weight x * ‖f‖ := by
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm f x)
        (mul_nonneg (p.nonneg x) (hw x))
    _ = ‖f‖ * expectation p weight := by
      rw [← Finset.sum_mul]
      unfold expectation
      dsimp
      ring

/-- The same test bound holds conditionally on each feature value. -/
theorem conditional_abs_mul_le (p : FiniteDist Ω) (feature : Ω → C)
    (weight f : Ω → ℝ) (hw : ∀ x, 0 ≤ weight x) (c : C) :
    |conditional p feature (fun x => weight x * f x) c| ≤
      ‖f‖ * conditional p feature weight c := by
  have he : (fun x => if feature x = c then weight x * f x else (0 : ℝ)) =
      fun x => (if feature x = c then weight x else 0) * f x := by
    funext x
    split_ifs <;> simp
  rw [conditional_apply, conditional_apply, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), he]
  have h := expectation_abs_mul_le p (fun x => if feature x = c then weight x else 0) f
    (fun x => by dsimp only; split_ifs <;> simp [hw])
  calc
    _ ≤ (Fintype.card C : ℝ) * (‖f‖ * expectation p
        (fun x => if feature x = c then weight x else 0)) :=
      mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
    _ = _ := by ring

omit [Fintype C] in
/-- Centering an allowed-set profile costs at most twice its sup bound. -/
theorem centerAllowed_abs_le (allowed : Finset C) (g : C → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hg : ∀ c ∈ allowed, |g c| ≤ M) (c : C) :
    |centerAllowed allowed g c| ≤ 2 * M := by
  rw [centerAllowed_apply]
  by_cases hc : c ∈ allowed
  · rw [if_pos hc]
    have hcard : 0 < (allowed.card : ℝ) :=
      Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨c, hc⟩)
    have havg : |(∑ a ∈ allowed, g a) / allowed.card| ≤ M := by
      rw [abs_div, abs_of_nonneg hcard.le, div_le_iff₀ hcard]
      calc
        _ ≤ ∑ a ∈ allowed, |g a| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _a ∈ allowed, M := Finset.sum_le_sum (fun a ha => hg a ha)
        _ = _ := by simp [mul_comm]
    exact (abs_sub _ _).trans (by linarith [hg c hc])
  · simp [hc, hM]

/-- The public deletion indicator used in the exact finite probability bounds. -/
noncomputable def badIndicator (safe : Ω → Prop) : Ω → ℝ :=
  fun x => if safe x then 0 else 1

/-- The actual `l∞` deletion norm bound, derived from scalar deletion
probabilities.  With `m` features this is exactly `(2m+1)ε` in V7. -/
theorem chartDeletion_norm (p : FiniteDist Ω) (features : I → Ω → C)
    (allowed : I → Finset C) (safe : Ω → Prop) [DecidablePred safe]
    (ε : ℝ) (hε : 0 ≤ ε)
    (hglobal : expectation p (badIndicator safe) ≤ ε)
    (hconditional : ∀ i c, c ∈ allowed i →
      conditional p (features i) (badIndicator safe) c ≤ ε) :
    ‖deletion (Ω := Ω) (chartProjection (Ω := Ω) (C := C) (I := I) p features allowed) safe‖ ≤
      (2 * Fintype.card I + 1) * ε := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro x
  have hb : ∀ y, 0 ≤ badIndicator safe y := by
    intro y
    unfold badIndicator
    split_ifs <;> norm_num
  have heq : f - safeMask safe f = fun y => badIndicator safe y * f y := by
    funext y
    simp only [Pi.sub_apply, safeMask_apply, badIndicator]
    split_ifs <;> simp
  have hg : |expectation p (f - safeMask safe f)| ≤ ε * ‖f‖ := by
    rw [heq]
    exact (expectation_abs_mul_le p (badIndicator safe) f hb).trans
      (by nlinarith [mul_le_mul_of_nonneg_left hglobal (norm_nonneg f)])
  have hc (i : I) (c : C) (hca : c ∈ allowed i) :
      |conditional p (features i) (f - safeMask safe f) c| ≤ ε * ‖f‖ := by
    rw [heq]
    exact (conditional_abs_mul_le p (features i) (badIndicator safe) f hb c).trans
      (by nlinarith [mul_le_mul_of_nonneg_left (hconditional i c hca) (norm_nonneg f)])
  change |chartProjection p features allowed (f - safeMask safe f) x| ≤ _
  rw [chartProjection_apply]
  calc
    _ ≤ |expectation p (f - safeMask safe f)| +
        |∑ i, centerAllowed (allowed i)
          (conditional p (features i) (f - safeMask safe f)) (features i x)| := abs_add_le _ _
    _ ≤ ε * ‖f‖ + ∑ i, |centerAllowed (allowed i)
        (conditional p (features i) (f - safeMask safe f)) (features i x)| :=
      add_le_add hg (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ε * ‖f‖ + ∑ _i : I, 2 * (ε * ‖f‖) := by
      apply add_le_add_right
      apply Finset.sum_le_sum
      intro i _
      exact centerAllowed_abs_le (allowed i) _ (ε * ‖f‖)
        (mul_nonneg hε (norm_nonneg _)) (hc i) (features i x)
    _ = _ := by simp; ring

/-- Expectation is monotone for pointwise ordered tests. -/
theorem expectation_mono (p : FiniteDist Ω) {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) :
    expectation p f ≤ expectation p g :=
  Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (p.nonneg x))

theorem conditional_mono (p : FiniteDist Ω) (feature : Ω → C)
    {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) (c : C) :
    conditional p feature f c ≤ conditional p feature g c := by
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply expectation_mono
  intro x
  split_ifs <;> simp [h]

/-- Indicator of a forbidden color in one palette. -/
noncomputable def paletteFailure (allowed : Finset C) (c : C) : ℝ :=
  if c ∈ allowed then 0 else 1

omit [Fintype C] in
@[simp] theorem paletteFailure_nonneg (allowed : Finset C) (c : C) :
    0 ≤ paletteFailure allowed c := by unfold paletteFailure; split_ifs <;> norm_num

/-- Simultaneously enforce nonzero scale (the auxiliary palette) and all
trimmed feature palettes. -/
def legalChart (auxiliary : Ω → C) (auxAllowed : Finset C)
    (features : I → Ω → C) (allowed : I → Finset C) (x : Ω) : Prop :=
  auxiliary x ∈ auxAllowed ∧ ∀ i, features i x ∈ allowed i

omit [Fintype Ω] [Fintype C] in
/-- The union bound is pointwise before any probability or conditioning. -/
theorem badIndicator_le_palette_sum (auxiliary : Ω → C) (auxAllowed : Finset C)
    (features : I → Ω → C) (allowed : I → Finset C) (x : Ω) :
    badIndicator (legalChart auxiliary auxAllowed features allowed) x ≤
      paletteFailure auxAllowed (auxiliary x) +
        ∑ i, paletteFailure (allowed i) (features i x) := by
  by_cases hs : legalChart auxiliary auxAllowed features allowed x
  · simp only [badIndicator, if_pos hs]
    exact add_nonneg (paletteFailure_nonneg _ _)
      (Finset.sum_nonneg (fun i _ => paletteFailure_nonneg _ _))
  · simp only [badIndicator, if_neg hs]
    by_cases ha : auxiliary x ∈ auxAllowed
    · have he : ∃ i, features i x ∉ allowed i := by
        simpa only [legalChart, ha, true_and, not_forall] using hs
      obtain ⟨i, hi⟩ := he
      have hsum := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
        paletteFailure_nonneg (allowed j) (features j x)) (Finset.mem_univ i)
      simpa [paletteFailure, ha, hi] using hsum
    · rw [show paletteFailure auxAllowed (auxiliary x) = 1 by simp [paletteFailure, ha]]
      exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => paletteFailure_nonneg _ _))

/-- Exact uniform probability of a forbidden palette. -/
theorem uniform_palette_failure [Nonempty C] (allowed : Finset C) :
    expectation (FiniteDist.uniform C) (paletteFailure allowed) =
      1 - (allowed.card : ℝ) / Fintype.card C := by
  have heq : paletteFailure allowed =
      (fun _ : C => (1 : ℝ)) - (fun c => if c ∈ allowed then (1 : ℝ) else 0) := by
    funext c
    unfold paletteFailure
    split_ifs <;> simp_all
  rw [heq, map_sub, expectation_const]
  congr 1
  simp only [expectation_apply, FiniteDist.uniform_weight, mul_ite, mul_one, mul_zero,
    ← Finset.sum_filter, Finset.filter_univ_mem]
  simp [div_eq_mul_inv]

/-- Uniform feature laws give the unconditional union deletion budget. -/
theorem legalChart_global_budget [Nonempty C] (p : FiniteDist Ω)
    (auxiliary : Ω → C) (auxAllowed : Finset C)
    (features : I → Ω → C) (allowed : I → Finset C)
    (haux : p.map auxiliary = FiniteDist.uniform C)
    (hfeature : ∀ i, p.map (features i) = FiniteDist.uniform C) :
    expectation p (badIndicator (legalChart auxiliary auxAllowed features allowed)) ≤
      expectation (FiniteDist.uniform C) (paletteFailure auxAllowed) +
        ∑ i, expectation (FiniteDist.uniform C) (paletteFailure (allowed i)) := by
  have h := expectation_mono p (badIndicator_le_palette_sum auxiliary auxAllowed features allowed)
  have heq : (fun x => paletteFailure auxAllowed (auxiliary x) +
      ∑ i, paletteFailure (allowed i) (features i x)) =
      (fun x => paletteFailure auxAllowed (auxiliary x)) +
        ∑ i, (fun x => paletteFailure (allowed i) (features i x)) := by
    ext x
    simp
  rw [heq, map_add, map_sum] at h
  rw [← expectation_map p auxiliary (paletteFailure auxAllowed), haux] at h
  have hf (i : I) : expectation p (fun x => paletteFailure (allowed i) (features i x)) =
      expectation (FiniteDist.uniform C) (paletteFailure (allowed i)) := by
    rw [← expectation_map p (features i) (paletteFailure (allowed i)), hfeature i]
  simpa only [hf] using h

/-- The same deletion budget remains valid after fixing any allowed feature
value: its own violation disappears and all other violations remain uniform. -/
theorem legalChart_conditional_budget [Nonempty C] (p : FiniteDist Ω)
    (auxiliary : Ω → C) (auxAllowed : Finset C)
    (features : I → Ω → C) (allowed : I → Finset C)
    (hfeature : ∀ i, p.map (features i) = FiniteDist.uniform C)
    (hpair : ∀ i j, i ≠ j → p.map (fun x => (features i x, features j x)) =
      (FiniteDist.uniform C).prod (FiniteDist.uniform C))
    (hauxpair : ∀ i, p.map (fun x => (features i x, auxiliary x)) =
      (FiniteDist.uniform C).prod (FiniteDist.uniform C))
    (i : I) (c : C) (hc : c ∈ allowed i) :
    conditional p (features i)
      (badIndicator (legalChart auxiliary auxAllowed features allowed)) c ≤
      expectation (FiniteDist.uniform C) (paletteFailure auxAllowed) +
        ∑ j, expectation (FiniteDist.uniform C) (paletteFailure (allowed j)) := by
  have h := conditional_mono p (features i)
    (badIndicator_le_palette_sum auxiliary auxAllowed features allowed) c
  have heq : (fun x => paletteFailure auxAllowed (auxiliary x) +
      ∑ j, paletteFailure (allowed j) (features j x)) =
      (fun x => paletteFailure auxAllowed (auxiliary x)) +
        ∑ j, (fun x => paletteFailure (allowed j) (features j x)) := by
    ext x
    simp
  rw [heq, map_add, map_sum] at h
  have ha := conditional_other p (features i) auxiliary (hauxpair i) (paletteFailure auxAllowed)
  have hj (j : I) : conditional p (features i)
      (fun x => paletteFailure (allowed j) (features j x)) c ≤
      expectation (FiniteDist.uniform C) (paletteFailure (allowed j)) := by
    by_cases hij : i = j
    · subst j
      rw [conditional_same p (features i) (hfeature i)]
      simp only [paletteFailure, if_pos hc]
      exact Finset.sum_nonneg (fun x _ => mul_nonneg
        ((FiniteDist.uniform C).nonneg x) (paletteFailure_nonneg _ _))
    · rw [conditional_other p (features i) (features j) (hpair i j hij)]
  calc
    _ ≤ _ := h
    _ ≤ _ := by
      simp only [Pi.add_apply, Finset.sum_apply]
      rw [ha]
      exact add_le_add_right (Finset.sum_le_sum (fun j _ => hj j)) _

/-- A component is unchanged by applying the complete orthogonal projection. -/
theorem featureProjection_combined [Nonempty C] (p : FiniteDist Ω)
    (features : I → Ω → C) (allowed : I → Finset C)
    (hfeature : ∀ i, p.map (features i) = FiniteDist.uniform C)
    (hpair : ∀ i j, i ≠ j → p.map (fun x => (features i x, features j x)) =
      (FiniteDist.uniform C).prod (FiniteDist.uniform C)) (i : I) (f : Ω → ℝ) :
    featureProjection p (features i) (allowed i) (combinedProjection p features allowed f) =
      featureProjection p (features i) (allowed i) f := by
  have hcomp (j : I) : featureProjection p (features i) (allowed i)
      (featureProjection p (features j) (allowed j) f) =
      if i = j then featureProjection p (features i) (allowed i) f else 0 := by
    by_cases hij : i = j
    · subst j
      simpa using congrArg (fun L : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) => L f)
        (featureProjection_idempotent p (features i) (hfeature i) (allowed i))
    · rw [if_neg hij]
      exact congrArg (fun L : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) => L f)
        (featureProjection_orthogonal p (features i) (features j) (hpair i j hij)
          (allowed i) (allowed j))
  simp only [combinedProjection, LinearMap.add_apply, LinearMap.sum_apply, map_add, map_sum]
  have hc : featureProjection p (features i) (allowed i) (constantProjection p f) = 0 :=
    featureProjection_const p (features i) (hfeature i) (allowed i) _
  rw [hc]
  simp only [hcomp, Finset.sum_ite_eq, Finset.mem_univ, if_true, zero_add]

/-- Summing conditional densities restores the unrestricted density mass. -/
theorem conditional_sum (p : FiniteDist Ω) (feature : Ω → C) (f : Ω → ℝ) :
    ∑ c, conditional p feature f c = (Fintype.card C : ℝ) * expectation p f := by
  simp only [conditional_apply, expectation_apply, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  simp [mul_ite]

/-- Zero centered component and palette support determine the entire marginal. -/
theorem centerAllowed_zero_profile (allowed : Finset C) (g : C → ℝ)
    (hcenter : centerAllowed allowed g = 0) (hsupport : ∀ c ∉ allowed, g c = 0) (c : C) :
    g c = if c ∈ allowed then (∑ a, g a) / allowed.card else 0 := by
  have hsum : ∑ a ∈ allowed, g a = ∑ a, g a :=
    Finset.sum_subset (Finset.subset_univ _) (fun a _ ha => hsupport a ha)
  by_cases hc : c ∈ allowed
  · have h := congrFun hcenter c
    simp only [centerAllowed_apply, if_pos hc, Pi.zero_apply, hsum] at h
    simpa only [if_pos hc] using sub_eq_zero.mp h
  · simp [hc, hsupport c hc]

/-- Safe support forces every forbidden feature marginal to vanish exactly. -/
theorem conditional_outside_zero (p : FiniteDist Ω) (feature : Ω → C)
    (allowed : Finset C) (safe : Ω → Prop) (f : Ω → ℝ)
    (hsupport : ∀ x, ¬ safe x → f x = 0)
    (hallowed : ∀ x, safe x → feature x ∈ allowed) (c : C) (hc : c ∉ allowed) :
    conditional p feature f c = 0 := by
  rw [conditional_apply]
  have heq : (fun x => if feature x = c then f x else (0 : ℝ)) = 0 := by
    funext x
    by_cases hx : feature x = c
    · have hn : ¬ safe x := by intro hs; exact hc (hx ▸ hallowed x hs)
      simp [hx, hsupport x hn]
    · simp [hx]
  rw [heq, map_zero, mul_zero]

/-- Positive normalized base chart density, constructed from the concrete
finite feature projection and its numerical deletion budget. -/
theorem positive_chart_density [Nonempty Ω] [Nonempty C] (p : FiniteDist Ω)
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
    (hsmall : (2 * Fintype.card I + 1) * ε ≤ 1 / 4) :
    ∃ w : Ω → ℝ,
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
  refine ⟨w, hmean, ?_, hzero, hpos, ?_⟩
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

/-- Turn a nonnegative mean-one chart density into its actual probability law. -/
noncomputable def densityLaw (p : FiniteDist Ω) (w : Ω → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hmean : expectation p w = 1) : FiniteDist Ω where
  weight x := p.weight x * w x
  nonneg x := mul_nonneg (p.nonneg x) (hw x)
  sum_one := hmean

/-- Conditional densities and the probability law's marginal have the exact
uniform-reference conversion factor. -/
theorem densityLaw_marginal [Nonempty C] (p : FiniteDist Ω) (w : Ω → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hmean : expectation p w = 1)
    (feature : Ω → C) (c : C) :
    ((densityLaw p w hw hmean).map feature).weight c =
      conditional p feature w c / Fintype.card C := by
  rw [FiniteDist.map_weight, conditional_apply]
  have hC : (Fintype.card C : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [mul_div_cancel_left₀ _ hC]
  simp only [expectation_apply, densityLaw, mul_ite, mul_zero]

end FeatureProjections






section AffineFeatures
variable {F : Type*} [Field F]

/-- A chart stores the base, scale, and shear in that order. -/
abbrev Chart (F : Type*) := F × F × F

/-- The exact protected affine feature at source input `(first, second)`. -/
def feature (first second : F) (chart : Chart F) : F :=
  chart.1 + chart.2.1 * first + chart.2.2 * second

/-- Every feature is a free uniform coordinate jointly with scale and shear. -/
def featureChartEquiv (first second : F) : Chart F ≃ Chart F where
  toFun chart := (feature first second chart, chart.2)
  invFun output := (output.1 - output.2.1 * first - output.2.2 * second, output.2)
  left_inv chart := by
    rcases chart with ⟨base, scale, shear⟩
    dsimp [feature]
    congr 1
    ring
  right_inv output := by
    rcases output with ⟨color, scale, shear⟩
    dsimp [feature]
    congr 1
    ring

/-- Two features with different first inputs, together with the shear, are
three independent free coordinates. -/
def firstPairChartEquiv (u v u' v' : F) (hfirst : u' - u ≠ 0) : Chart F ≃ Chart F where
  toFun chart := (feature u v chart, feature u' v' chart, chart.2.2)
  invFun output :=
    let scale := (output.2.1 - output.1 - output.2.2 * (v' - v)) / (u' - u)
    (output.1 - scale * u - output.2.2 * v, scale, output.2.2)
  left_inv chart := by
    rcases chart with ⟨base, scale, shear⟩
    simp only [feature, Prod.mk.injEq, and_true]
    constructor <;> field_simp <;> ring
  right_inv output := by
    rcases output with ⟨color, other, shear⟩
    simp only [feature, Prod.mk.injEq, and_true]
    constructor <;> field_simp <;> ring

/-- Two features with different second inputs, together with the scale, are
three independent free coordinates. -/
def secondPairChartEquiv (u v u' v' : F) (hsecond : v' - v ≠ 0) : Chart F ≃ Chart F where
  toFun chart := (feature u v chart, feature u' v' chart, chart.2.1)
  invFun output :=
    let shear := (output.2.1 - output.1 - output.2.2 * (u' - u)) / (v' - v)
    (output.1 - output.2.2 * u - shear * v, output.2.2, shear)
  left_inv chart := by
    rcases chart with ⟨base, scale, shear⟩
    simp only [feature, Prod.mk.injEq, true_and]
    constructor <;> field_simp <;> ring
  right_inv output := by
    rcases output with ⟨color, other, scale⟩
    simp only [feature, Prod.mk.injEq, and_true]
    constructor <;> field_simp <;> ring

/-- For any two distinct source inputs, the ordered feature pair can be
completed to an explicit bijection of unrestricted charts. -/
noncomputable def pairChartEquiv (input other : F × F) (hne : input ≠ other) :
    Chart F ≃ Chart F := by
  classical
  by_cases hfirst : other.1 - input.1 = 0
  · have hsecond : other.2 - input.2 ≠ 0 := by
      intro h
      apply hne
      exact Prod.ext (sub_eq_zero.mp hfirst).symm (sub_eq_zero.mp h).symm
    exact secondPairChartEquiv input.1 input.2 other.1 other.2 hsecond
  · exact firstPairChartEquiv input.1 input.2 other.1 other.2 hfirst

@[simp] theorem pairChartEquiv_first (input other : F × F) (hne : input ≠ other)
    (chart : Chart F) :
    (pairChartEquiv input other hne chart).1 = feature input.1 input.2 chart := by
  classical
  unfold pairChartEquiv
  split_ifs <;> rfl

@[simp] theorem pairChartEquiv_second (input other : F × F) (hne : input ≠ other)
    (chart : Chart F) :
    (pairChartEquiv input other hne chart).2.1 = feature other.1 other.2 chart := by
  classical
  unfold pairChartEquiv
  split_ifs <;> rfl

end AffineFeatures

section UniformFeatures
open scoped Classical
variable {F : Type*} [Field F] [Fintype F]

/-- Projecting the first two unrestricted chart coordinates gives independent
uniform colors. -/
theorem uniform_chart_first_two :
    (FiniteDist.uniform (Chart F)).map (fun chart => (chart.1, chart.2.1)) =
      (FiniteDist.uniform F).prod (FiniteDist.uniform F) := by
  ext colors
  rcases colors with ⟨first, second⟩
  simp only [FiniteDist.map_weight, FiniteDist.uniform_weight, FiniteDist.prod_weight]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Prod.mk.injEq, Fintype.card_prod, Nat.cast_mul]
  have hF : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [ite_and]
  field_simp

/-- Each affine chart feature is independent uniform with the scale. -/
theorem feature_scale_uniform (first second : F) :
    (FiniteDist.uniform (Chart F)).map (fun chart => (feature first second chart, chart.2.1)) =
      (FiniteDist.uniform F).prod (FiniteDist.uniform F) := by
  have h := FiniteDist.uniform_map_equiv (featureChartEquiv first second)
  have hh := congrArg (fun p : FiniteDist (Chart F) =>
    p.map (fun chart => (chart.1, chart.2.1))) h
  dsimp only at hh
  rw [FiniteDist.map_map, uniform_chart_first_two] at hh
  exact hh

/-- The exact pairwise-independence assertion in V7's boundary-chart proof,
proved from explicit invertible affine coordinate changes. -/
theorem feature_pair_uniform (input other : F × F) (hne : input ≠ other) :
    (FiniteDist.uniform (Chart F)).map
      (fun chart => (feature input.1 input.2 chart, feature other.1 other.2 chart)) =
      (FiniteDist.uniform F).prod (FiniteDist.uniform F) := by
  have h := FiniteDist.uniform_map_equiv (pairChartEquiv input other hne)
  have hh := congrArg (fun p : FiniteDist (Chart F) =>
    p.map (fun chart => (chart.1, chart.2.1))) h
  dsimp only at hh
  rw [FiniteDist.map_map, uniform_chart_first_two] at hh
  simpa only [pairChartEquiv_first, pairChartEquiv_second] using hh

private theorem prod_map_first {α β : Type*} [Fintype α] [Fintype β]
    (p : FiniteDist α) (q : FiniteDist β) : (p.prod q).map Prod.fst = p := by
  ext a
  simp only [FiniteDist.map_weight, FiniteDist.prod_weight, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp [← Finset.mul_sum, q.sum_one]

private theorem prod_map_second {α β : Type*} [Fintype α] [Fintype β]
    (p : FiniteDist α) (q : FiniteDist β) : (p.prod q).map Prod.snd = q := by
  ext b
  simp only [FiniteDist.map_weight, FiniteDist.prod_weight, Fintype.sum_prod_type]
  simp [← Finset.sum_mul, p.sum_one]

/-- Every unrestricted affine feature is exactly uniform. -/
theorem feature_uniform (first second : F) :
    (FiniteDist.uniform (Chart F)).map (feature first second) = FiniteDist.uniform F := by
  have h := congrArg (fun p : FiniteDist (F × F) => p.map Prod.fst)
    (feature_scale_uniform first second)
  dsimp only at h
  rw [FiniteDist.map_map, prod_map_first] at h
  exact h

/-- The unrestricted scale is uniform and remains a public chart coordinate. -/
theorem scale_uniform :
    (FiniteDist.uniform (Chart F)).map (fun chart => chart.2.1) = FiniteDist.uniform F := by
  have h := congrArg (fun p : FiniteDist (F × F) => p.map Prod.snd)
    (feature_scale_uniform (0 : F) 0)
  dsimp only at h
  rw [FiniteDist.map_map, prod_map_second] at h
  exact h

/-- The scale-zero probability contributes exactly one deleted field value. -/
theorem nonzero_palette_failure :
    expectation (FiniteDist.uniform F) (paletteFailure (Finset.univ.erase (0 : F))) =
      (Fintype.card F : ℝ)⁻¹ := by
  simp [expectation_apply, FiniteDist.uniform_weight, paletteFailure, mul_ite, ite_not]

variable {I : Type*} [Fintype I]

/-- The actual deleted-color union budget for unrestricted affine charts. -/
noncomputable def affineDeletionBudget (allowed : I → Finset F) : ℝ :=
  (Fintype.card F : ℝ)⁻¹ + ∑ i, (1 - (allowed i).card / (Fintype.card F : ℝ))

/-- A positive law on actual affine charts, with nonzero scale and all exact
trimmed uniform feature marginals.  All independence and projection conditions
have been discharged; only the displayed finite numerical budget remains. -/
theorem affine_positive_chart (inputs : I → F × F) (hinj : Function.Injective inputs)
    (allowed : I → Finset F)
    (hsmall : (2 * Fintype.card I + 1) * affineDeletionBudget allowed ≤ 1 / 4) :
    ∃ law : FiniteDist (Chart F),
      (∀ chart, ¬ (chart.2.1 ≠ 0 ∧
        ∀ i, feature (inputs i).1 (inputs i).2 chart ∈ allowed i) → law.weight chart = 0) ∧
      (∀ i c, (law.map (feature (inputs i).1 (inputs i).2)).weight c =
        if c ∈ allowed i then ((allowed i).card : ℝ)⁻¹ else 0) := by
  let p := FiniteDist.uniform (Chart F)
  let features := fun i => feature (inputs i).1 (inputs i).2
  let auxiliary := fun chart : Chart F => chart.2.1
  let auxAllowed := Finset.univ.erase (0 : F)
  let safe := legalChart auxiliary auxAllowed features allowed
  have hfeature (i : I) : p.map (features i) = FiniteDist.uniform F :=
    feature_uniform _ _
  have hpair (i j : I) (hij : i ≠ j) :
      p.map (fun x => (features i x, features j x)) =
        (FiniteDist.uniform F).prod (FiniteDist.uniform F) :=
    feature_pair_uniform (inputs i) (inputs j) (fun h => hij (hinj h))
  have hauxpair (i : I) : p.map (fun x => (features i x, auxiliary x)) =
      (FiniteDist.uniform F).prod (FiniteDist.uniform F) := feature_scale_uniform _ _
  have hbudget : expectation (FiniteDist.uniform F) (paletteFailure auxAllowed) +
      ∑ i, expectation (FiniteDist.uniform F) (paletteFailure (allowed i)) =
        affineDeletionBudget allowed := by
    change expectation (FiniteDist.uniform F)
      (paletteFailure (Finset.univ.erase (0 : F))) + _ = _
    rw [nonzero_palette_failure]
    simp only [uniform_palette_failure, affineDeletionBudget]
  have hglobal : expectation p (badIndicator safe) ≤ affineDeletionBudget allowed := by
    rw [← hbudget]
    exact legalChart_global_budget p auxiliary auxAllowed features allowed scale_uniform hfeature
  have hconditional : ∀ i c, c ∈ allowed i →
      conditional p (features i) (badIndicator safe) c ≤ affineDeletionBudget allowed := by
    intro i c hc
    rw [← hbudget]
    exact legalChart_conditional_budget p auxiliary auxAllowed features allowed hfeature hpair
      hauxpair i c hc
  have hε : 0 ≤ affineDeletionBudget allowed := by
    apply le_trans _ hglobal
    exact Finset.sum_nonneg (fun x _ => mul_nonneg (p.nonneg x)
      (by unfold badIndicator; split_ifs <;> norm_num))
  obtain ⟨w, hmean, hw, hzero, _, hmarg⟩ := positive_chart_density p features allowed hfeature hpair
    safe (fun i x hx => hx.2 i) (affineDeletionBudget allowed) hε hglobal hconditional hsmall
  refine ⟨densityLaw p w hw hmean, ?_, ?_⟩
  · intro chart hbad
    have hn : ¬ safe chart := by
      simpa [safe, legalChart, auxiliary, auxAllowed, features] using hbad
    simp [densityLaw, hzero chart hn]
  · intro i c
    rw [densityLaw_marginal, hmarg]
    split_ifs with hc
    · have hF : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      field_simp
    · simp

end UniformFeatures


end BoundaryCalibration
end AFT
