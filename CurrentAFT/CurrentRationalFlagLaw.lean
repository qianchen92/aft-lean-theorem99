import CurrentAFT.AffineFlagCalibration
import CurrentAFT.AffineLegFeasibility

/-!
# Exact rational finite response for the current flag calibration

The matrix is the literal `Id - P(1_safeᶜ ·)` on the complete finite chart
table.  Its entries are rational.  The real deletion bound proves this
rational matrix invertible; no inverse or positive table is supplied as a
premise.  Bit-operation accounting for solving the table is separate.
-/

namespace CurrentAFT.CurrentRationalFlagLaw

open AFT AFT.BoundaryCalibration AffineFlagCalibration
open scoped BigOperators Classical

noncomputable section

variable {Ω C I : Type*} [Fintype Ω] [Fintype C] [Fintype I]

def realVector (f : Ω → ℚ) : Ω → ℝ := fun x => f x

def expectationQ : (Ω → ℚ) →ₗ[ℚ] ℚ where
  toFun f := (Fintype.card Ω : ℚ)⁻¹ * ∑ x, f x
  map_add' f g := by simp only [Pi.add_apply, Finset.sum_add_distrib, mul_add]
  map_smul' r f := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]; ring

def conditionalQ (feature : Ω → C) : (Ω → ℚ) →ₗ[ℚ] (C → ℚ) where
  toFun f c := (Fintype.card C : ℚ) * expectationQ (fun x => if feature x = c then f x else 0)
  map_add' f g := by
    funext c
    simp only [expectationQ, Pi.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
    simp_rw [ite_add_zero]
    rw [Finset.sum_add_distrib]
    ring
  map_smul' r f := by
    funext c
    have he : (fun x => if feature x = c then r * f x else 0) =
        r • (fun x => if feature x = c then f x else 0) := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      split_ifs <;> simp
    change (Fintype.card C : ℚ) * expectationQ (fun x => if feature x = c then r * f x else 0) =
      r * ((Fintype.card C : ℚ) * expectationQ (fun x => if feature x = c then f x else 0))
    rw [he, map_smul]
    simp only [smul_eq_mul]
    ring

def centerAllowedQ (allowed : Finset C) : (C → ℚ) →ₗ[ℚ] (C → ℚ) where
  toFun f c := if c ∈ allowed then f c - (∑ a ∈ allowed, f a) / allowed.card else 0
  map_add' f g := by
    funext c
    simp only [Pi.add_apply]
    split_ifs <;> simp [Finset.sum_add_distrib, add_div]
    ring
  map_smul' r f := by
    funext c
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp [← Finset.mul_sum, mul_sub, mul_div_assoc]

def featureProjectionQ (feature : Ω → C) (allowed : Finset C) :
    (Ω → ℚ) →ₗ[ℚ] (Ω → ℚ) :=
  (LinearMap.funLeft ℚ ℚ feature).comp ((centerAllowedQ allowed).comp (conditionalQ feature))

def projectionQ (features : I → Ω → C) (allowed : I → Finset C) :
    (Ω → ℚ) →ₗ[ℚ] (Ω → ℚ) where
  toFun f x := expectationQ f + ∑ i, featureProjectionQ (features i) (allowed i) f x
  map_add' f g := by
    funext x
    simp only [map_add, Pi.add_apply, Finset.sum_add_distrib]
    ring
  map_smul' r f := by
    funext x
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← Finset.mul_sum]
    ring

def badMaskQ (safe : Ω → Prop) : (Ω → ℚ) →ₗ[ℚ] (Ω → ℚ) where
  toFun f x := if safe x then 0 else f x
  map_add' f g := by funext x; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' r f := by funext x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp

def responseQ (features : I → Ω → C) (allowed : I → Finset C) (safe : Ω → Prop) :
    (Ω → ℚ) →ₗ[ℚ] (Ω → ℚ) :=
  LinearMap.id - (projectionQ features allowed).comp (badMaskQ safe)

theorem expectationQ_cast [Nonempty Ω] (f : Ω → ℚ) :
    (expectationQ f : ℝ) = expectation (FiniteDist.uniform Ω) (realVector f) := by
  simp only [expectationQ, LinearMap.coe_mk, AddHom.coe_mk, Rat.cast_mul, Rat.cast_inv,
    Rat.cast_natCast, Rat.cast_sum, expectation_apply, FiniteDist.uniform_weight, realVector,
    Finset.mul_sum]

theorem conditionalQ_cast [Nonempty Ω] (feature : Ω → C) (f : Ω → ℚ) (c : C) :
    (conditionalQ feature f c : ℝ) = conditional (FiniteDist.uniform Ω) feature (realVector f) c := by
  simp only [conditionalQ, LinearMap.coe_mk, AddHom.coe_mk, Rat.cast_mul,
    Rat.cast_natCast, expectationQ_cast, conditional_apply]
  congr 2
  funext x
  simp only [realVector]
  split_ifs <;> simp

omit [Fintype C] in
theorem centerAllowedQ_cast (allowed : Finset C) (f : C → ℚ) (c : C) :
    (centerAllowedQ allowed f c : ℝ) = centerAllowed allowed (realVector f) c := by
  simp only [centerAllowedQ, LinearMap.coe_mk, AddHom.coe_mk, centerAllowed_apply, realVector]
  split_ifs <;> simp only [Rat.cast_sub, Rat.cast_div, Rat.cast_sum, Rat.cast_natCast, Rat.cast_zero]

theorem featureProjectionQ_cast [Nonempty Ω] (feature : Ω → C) (allowed : Finset C)
    (f : Ω → ℚ) (x : Ω) :
    (featureProjectionQ feature allowed f x : ℝ) =
      featureProjection (FiniteDist.uniform Ω) feature allowed (realVector f) x := by
  change (centerAllowedQ allowed (conditionalQ feature f) (feature x) : ℝ) = _
  rw [centerAllowedQ_cast]
  have hc : realVector (conditionalQ feature f) = conditional (FiniteDist.uniform Ω) feature (realVector f) :=
    funext (conditionalQ_cast feature f)
  rw [hc]
  rfl

theorem projectionQ_cast [Nonempty Ω] (features : I → Ω → C) (allowed : I → Finset C)
    (f : Ω → ℚ) (x : Ω) :
    (projectionQ features allowed f x : ℝ) =
      chartProjection (FiniteDist.uniform Ω) features allowed (realVector f) x := by
  simp only [projectionQ, LinearMap.coe_mk, AddHom.coe_mk, Rat.cast_add, Rat.cast_sum,
    expectationQ_cast, featureProjectionQ_cast, chartProjection_apply]
  rfl

theorem responseQ_cast [Nonempty Ω] (features : I → Ω → C) (allowed : I → Finset C)
    (safe : Ω → Prop) (f : Ω → ℚ) :
    realVector (responseQ features allowed safe f) = realVector f -
      deletion (chartProjection (FiniteDist.uniform Ω) features allowed) safe (realVector f) := by
  funext x
  change ((f x - projectionQ features allowed (badMaskQ safe f) x : ℚ) : ℝ) = _
  rw [Rat.cast_sub, projectionQ_cast]
  have hb : realVector (badMaskQ safe f) = realVector f - safeMask safe (realVector f) := by
    funext y
    simp only [badMaskQ, realVector, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply, safeMask_apply]
    split_ifs <;> simp
  rw [hb]
  rfl

theorem contraction_response_injective (D : (Ω → ℝ) →L[ℝ] (Ω → ℝ)) (hD : ‖D‖ < 1) :
    Function.Injective (fun f : Ω → ℝ => f - D f) := by
  intro f g heq
  have hd : f - g = D (f - g) := by rw [map_sub]; linear_combination heq
  have hn : ‖f - g‖ ≤ ‖D‖ * ‖f - g‖ := by
    conv_lhs => rw [hd]
    exact D.le_opNorm _
  have hz : ‖f - g‖ = 0 := by nlinarith [norm_nonneg (f - g)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

variable [DecidableEq Ω]

def responseMatrix (features : I → Ω → C) (allowed : I → Finset C) (safe : Ω → Prop) :
    Matrix Ω Ω ℚ := LinearMap.toMatrix' (responseQ features allowed safe)

def solve (features : I → Ω → C) (allowed : I → Finset C) (safe : Ω → Prop)
    (target : Ω → ℚ) : Ω → ℚ := (responseMatrix features allowed safe)⁻¹.mulVec target

theorem responseMatrix_isUnit [Nonempty Ω] (features : I → Ω → C) (allowed : I → Finset C)
    (safe : Ω → Prop)
    (hD : ‖deletion (chartProjection (FiniteDist.uniform Ω) features allowed) safe‖ < 1) :
    IsUnit (responseMatrix features allowed safe) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro f g hfg
  have hq : responseQ features allowed safe f = responseQ features allowed safe g := by
    simpa only [responseMatrix, LinearMap.toMatrix'_mulVec] using hfg
  have hr := congrArg realVector hq
  rw [responseQ_cast, responseQ_cast] at hr
  have hi := contraction_response_injective _ hD hr
  funext x
  exact Rat.cast_injective (congrFun hi x)

theorem solve_equation [Nonempty Ω] (features : I → Ω → C) (allowed : I → Finset C)
    (safe : Ω → Prop)
    (hD : ‖deletion (chartProjection (FiniteDist.uniform Ω) features allowed) safe‖ < 1)
    (target : Ω → ℚ) : responseQ features allowed safe (solve features allowed safe target) = target := by
  have hu := responseMatrix_isUnit features allowed safe hD
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hu
  rw [← LinearMap.toMatrix'_mulVec (responseQ features allowed safe)]
  change (responseMatrix features allowed safe).mulVec
    ((responseMatrix features allowed safe)⁻¹.mulVec target) = _
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd, Matrix.one_mulVec]

theorem solve_cast [Nonempty Ω] (features : I → Ω → C) (allowed : I → Finset C)
    (safe : Ω → Prop)
    (hD : ‖deletion (chartProjection (FiniteDist.uniform Ω) features allowed) safe‖ < 1)
    (target : Ω → ℚ) :
    realVector (solve features allowed safe target) =
      neumannSolve (deletion (chartProjection (FiniteDist.uniform Ω) features allowed) safe) hD (realVector target) := by
  apply contraction_response_injective _ hD
  exact ((responseQ_cast features allowed safe (solve features allowed safe target)).symm.trans
    (congrArg realVector (solve_equation features allowed safe hD target))).trans
      (neumannSolve_equation _ hD (realVector target)).symm

def offLineDefectQ (features : I → Ω → C) (allowed : I → Finset C)
    (line : I → Prop) (spike : Ω → ℚ) : Ω → ℚ :=
  ∑ i, if line i then 0 else featureProjectionQ (features i) (allowed i) spike

def regularDensityQ (features : I → Ω → C) (allowed : I → Finset C)
    (line : I → Prop) (safe : Ω → Prop) (atom : ℚ) (spike : Ω → ℚ) : Ω → ℚ :=
  fun x => if safe x then solve features allowed safe
    (1 - (atom / (1 - atom)) • offLineDefectQ features allowed line spike) x else 0

omit [DecidableEq Ω] in
theorem offLineDefectQ_cast [Nonempty Ω] (features : I → Ω → C) (allowed : I → Finset C)
    (line : I → Prop) (spike : Ω → ℚ) :
    realVector (offLineDefectQ features allowed line spike) =
      offLineDefect (FiniteDist.uniform Ω) features allowed line (realVector spike) := by
  funext x
  simp only [realVector, offLineDefectQ, offLineDefect, Finset.sum_apply, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : line i
  · simp only [if_pos hi, Pi.zero_apply, Rat.cast_zero]
  · simp only [if_neg hi, featureProjectionQ_cast]

theorem regularDensityQ_cast [Nonempty Ω] (features : I → Ω → C) (allowed : I → Finset C)
    (line : I → Prop) (safe : Ω → Prop) (atom : ℚ) (spike : Ω → ℚ)
    (hD : ‖deletion (chartProjection (FiniteDist.uniform Ω) features allowed) safe‖ < 1) :
    realVector (regularDensityQ features allowed line safe atom spike) =
      regularDensity (FiniteDist.uniform Ω) features allowed line safe atom (realVector spike) hD := by
  let target : Ω → ℚ := 1 - (atom / (1 - atom)) • offLineDefectQ features allowed line spike
  have htarget : realVector target = (1 : Ω → ℝ) -
      ((atom : ℝ) / (1 - (atom : ℝ))) • offLineDefect (FiniteDist.uniform Ω) features allowed line (realVector spike) := by
    funext x
    have hd := congrFun (offLineDefectQ_cast features allowed line spike) x
    change ((1 - atom / (1 - atom) * offLineDefectQ features allowed line spike x : ℚ) : ℝ) = _
    simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_one, Pi.sub_apply,
      Pi.one_apply, Pi.smul_apply, smul_eq_mul]
    rw [show (offLineDefectQ features allowed line spike x : ℝ) = _ from hd]
  have hraw := solve_cast features allowed safe hD target
  rw [htarget] at hraw
  funext x
  change ((if safe x then solve features allowed safe target x else 0 : ℚ) : ℝ) = _
  rw [regularDensity, safeMask_apply]
  by_cases hx : safe x
  · simp only [if_pos hx]
    exact congrFun hraw x
  · simp only [if_neg hx, Rat.cast_zero]

structure RegularCertificate [Nonempty Ω] (features : I → Ω → C) (allowed : I → Finset C)
    (line : I → Prop) (safe : Ω → Prop) (atom : ℚ) (spike density : Ω → ℚ) where
  mass : expectation (FiniteDist.uniform Ω) (realVector density) = 1
  nonneg : ∀ x, 0 ≤ (density x : ℝ)
  support : ∀ x, ¬ safe x → density x = 0
  lower : ∀ x, safe x → (1 / 3 : ℝ) ≤ density x
  on_line : ∀ i, line i → ∀ c,
    conditional (FiniteDist.uniform Ω) (features i) (realVector density) c =
      if c ∈ allowed i then (Fintype.card C : ℝ) / (allowed i).card else 0
  off_line : ∀ i, ¬ line i → ∀ c,
    conditional (FiniteDist.uniform Ω) (features i)
      ((1 - (atom : ℝ)) • realVector density + (atom : ℝ) • realVector spike) c =
        if c ∈ allowed i then (Fintype.card C : ℝ) / (allowed i).card else 0

theorem regularDensityQ_certificate [Nonempty Ω] [Nonempty C]
    (features : I → Ω → C) (allowed : I → Finset C) (line : I → Prop)
    (hfeature : ∀ i, (FiniteDist.uniform Ω).map (features i) = FiniteDist.uniform C)
    (hpair : ∀ i j, i ≠ j → (FiniteDist.uniform Ω).map (fun x => (features i x, features j x)) =
      (FiniteDist.uniform C).prod (FiniteDist.uniform C))
    (safe : Ω → Prop) (hallowed : ∀ i x, safe x → features i x ∈ allowed i)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hglobal : expectation (FiniteDist.uniform Ω) (badIndicator safe) ≤ δ)
    (hconditional : ∀ i c, c ∈ allowed i →
      conditional (FiniteDist.uniform Ω) (features i) (badIndicator safe) c ≤ δ)
    (hsmall : (2 * Fintype.card I + 1) * δ ≤ 1 / 4)
    (hpositivity : (Fintype.card I : ℝ) / (1 - δ) *
      (δ + ((2 * Fintype.card I + 1) * δ) /
        (1 - (2 * Fintype.card I + 1) * δ)) ≤ 1 / 3)
    (atom : ℚ) (ha0 : 0 ≤ (atom : ℝ)) (haHalf : (atom : ℝ) ≤ 1 / 2)
    (spike : Ω → ℚ) (hsmean : expectation (FiniteDist.uniform Ω) (realVector spike) = 1)
    (hsnonneg : ∀ x, 0 ≤ (spike x : ℝ))
    (hsallowed : ∀ i, ¬ line i → ∀ x, features i x ∉ allowed i → spike x = 0)
    (hsbound : ∀ i, ¬ line i → ∀ c,
      conditional (FiniteDist.uniform Ω) (features i) (realVector spike) c ≤ 1 / (1 - δ)) :
    RegularCertificate features allowed line safe atom spike
      (regularDensityQ features allowed line safe atom spike) := by
  have hquarter : ‖deletion (chartProjection (FiniteDist.uniform Ω) features allowed) safe‖ ≤ 1 / 4 :=
    (chartDeletion_norm _ features allowed safe δ hδ0 hglobal hconditional).trans hsmall
  have hD : ‖deletion (chartProjection (FiniteDist.uniform Ω) features allowed) safe‖ < 1 :=
    hquarter.trans_lt (by norm_num)
  have h := regularDensity_properties (FiniteDist.uniform Ω) features allowed line hfeature hpair
    safe hallowed δ hδ0 hδ1 hglobal hconditional hsmall hpositivity (atom : ℝ) ha0 haHalf
    (realVector spike) hsmean hsnonneg
    (by intro i hi x hx; change (spike x : ℝ) = 0; rw [hsallowed i hi x hx]; norm_num)
    hsbound hD
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at h
  rw [← regularDensityQ_cast features allowed line safe atom spike hD] at h
  refine ⟨h.1, h.2.1, ?_, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
  intro x hx
  exact Rat.cast_injective (by simpa only [realVector, Rat.cast_zero] using h.2.2.1 x hx)

section MarkedFiber

variable {F : Type*} [Field F] [Fintype F]

def markedScaleSet (inputs : I → F × F) (allowed : I → Finset F) (mark : F) : Finset F :=
  Finset.univ.filter (markedScaleSafe inputs allowed mark)

def markedSurvivalQ (inputs : I → F × F) (allowed : I → Finset F) (mark : F) : ℚ :=
  (markedScaleSet inputs allowed mark).card / (Fintype.card F : ℚ)

omit [Fintype I] in
theorem markedSurvivalQ_cast (inputs : I → F × F) (allowed : I → Finset F) (mark : F) :
    (markedSurvivalQ inputs allowed mark : ℝ) = markedSurvival inputs allowed mark := by
  simp only [markedSurvivalQ, Rat.cast_div, Rat.cast_natCast, markedSurvival,
    eventMass, expectation_apply, FiniteDist.uniform_weight, eventIndicator,
    mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  simp only [markedScaleSet, Finset.sum_const, nsmul_eq_mul]
  ring

/-- The actual normalized marked branch, as a finite rational table. -/
def markedDensityQ (inputs : I → F × F) (allowed : I → Finset F) (mark : F) : Chart F → ℚ :=
  fun chart => (Fintype.card F : ℚ) ^ 2 / markedSurvivalQ inputs allowed mark *
    if chart.1 = mark ∧ chart.2.2 = 0 ∧ markedScaleSafe inputs allowed mark chart.2.1 then 1 else 0

omit [Fintype I] in
theorem markedChartLaw_weight (inputs : I → F × F) (allowed : I → Finset F) (mark : F)
    (hpos : 0 < markedSurvival inputs allowed mark) (chart : Chart F) :
    (markedChartLaw inputs allowed mark hpos).weight chart =
      if chart.1 = mark ∧ chart.2.2 = 0 then
        (markedScaleLaw inputs allowed mark hpos).weight chart.2.1 else 0 := by
  rcases chart with ⟨base, scale, shear⟩
  by_cases hb : base = mark
  · subst base
    by_cases hs : shear = 0
    · subst shear
      simp only [markedChartLaw, FiniteDist.map_weight, Prod.mk.injEq, true_and, and_true,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
    · simp [markedChartLaw, FiniteDist.map_weight, hs, Ne.symm hs]
  · simp [markedChartLaw, FiniteDist.map_weight, hb, Ne.symm hb]

omit [Fintype I] in
theorem markedDensityQ_cast (inputs : I → F × F) (allowed : I → Finset F) (mark : F)
    (hpos : 0 < markedSurvival inputs allowed mark) :
    realVector (markedDensityQ inputs allowed mark) =
      uniformDensity (markedChartLaw inputs allowed mark hpos) := by
  funext chart
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [realVector, markedDensityQ, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_natCast, markedSurvivalQ_cast, uniformDensity, markedChartLaw_weight,
    markedScaleLaw, densityLaw, FiniteDist.uniform_weight, restrictedDensity]
  rw [show eventMass (FiniteDist.uniform F) (markedScaleSafe inputs allowed mark) =
    markedSurvival inputs allowed mark from rfl]
  by_cases hb : chart.1 = mark ∧ chart.2.2 = 0
  · by_cases hs : markedScaleSafe inputs allowed mark chart.2.1
    · simp only [hb.1, hb.2, hs, and_self, if_true, Rat.cast_one, eventIndicator]
      simp only [Chart, Fintype.card_prod, Nat.cast_mul]
      field_simp [hq, hpos.ne']
    · simp only [hb.1, hb.2, hs, and_false, and_self, if_false, if_true, Rat.cast_zero, mul_zero,
        eventIndicator, zero_div]
  · have hn : ¬ (chart.1 = mark ∧ chart.2.2 = 0 ∧ markedScaleSafe inputs allowed mark chart.2.1) :=
      fun h => hb ⟨h.1, h.2.1⟩
    simp only [if_neg hn, if_neg hb, Rat.cast_zero, mul_zero]

def affineFeatures (inputs : I → F × F) : I → Chart F → F :=
  fun i => feature (inputs i).1 (inputs i).2

def affineSafe (inputs : I → F × F) (allowed : I → Finset F) : Chart F → Prop :=
  legalChart (fun chart => chart.2.1) (Finset.univ.erase 0) (affineFeatures inputs) allowed

theorem affine_regular_certificate (inputs : I → F × F) (hinj : Function.Injective inputs)
    (allowed : I → Finset F) (mark : F)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hbudget : affineDeletionBudget allowed ≤ δ)
    (hsmall : (2 * Fintype.card I + 1) * δ ≤ 1 / 4)
    (hpositivity : (Fintype.card I : ℝ) / (1 - δ) *
      (δ + ((2 * Fintype.card I + 1) * δ) /
        (1 - (2 * Fintype.card I + 1) * δ)) ≤ 1 / 3)
    (atom : ℚ) (ha0 : 0 ≤ (atom : ℝ)) (haHalf : (atom : ℝ) ≤ 1 / 2) :
    RegularCertificate (affineFeatures inputs) allowed (fun i => (inputs i).1 = 0)
      (affineSafe inputs allowed) atom (markedDensityQ inputs allowed mark)
      (regularDensityQ (affineFeatures inputs) allowed (fun i => (inputs i).1 = 0)
        (affineSafe inputs allowed) atom (markedDensityQ inputs allowed mark)) := by
  let p := FiniteDist.uniform (Chart F)
  have hfeature (i : I) : p.map (affineFeatures inputs i) = FiniteDist.uniform F := feature_uniform _ _
  have hpair (i j : I) (hij : i ≠ j) :
      p.map (fun x => (affineFeatures inputs i x, affineFeatures inputs j x)) =
        (FiniteDist.uniform F).prod (FiniteDist.uniform F) :=
    feature_pair_uniform (inputs i) (inputs j) (fun h => hij (hinj h))
  have hauxpair (i : I) : p.map (fun x => (affineFeatures inputs i x, x.2.1)) =
      (FiniteDist.uniform F).prod (FiniteDist.uniform F) := feature_scale_uniform _ _
  have hbudgetFormula : expectation (FiniteDist.uniform F) (paletteFailure (Finset.univ.erase 0)) +
      ∑ i, expectation (FiniteDist.uniform F) (paletteFailure (allowed i)) = affineDeletionBudget allowed := by
    rw [nonzero_palette_failure]
    simp only [uniform_palette_failure, affineDeletionBudget]
  have hglobal : expectation p (badIndicator (affineSafe inputs allowed)) ≤ δ := by
    apply le_trans _ hbudget
    rw [← hbudgetFormula]
    exact legalChart_global_budget p (fun chart => chart.2.1) (Finset.univ.erase 0)
      (affineFeatures inputs) allowed scale_uniform hfeature
  have hconditional : ∀ i c, c ∈ allowed i →
      conditional p (affineFeatures inputs i) (badIndicator (affineSafe inputs allowed)) c ≤ δ := by
    intro i c hc
    apply le_trans _ hbudget
    rw [← hbudgetFormula]
    exact legalChart_conditional_budget p _ _ (affineFeatures inputs) allowed hfeature hpair hauxpair i c hc
  have hsurvival : 0 < markedSurvival inputs allowed mark := by
    have hl := markedSurvival_lower inputs allowed mark
    linarith
  have hspike := markedDensityQ_cast inputs allowed mark hsurvival
  apply regularDensityQ_certificate (affineFeatures inputs) allowed (fun i => (inputs i).1 = 0)
    hfeature hpair (affineSafe inputs allowed) (fun i x hx => hx.2 i)
    δ hδ0 hδ1 hglobal hconditional hsmall hpositivity atom ha0 haHalf
    (markedDensityQ inputs allowed mark)
  · rw [hspike]
    exact uniformDensity_mean _
  · intro x
    change realVector (markedDensityQ inputs allowed mark) x ≥ 0
    rw [hspike]
    exact uniformDensity_nonneg _ _
  · intro i hi chart hc
    have hzR : (markedDensityQ inputs allowed mark chart : ℝ) = 0 := by
      change realVector (markedDensityQ inputs allowed mark) chart = (0 : ℝ)
      rw [hspike]
      have hz := markedChartLaw_support inputs allowed mark hsurvival chart
        (by rintro ⟨_, _, _, hh⟩; exact hc (hh i hi))
      simp only [uniformDensity, hz, mul_zero]
    exact_mod_cast hzR
  · intro i hi c
    rw [hspike]
    exact markedDensity_bound inputs allowed mark δ hδ1 hbudget hsurvival i hi c

end MarkedFiber

end
end CurrentAFT.CurrentRationalFlagLaw
