import CurrentAFT.CurrentRationalFlagLaw
import CurrentAFT.AffineLawSpec

/-!
# A canonical exact rational flag and chart table

The ideal table is built from the literal finite rational response matrix.
It has the same simultaneous marginal and safe-support specification as
the real construction, with no arbitrary selection of a positive law.
The binary finite-iteration implementation is developed separately from
this exact table semantics.
-/

namespace CurrentAFT.CurrentFlagProgram

open AFT AFT.BoundaryCalibration AffineFlagCalibration CurrentRationalFlagLaw
open scoped BigOperators Classical

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentRationalFlagLaw.solve CurrentRationalFlagLaw.responseMatrix

variable {F I : Type*} [Field F] [Fintype F] [Fintype I]

structure RationalModel (inputs : I → F × F) (allowed : I → Finset F) (mark : F) (atom : ℚ) where
  model : SimultaneousLaw inputs allowed mark (atom : ℝ)
  table : Bool × Chart F → ℚ
  table_cast : ∀ point, (table point : ℝ) = model.joint.weight point

theorem RationalModel.table_nonneg {inputs : I → F × F} {allowed : I → Finset F}
    {mark : F} {atom : ℚ} (data : RationalModel inputs allowed mark atom) (point : Bool × Chart F) :
    0 ≤ data.table point := by
  have h := data.model.joint.nonneg point
  rw [← data.table_cast point] at h
  exact_mod_cast h

theorem RationalModel.table_mass {inputs : I → F × F} {allowed : I → Finset F}
    {mark : F} {atom : ℚ} (data : RationalModel inputs allowed mark atom) :
    ∑ point, data.table point = 1 := by
  have h : ((∑ point, data.table point : ℚ) : ℝ) = 1 := by
    simp only [Rat.cast_sum, data.table_cast]
    exact data.model.joint.sum_one
  exact_mod_cast h

def regularDensity (inputs : I → F × F) (allowed : I → Finset F) (mark : F) (atom : ℚ) : Chart F → ℚ :=
  regularDensityQ (affineFeatures inputs) allowed (fun i => (inputs i).1 = 0)
    (affineSafe inputs allowed) atom (markedDensityQ inputs allowed mark)

def table (inputs : I → F × F) (allowed : I → Finset F) (mark : F) (atom : ℚ) : Bool × Chart F → ℚ :=
  fun point => if point.1 then atom * ((Fintype.card (Chart F) : ℚ)⁻¹ * markedDensityQ inputs allowed mark point.2)
    else (1 - atom) * ((Fintype.card (Chart F) : ℚ)⁻¹ * regularDensity inputs allowed mark atom point.2)

def make (inputs : I → F × F) (hinj : Function.Injective inputs)
    (allowed : I → Finset F) (mark : F)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hbudget : affineDeletionBudget allowed ≤ δ)
    (hsmall : (2 * Fintype.card I + 1) * δ ≤ 1 / 4)
    (hpositivity : (Fintype.card I : ℝ) / (1 - δ) *
      (δ + ((2 * Fintype.card I + 1) * δ) /
        (1 - (2 * Fintype.card I + 1) * δ)) ≤ 1 / 3)
    (atom : ℚ) (ha0 : 0 ≤ (atom : ℝ)) (haHalf : (atom : ℝ) ≤ 1 / 2) :
    RationalModel inputs allowed mark atom := by
  let densityQ := regularDensity inputs allowed mark atom
  let cert : RegularCertificate (affineFeatures inputs) allowed (fun i => (inputs i).1 = 0)
      (affineSafe inputs allowed) atom (markedDensityQ inputs allowed mark) densityQ :=
    affine_regular_certificate inputs hinj allowed mark δ hδ0 hδ1 hbudget hsmall hpositivity atom ha0 haHalf
  let p := FiniteDist.uniform (Chart F)
  let regular := densityLaw p (realVector densityQ) cert.nonneg cert.mass
  have hsurvival : 0 < markedSurvival inputs allowed mark := by
    have hl := markedSurvival_lower inputs allowed mark
    linarith
  let marked := markedChartLaw inputs allowed mark hsurvival
  let joint := flagLaw (atom : ℝ) ha0 (by linarith : (atom : ℝ) ≤ 1) regular marked
  have hspike : realVector (markedDensityQ inputs allowed mark) = uniformDensity marked :=
    markedDensityQ_cast inputs allowed mark hsurvival
  have hregular (i : I) (hi : (inputs i).1 = 0) (c : F) :
      (regular.map (feature (inputs i).1 (inputs i).2)).weight c =
        if c ∈ allowed i then ((allowed i).card : ℝ)⁻¹ else 0 := by
    rw [densityLaw_marginal]
    have hc := cert.on_line i hi c
    change conditional p (feature (inputs i).1 (inputs i).2) (realVector densityQ) c = _ at hc
    rw [hc]
    split_ifs
    · have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      field_simp
    · simp
  have hon (i : I) (hi : (inputs i).1 = 0) (c : F) :
      (joint.map (fun point => feature (inputs i).1 (inputs i).2 point.2)).weight c =
        (1 - (atom : ℝ)) * (if c ∈ allowed i then ((allowed i).card : ℝ)⁻¹ else 0) +
          (atom : ℝ) * (if c = mark then 1 else 0) := by
    rw [flagLaw_feature, hregular i hi c, markedChartLaw_line inputs allowed mark hsurvival i hi c]
  have hoff (i : I) (hi : (inputs i).1 ≠ 0) (c : F) :
      (joint.map (fun point => feature (inputs i).1 (inputs i).2 point.2)).weight c =
        if c ∈ allowed i then ((allowed i).card : ℝ)⁻¹ else 0 := by
    rw [flagLaw_feature, densityLaw_marginal]
    have hf := cert.off_line i hi c
    change conditional p (affineFeatures inputs i)
      ((1 - (atom : ℝ)) • realVector densityQ + (atom : ℝ) • realVector (markedDensityQ inputs allowed mark)) c = _ at hf
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hf
    rw [hspike, uniformDensity_conditional] at hf
    change (1 - (atom : ℝ)) * (conditional p (affineFeatures inputs i) (realVector densityQ) c /
      Fintype.card F) + (atom : ℝ) * (marked.map (affineFeatures inputs i)).weight c = _
    have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    split_ifs at hf ⊢ <;> field_simp <;> nlinarith [hf]
  let model : SimultaneousLaw inputs allowed mark (atom : ℝ) :=
    { regular := regular
      marked := marked
      joint := joint
      decomposition := by intro point; rfl
      regular_support := by
        intro chart hn
        have hsafe : ¬ affineSafe inputs allowed chart := by
          simpa only [affineSafe, legalChart, affineFeatures, Finset.mem_erase,
            Finset.mem_univ, and_true] using hn
        change p.weight chart * (densityQ chart : ℝ) = 0
        rw [cert.support chart hsafe, Rat.cast_zero, mul_zero]
      regular_lower := by
        intro chart hn hc
        have hsafe : affineSafe inputs allowed chart := by
          simpa only [affineSafe, legalChart, affineFeatures, Finset.mem_erase,
            Finset.mem_univ, and_true] using And.intro hn hc
        change (Fintype.card (Chart F) : ℝ)⁻¹ / 3 ≤
          (Fintype.card (Chart F) : ℝ)⁻¹ * (densityQ chart : ℝ)
        have hh := mul_le_mul_of_nonneg_left (cert.lower chart hsafe)
          (inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card (Chart F)) : (0 : ℝ) ≤ _))
        simpa only [div_eq_mul_inv, one_mul] using hh
      marked_support := markedChartLaw_support inputs allowed mark hsurvival
      flag_marginal := flagLaw_flag (atom : ℝ) ha0 (by linarith) regular marked
      on_line := hon
      off_line := hoff }
  refine ⟨model, table inputs allowed mark atom, ?_⟩
  intro point
  have hm : (Fintype.card (Chart F) : ℝ)⁻¹ *
      (markedDensityQ inputs allowed mark point.2 : ℝ) = marked.weight point.2 := by
    have h := congrFun hspike point.2
    change (markedDensityQ inputs allowed mark point.2 : ℝ) =
      (Fintype.card (Chart F) : ℝ) * marked.weight point.2 at h
    rw [h, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]
  change ((if point.1 then atom * ((Fintype.card (Chart F) : ℚ)⁻¹ * markedDensityQ inputs allowed mark point.2)
    else (1 - atom) * ((Fintype.card (Chart F) : ℚ)⁻¹ * densityQ point.2) : ℚ) : ℝ) = _
  rw [model.decomposition]
  cases point.1 <;> simp only [Bool.false_eq_true, if_false, if_true, Rat.cast_mul, Rat.cast_inv,
    Rat.cast_natCast, Rat.cast_sub, Rat.cast_one, hm]
  all_goals rfl

local instance currentFlagModulusNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩
local instance currentFlagModulusPrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩

/-- Exact rational ideal at the current public sizes, for every protected
input simultaneously.  Only public data occur among the arguments. -/
def current (security : ℕ) (baseline : ℤ) (hbaseline : |baseline| ≤ legOffsetBound security)
    (mark : ZMod (Parameters.modulus security)) (atom : ℚ)
    (ha0 : 0 ≤ (atom : ℝ)) (haHalf : (atom : ℝ) ≤ 1 / 2) :
    RationalModel (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security))
      (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline)
      mark atom := by
  have hb := leg_budget_conditions security
  exact make (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security))
    (protectedInputs_injective _ _ (leg_input_separation security))
    (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline)
    mark (legDeletionUpper security) hb.1 hb.2.1 (protectedPalette_current_budget security baseline hbaseline)
    hb.2.2.1 hb.2.2.2 atom ha0 haHalf

attribute [irreducible] make current

end
end CurrentAFT.CurrentFlagProgram
