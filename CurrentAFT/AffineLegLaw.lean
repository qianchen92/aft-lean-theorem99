import CurrentAFT.AffineLegFeasibility
import CurrentAFT.AffineLawSpec
import CurrentAFT.CurrentFlagProgram

/-!
# The current source-independent positive flag and chart law

`currentLaw` is selected once from public offset, prescribed color, and
branch weight.  The protected input is an argument only to its correctness
theorems, never to the sampled distribution.
-/

namespace CurrentAFT.AffineFlagCalibration

open AFT AFT.BoundaryCalibration
open scoped BigOperators Classical

noncomputable section

theorem exists_simultaneousLaw {F I : Type*} [Field F] [Fintype F] [Fintype I]
    (inputs : I → F × F) (hinj : Function.Injective inputs)
    (allowed : I → Finset F) (mark : F)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hbudget : affineDeletionBudget allowed ≤ δ)
    (hsmall : (2 * Fintype.card I + 1) * δ ≤ 1 / 4)
    (hpositivity : (Fintype.card I : ℝ) / (1 - δ) *
      (δ + ((2 * Fintype.card I + 1) * δ) /
        (1 - (2 * Fintype.card I + 1) * δ)) ≤ 1 / 3)
    (atom : ℝ) (ha0 : 0 ≤ atom) (haHalf : atom ≤ 1 / 2) :
    Nonempty (SimultaneousLaw inputs allowed mark atom) := by
  obtain ⟨regular, marked, joint, hjoint, hs, hl, hm, hf, hon, hoff⟩ :=
    affine_flag_law inputs hinj allowed mark δ hδ0 hδ1 hbudget hsmall hpositivity atom ha0 haHalf
  exact ⟨⟨regular, marked, joint, by intro point; rw [hjoint]; rfl,
    hs, hl, hm, hf, hon, hoff⟩⟩

local instance legLawModulusNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩

local instance currentModulusPrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩

/-- The complete current public law.  All feasibility obligations are
discharged at the current polynomial sizes, for every security parameter. -/
def currentLaw (security : ℕ) (baseline : ℤ) (hbaseline : |baseline| ≤ legOffsetBound security)
    (mark : ZMod (Parameters.modulus security)) (atom : ℝ)
    (ha0 : 0 ≤ atom) (haHalf : atom ≤ 1 / 2) :
    SimultaneousLaw (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security))
      (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline)
      mark atom := by
  by_cases hrational : ∃ value : ℚ, (value : ℝ) = atom
  · let value := Classical.choose hrational
    have hvalue : (value : ℝ) = atom := Classical.choose_spec hrational
    have hnonneg : 0 ≤ (value : ℝ) := by rw [hvalue]; exact ha0
    have hhalf : (value : ℝ) ≤ 1 / 2 := by rw [hvalue]; exact haHalf
    exact hvalue ▸ (CurrentFlagProgram.current security baseline hbaseline mark value hnonneg hhalf).model
  · have hb := leg_budget_conditions security
    exact Classical.choice (exists_simultaneousLaw
      (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security))
      (protectedInputs_injective _ _ (leg_input_separation security))
      (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline)
      mark (legDeletionUpper security) hb.1 hb.2.1
      (protectedPalette_current_budget security baseline hbaseline) hb.2.2.1 hb.2.2.2 atom ha0 haHalf)

private theorem rational_model_transport (security : ℕ) (baseline : ℤ)
    (hbaseline : |baseline| ≤ legOffsetBound security) (mark : ZMod (Parameters.modulus security))
    (left right : ℚ) (hl0 : 0 ≤ (left : ℝ)) (hlHalf : (left : ℝ) ≤ 1 / 2)
    (hr0 : 0 ≤ (right : ℝ)) (hrHalf : (right : ℝ) ≤ 1 / 2)
    (hcast : (left : ℝ) = (right : ℝ)) :
    hcast ▸ (CurrentFlagProgram.current security baseline hbaseline mark left hl0 hlHalf).model =
      (CurrentFlagProgram.current security baseline hbaseline mark right hr0 hrHalf).model := by
  have heq : left = right := Rat.cast_injective hcast
  subst left
  rfl

/-- Every rational branch parameter, including the actual `1/2`, uses the
same canonical rational table as the finite sampling program. -/
theorem currentLaw_rat (security : ℕ) (baseline : ℤ)
    (hbaseline : |baseline| ≤ legOffsetBound security) (mark : ZMod (Parameters.modulus security))
    (atom : ℚ) (ha0 : 0 ≤ (atom : ℝ)) (haHalf : (atom : ℝ) ≤ 1 / 2) :
    currentLaw security baseline hbaseline mark (atom : ℝ) ha0 haHalf =
      (CurrentFlagProgram.current security baseline hbaseline mark atom ha0 haHalf).model := by
  unfold currentLaw
  split_ifs with hrational
  · exact rational_model_transport security baseline hbaseline mark (Classical.choose hrational) atom
      _ _ ha0 haHalf (Classical.choose_spec hrational)
  · exact False.elim (hrational ⟨atom, rfl⟩)

theorem protected_first_cast_eq_zero_iff (security : ℕ) (input : ProtectedInput security) :
    (((input.1 : ℤ) : ZMod (Parameters.modulus security)) = 0) ↔ (input.1 : ℤ) = 0 := by
  let zero : GaussianSource.Window (Parameters.sourceCutoff security - 1) :=
    GaussianSource.windowZero (Parameters.sourceCutoff security - 1)
  constructor
  · intro hc
    have hi := window_cast_injective (Parameters.sourceCutoff security - 1)
      (Parameters.modulus security) (leg_input_separation security)
    have hz : input.1 = zero := hi (by simpa only [zero, GaussianSource.windowZero, Int.cast_zero] using hc)
    exact congrArg Subtype.val hz
  · intro hc
    rw [hc, Int.cast_zero]

theorem currentLaw_nonzero_scale (security : ℕ) (baseline : ℤ)
    (hbaseline : |baseline| ≤ legOffsetBound security)
    (mark : ZMod (Parameters.modulus security)) (atom : ℝ)
    (ha0 : 0 ≤ atom) (haHalf : atom ≤ 1 / 2)
    (point : Bool × Chart (ZMod (Parameters.modulus security)))
    (hweight : (currentLaw security baseline hbaseline mark atom ha0 haHalf).joint.weight point ≠ 0) :
    point.2.2.1 ≠ 0 := by
  let model := currentLaw security baseline hbaseline mark atom ha0 haHalf
  intro hz
  have hr : model.regular.weight point.2 = 0 := model.regular_support point.2 (by simp [hz])
  have hm : model.marked.weight point.2 = 0 := model.marked_support point.2 (by simp [hz])
  apply hweight
  rw [model.decomposition point, hr, hm]
  split_ifs <;> simp

end
end CurrentAFT.AffineFlagCalibration
