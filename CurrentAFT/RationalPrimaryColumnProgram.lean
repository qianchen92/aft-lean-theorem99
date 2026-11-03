import CurrentAFT.RationalSelectedRootProgram
import CurrentAFT.RootReferenceColumns

/-! # The actual centered primary point column

The program centers a point score using its computed primary table.
The proof compares with the original exact `C_p delta` column, including
the error of that centering. Root masses have already been factored out.
-/
namespace CurrentAFT.RationalPrimaryColumnProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls CoefficientHilbert
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def centerDelta (security bits source color : ℕ) : ℚ :=
  (if color = source then 1 else 0) - RationalProposalProgram.primary security bits source

def current (security bits : ℕ) (compensatorRoot attachmentRoot : ℤ) (primaryColor : ℕ)
    (selected : Finset (Fin 4)) (output : Fin selected.card → ℕ) : ℚ :=
  RationalSelectedRootProgram.current security bits compensatorRoot attachmentRoot
    (centerDelta security bits primaryColor) selected output

noncomputable section
open scoped Classical
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSubtypeDecidableEq {Index : Type*} (selected : Finset Index) : DecidableEq selected := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw

theorem centerDelta_cast (security bits : ℕ) (source color : Palette security) :
    (centerDelta security bits source.val color.val : ℝ) =
      (if color = source then (1 : ℝ) else 0) -
        (RationalProposalProgram.approximatePrimaryLaw security bits).weight source := by
  unfold centerDelta
  by_cases hequal : color = source
  · subst color
    simp only [if_true, Rat.cast_sub, Rat.cast_one]
    rfl
  · have hne : color.val ≠ source.val := fun h => hequal (Fin.ext h)
    simp only [if_neg hne, if_neg hequal, Rat.cast_sub, Rat.cast_zero]
    rfl

theorem actual_centerDelta (security : ℕ) (source color : Palette security) :
    centerLinear (primaryLaw security) (Pi.single source 1) color =
      (if color = source then (1 : ℝ) else 0) - (primaryLaw security).weight source := by
  change (Pi.single (M := fun _ : Palette security => ℝ) source 1) color -
    (primaryLaw security).expectation (Pi.single source 1) = _
  simp [Pi.single_apply, FiniteDist.expectation]

theorem centerDelta_bound (security bits : ℕ) (source color : Palette security) :
    |(centerDelta security bits source.val color.val : ℝ)| ≤ 1 := by
  rw [centerDelta_cast]
  have hlo := (RationalProposalProgram.approximatePrimaryLaw security bits).nonneg source
  have hhi := (RationalProposalProgram.approximatePrimaryLaw security bits).atom_le_one source
  split_ifs <;> exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem actual_centerDelta_bound (security : ℕ) (source color : Palette security) :
    |centerLinear (primaryLaw security) (Pi.single source 1) color| ≤ 1 := by
  rw [actual_centerDelta]
  have hlo := (primaryLaw security).nonneg source
  have hhi := (primaryLaw security).atom_le_one source
  split_ifs <;> exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem centerDelta_error (security bits : ℕ) (source color : Palette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(centerDelta security bits source.val color.val : ℝ) -
      centerLinear (primaryLaw security) (Pi.single source 1) color| ≤
        RationalRootMassProgram.primaryErrorConstant security * (1 / (2 : ℝ)^bits) := by
  rw [centerDelta_cast, actual_centerDelta]
  have h : |(RationalProposalProgram.approximatePrimaryLaw security bits).weight source -
      (primaryLaw security).weight source| ≤
      RationalRootMassProgram.primaryErrorConstant security * (1 / (2 : ℝ)^bits) := by
    simpa only [RationalProposalProgram.approximatePrimaryLaw, primaryLaw, RationalRootMassProgram.primaryErrorConstant] using
      RationalProposalProgram.primary_error security bits source hprecision hbudget
  have hequal : ((if color = source then (1 : ℝ) else 0) -
      (RationalProposalProgram.approximatePrimaryLaw security bits).weight source) -
      ((if color = source then (1 : ℝ) else 0) - (primaryLaw security).weight source) =
        (primaryLaw security).weight source - (RationalProposalProgram.approximatePrimaryLaw security bits).weight source := by ring
  rw [hequal, abs_sub_comm]
  exact h

theorem primaryMassAt_difference (security : ℕ) (roots : RootTaggedSelected.RootPair security)
    (first second : Palette security → ℝ) (error : ℝ) (he : 0 ≤ error)
    (hdiff : ∀ color, |first color - second color| ≤ error) (word : Fin 4 → Palette security) :
    |RootMassColumns.primaryMassAt security roots first word - RootMassColumns.primaryMassAt security roots second word| ≤
      (2 * (Parameters.modulus security : ℝ)^2) * error := by
  change |(RootMassColumns.primaryMassAt security roots first - RootMassColumns.primaryMassAt security roots second) word| ≤ _
  rw [← map_sub]
  exact RationalRootMassProgram.primaryMassAt_bound security roots (first - second) error he hdiff word

def massErrorConstant (security : ℕ) : ℝ :=
  RationalRootMassProgram.primaryMassErrorConstant security +
    (2 * (Parameters.modulus security : ℝ)^2) * RationalRootMassProgram.primaryErrorConstant security

theorem mass_error (security bits : ℕ) (roots : RootTaggedSelected.RootPair security) (source : Palette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) (word : Fin 4 → Palette security) :
    |(RationalRootMassProgram.primaryMass security bits roots.1.val roots.2.val
        (centerDelta security bits source.val) (fun index => (word index).val) : ℝ) -
      RootMassColumns.primaryMassAt security roots (centerLinear (primaryLaw security) (Pi.single source 1)) word| ≤
      massErrorConstant security * (1 / (2 : ℝ)^bits) := by
  let approximate := fun color : Palette security => (centerDelta security bits source.val color.val : ℝ)
  have hprogram := RationalRootMassProgram.primaryMass_error security bits roots (centerDelta security bits source.val) 1
    (by norm_num) (centerDelta_bound security bits source) hprecision hbudget word
  have hcentering := primaryMassAt_difference security roots approximate
    (centerLinear (primaryLaw security) (Pi.single source 1))
    (RationalRootMassProgram.primaryErrorConstant security * (1 / (2 : ℝ)^bits))
    (by unfold RationalRootMassProgram.primaryErrorConstant; positivity)
    (fun color => centerDelta_error security bits source color hprecision hbudget) word
  calc
    _ ≤ |(RationalRootMassProgram.primaryMass security bits roots.1.val roots.2.val
          (centerDelta security bits source.val) (fun index => (word index).val) : ℝ) -
        RootMassColumns.primaryMassAt security roots approximate word| +
      |RootMassColumns.primaryMassAt security roots approximate word -
        RootMassColumns.primaryMassAt security roots (centerLinear (primaryLaw security) (Pi.single source 1)) word| :=
      abs_sub_le _ _ _
    _ ≤ _ := add_le_add hprogram hcentering
    _ = _ := by unfold massErrorConstant; ring

def errorConstant (security degree : ℕ) : ℝ :=
  RationalCoefficientExtraction.normalizedError security degree (2 * (Parameters.modulus security : ℝ)^2)
    (massErrorConstant security)

theorem current_error (security bits : ℕ) (roots : RootTaggedSelected.RootPair security) (source : Palette security)
    (selected : Finset (Fin 4))
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (output : Fin selected.card → Palette security) (body : Fin 0 → SafePalette security) :
    |(current security bits roots.1.val roots.2.val source.val selected (fun index => (output index).val) : ℝ) -
      (LocalCoefficientFamily.selectedKernel security selected.card
        (RootMassColumns.primaryMassAt security roots (centerLinear (primaryLaw security) (Pi.single source 1)))
        selected (by simp)).val output body| ≤
      errorConstant security selected.card * (1 / (2 : ℝ)^bits) := by
  have hmassError : 0 ≤ massErrorConstant security := by
    unfold massErrorConstant RationalRootMassProgram.primaryMassErrorConstant RationalRootMassProgram.fixedErrorConstant
      RationalRootMassProgram.weightedErrorConstant RationalRootMassProgram.primaryErrorConstant
    positivity
  have h := RationalCoefficientExtraction.selectedKernel_error security bits
    (RationalRootMassProgram.primaryMass security bits roots.1.val roots.2.val (centerDelta security bits source.val))
    (RootMassColumns.primaryMassAt security roots (centerLinear (primaryLaw security) (Pi.single source 1))) selected
    (2 * (Parameters.modulus security : ℝ)^2) (massErrorConstant security) (by positivity) hmassError
    (fun word => by
      simpa only [mul_one] using RationalRootMassProgram.primaryMassAt_bound security roots
        (centerLinear (primaryLaw security) (Pi.single source 1)) 1 (by norm_num) (actual_centerDelta_bound security source) word)
    (fun word => mass_error security bits roots source hprecision hbudget word)
    hfirst hprecision hbudget output body
  exact h

end
end CurrentAFT.RationalPrimaryColumnProgram
