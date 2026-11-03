import AFT.PendingPhysicalReindex

/-! # Every tagged original-coordinate expansion has its exact physical image -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration RepresentedPolynomial MixedKernel Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance pendingPhysicalIdentityFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance pendingPhysicalIdentityUnitDecEq : DecidableEq Unit := Classical.decEq _
local instance pendingPhysicalIdentitySelectedDecEq (s : Finset (Fin 4)) : DecidableEq s := Classical.decEq _
attribute [local instance] actualModulusNeZero

theorem pendingPhysical_step_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n →
    ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    (∀ mark attached first second,publicChartRaw C n mark (charts mark) attached first second=
      conditionalJointOutput C n mark attached first second) →
    ∀ state : PendingInput (Fin (Parameters.modulus n)),∀ point : Fin state.seed.primaryOrder,
    point∈state.pending →
    Hoeffding.Canonical (inputReference (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) state.seed)
      Finset.univ state.seed.kernel →
    pendingPhysicalPolynomial C n (beta n) charts ⟨state.seed,state.pending.erase point⟩+
      (∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).filter (fun selected => 2≤selected.card),
        pendingPhysicalPolynomial C n (beta n) charts (pendingHigherState C n (beta n) operator charts state point selected))=
      pendingPhysicalPolynomial C n (beta n) charts state := by
  filter_upwards [independentPolynomialReplacement_eventually C hC beta hbeta]
    with n hi operator hop charts hcharts state point hp hc
  rw [pendingErasedPolynomial_split,pendingPhysicalPolynomial_split C n (beta n) charts state point hp,
    independentPairedForm_sum]
  simp_rw [pendingHigherPolynomial_reindex]
  exact hi ({other : Fin state.seed.primaryOrder // other≠point} ⊕ Fin state.seed.bodyOrder)
    operator hop charts hcharts _ _ (splitPrimaryKernel state.seed point)
    (splitPrimaryKernel_primary_mean _ _ state.seed point hc)

/-- New outputs are never fed back into the independent channel. After the
number of original primary coordinates has been exhausted, the polynomial is
exactly the physical joint channel, still retaining all original body inputs. -/
theorem independentNumeratorTable_image_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n →
    ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    (∀ mark attached first second,publicChartRaw C n mark (charts mark) attached first second=
      conditionalJointOutput C n mark attached first second) →
    ∀ seed : InputSeed (Fin (Parameters.modulus n)),
    Hoeffding.Canonical (inputReference (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) seed)
      Finset.univ seed.kernel →
    actualLeadingOutput C n (beta n) (independentNumeratorTable C n (beta n) operator charts seed)=
      pendingPhysicalPolynomial C n (beta n) charts (initialPendingInput seed) := by
  filter_upwards [pendingPhysical_step_eventually C hC beta hbeta,
    pendingPrimaryHigherSeed_canonical_eventually C hC beta hbeta]
    with n hstep hcanonical operator hop charts hcharts seed hseed
  have hrec (steps : ℕ) : ∀ state : PendingInput (Fin (Parameters.modulus n)),state.pending.card≤steps →
      Hoeffding.Canonical (inputReference (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) state.seed)
        Finset.univ state.seed.kernel →
      actualLeadingOutput C n (beta n) (seedExpansion PendingInput.seed pendingLinearState pendingHigherChoices
        (pendingNonlinearState C n (beta n) operator charts) steps state)=
          pendingPhysicalPolynomial C n (beta n) charts state := by
    induction steps with
    | zero =>
      intro state hcard _
      have he : state.pending=∅ := Finset.card_eq_zero.mp (by omega)
      exact (pendingPhysicalPolynomial_empty C n (beta n) charts state he).symm
    | succ steps ih =>
      intro state hcard hc
      by_cases hn : state.pending.Nonempty
      · have hp : state.pending.min' hn∈state.pending := Finset.min'_mem _ _
        rw [seedExpansion,map_add,map_sum]
        have hlinear : Hoeffding.Canonical
            (inputReference (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (pendingLinearState state).seed)
            Finset.univ (pendingLinearState state).seed.kernel := by rw [pendingLinearState_seed]; exact hc
        rw [ih (pendingLinearState state) (by have hh := pendingLinearState_card state hn; omega) hlinear]
        have hnon (selected) : pendingNonlinearState C n (beta n) operator charts state selected=
            pendingHigherState C n (beta n) operator charts state (state.pending.min' hn) selected := by
          unfold pendingNonlinearState
          exact dif_pos hn
        have hsum : (∑ selected ∈ pendingHigherChoices state,
            actualLeadingOutput C n (beta n) (seedExpansion PendingInput.seed pendingLinearState pendingHigherChoices
              (pendingNonlinearState C n (beta n) operator charts) steps
              (pendingNonlinearState C n (beta n) operator charts state selected)))=
            ∑ selected ∈ pendingHigherChoices state,pendingPhysicalPolynomial C n (beta n) charts
              (pendingNonlinearState C n (beta n) operator charts state selected) := by
          apply Finset.sum_congr rfl
          intro selected _
          apply ih
          · rw [hnon]
            have hh := pendingHigherState_card C n (beta n) operator charts state (state.pending.min' hn) hp selected
            omega
          · rw [hnon]
            exact hcanonical operator hop charts state.seed (state.pending.min' hn) hc selected
        rw [hsum]
        simpa only [pendingLinearState,dif_pos hn,pendingHigherChoices,if_pos hn,pendingNonlinearState] using
          hstep operator hop charts hcharts state (state.pending.min' hn) hp hc
      · have he : state.pending=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
        simp only [seedExpansion,pendingLinearState,dif_neg hn,pendingHigherChoices,if_neg hn,
          Finset.sum_empty,add_zero]
        exact ih state (by simp [he]) hc
  exact hrec seed.primaryOrder (initialPendingInput seed) (by simp [initialPendingInput]) hseed

end
end AFT.V7Calibration
