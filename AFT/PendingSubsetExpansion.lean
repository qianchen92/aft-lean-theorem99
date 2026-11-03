import AFT.PendingPhysicalIdentity

/-! # Independent replacement of any specified subset of old primary inputs -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration RepresentedPolynomial MixedKernel Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance pendingSubsetFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance pendingSubsetUnitDecEq : DecidableEq Unit := Classical.decEq _
local instance pendingSubsetSelectedDecEq (s : Finset (Fin 4)) : DecidableEq s := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- Only the named old primary coordinates pass through the independent
channel. All other primary coordinates retain their leading output channel. -/
def pendingNumeratorTable (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (state : PendingInput (Fin (Parameters.modulus n))) : Table (InputSeed (Fin (Parameters.modulus n))) :=
  seedExpansion PendingInput.seed pendingLinearState pendingHigherChoices
    (pendingNonlinearState C n beta operator charts) state.pending.card state

theorem pendingNumeratorTable_bounds_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n ∧
      Parameters.legs n ≤ 2*pool n ∧ pool n ≤ Parameters.legs n) :
    ∀ᶠ n in atTop,
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n →
    ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    (∀ mark first second,publicChartRaw C n mark (charts mark) (fun _ => 1) first second=
      conditionalJointOutput C n mark (fun _ => 1) first second) →
    ∀ bodyPool radius : ℝ,0 ≤ radius →
    ∀ state : PendingInput (Fin (Parameters.modulus n)),
    Hoeffding.Canonical (inputReference (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) state.seed)
      Finset.univ state.seed.kernel →
    let weight := inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (pool n) bodyPool radius
    let delta := independentJointHigherConstant C/(n : ℝ)^(5/2 : ℝ)
    activity weight (pendingNumeratorTable C n (beta n) operator charts state) ≤
      (1+delta)^state.pending.card*weight state.seed ∧
    activity weight (pendingNumeratorTable C n (beta n) operator charts state-MvPolynomial.X state.seed) ≤
      ((1+delta)^state.pending.card-1)*weight state.seed := by
  have hbeta := htypical.mono fun _ hn => And.intro hn.1 hn.2.1
  filter_upwards [pendingPrimaryHigherTable_activity_eventually C hC beta pool htypical,
    pendingPrimaryHigherSeed_canonical_eventually C hC beta hbeta]
    with n hactivity hcanonical operator hop charts hcharts bodyPool radius hradius state hseed
  let weight := inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (pool n) bodyPool radius
  let delta := independentJointHigherConstant C/(n : ℝ)^(5/2 : ℝ)
  let good := fun state : PendingInput (Fin (Parameters.modulus n)) =>
    Hoeffding.Canonical (inputReference (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) state.seed)
      Finset.univ state.seed.kernel
  have hweight (seed) : 0 ≤ weight seed := inputWeight_nonneg _ _ _ _ _ seed hradius
  have hdelta : 0 ≤ delta := by
    have ha := activationConstant_pos C hC
    dsimp [delta,independentJointHigherConstant,independentReferenceHilbertConstant]
    positivity
  have hlinear (state) (hs : good state) : good (pendingLinearState state) ∧
      (pendingLinearState state).seed=state.seed := by
    refine ⟨?_,pendingLinearState_seed state⟩
    dsimp only [good]
    rw [pendingLinearState_seed]
    exact hs
  have hhigher (state) (hs : good state) (selected) (_ : selected ∈ pendingHigherChoices state) :
      good (pendingNonlinearState C n (beta n) operator charts state selected) := by
    unfold pendingNonlinearState
    split_ifs with hn
    · exact hcanonical operator hop charts state.seed (state.pending.min' hn) hs selected
    · exact hs
  have hstep (state) (hs : good state) :
      (∑ selected ∈ pendingHigherChoices state,
        weight (pendingNonlinearState C n (beta n) operator charts state selected).seed) ≤ delta*weight state.seed := by
    by_cases hn : state.pending.Nonempty
    · have hh := hactivity operator hop charts hcharts state.seed (state.pending.min' hn) hs bodyPool radius hradius
      unfold pendingPrimaryHigherTable independentJointHigherTable at hh
      rw [activity_sum_X] at hh
      simpa only [pendingHigherChoices,if_pos hn,pendingNonlinearState,dif_pos hn,pendingHigherState]
        using hh
    · simp only [pendingHigherChoices,if_neg hn,Finset.sum_empty]
      exact mul_nonneg hdelta (hweight state.seed)
  exact ⟨seedExpansion_activity weight hweight PendingInput.seed pendingLinearState pendingHigherChoices
      (pendingNonlinearState C n (beta n) operator charts) good hlinear hhigher delta hdelta hstep
      state.pending.card state hseed,
    seedExpansion_error_activity weight hweight PendingInput.seed pendingLinearState pendingHigherChoices
      (pendingNonlinearState C n (beta n) operator charts) good hlinear hhigher delta hdelta hstep
      state.pending.card state hseed⟩

theorem pendingNumeratorTable_canonical_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n →
    ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    ∀ state : PendingInput (Fin (Parameters.modulus n)),
    Hoeffding.Canonical (inputReference (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) state.seed)
      Finset.univ state.seed.kernel →
    InputTableCanonical (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
      (pendingNumeratorTable C n (beta n) operator charts state) := by
  filter_upwards [pendingPrimaryHigherSeed_canonical_eventually C hC beta hbeta]
    with n hi operator hop charts state hseed
  let good := fun state : PendingInput (Fin (Parameters.modulus n)) =>
    Hoeffding.Canonical (inputReference (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) state.seed)
      Finset.univ state.seed.kernel
  apply seedExpansion_canonical (good := good)
  · intro state hs; exact hs
  · intro state hs
    dsimp only [good]
    rw [pendingLinearState_seed]
    exact hs
  · intro state hs selected _
    unfold pendingNonlinearState
    split_ifs with hn
    · exact hi operator hop charts state.seed (state.pending.min' hn) hs selected
    · exact hs
  · exact hseed

theorem pendingNumeratorTable_image_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n →
    ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    (∀ mark attached first second,publicChartRaw C n mark (charts mark) attached first second=
      conditionalJointOutput C n mark attached first second) →
    ∀ state : PendingInput (Fin (Parameters.modulus n)),
    Hoeffding.Canonical (inputReference (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) state.seed)
      Finset.univ state.seed.kernel →
    actualLeadingOutput C n (beta n) (pendingNumeratorTable C n (beta n) operator charts state)=
      pendingPhysicalPolynomial C n (beta n) charts state := by
  filter_upwards [pendingPhysical_step_eventually C hC beta hbeta,
    pendingPrimaryHigherSeed_canonical_eventually C hC beta hbeta]
    with n hstep hcanonical operator hop charts hcharts state hseed
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
  exact hrec state.pending.card state le_rfl hseed

end
end AFT.V7Calibration
