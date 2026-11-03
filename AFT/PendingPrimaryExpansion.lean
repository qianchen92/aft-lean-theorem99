import AFT.PendingPrimary
import AFT.FiniteSeedExpansion

/-! # The actual independent numerator, replacing only old primary coordinates -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section

structure PendingInput (Color : Type*) where
  seed : InputSeed Color
  pending : Finset (Fin seed.primaryOrder)

def initialPendingInput {Color : Type*} (seed : InputSeed Color) : PendingInput Color :=
  ⟨seed,Finset.univ⟩

end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance pendingExpansionFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- Only the unchanged old coordinates enter the next pending set. -/
def pendingHigherOldEmbedding (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (seed : InputSeed (Fin (Parameters.modulus n))) (point : Fin seed.primaryOrder)
    (selected : Finset (Fin 4)) : {other : Fin seed.primaryOrder // other ≠ point} ↪
      Fin (pendingPrimaryHigherSeed C n beta operator charts seed point selected).primaryOrder :=
  { toFun := fun other => Fintype.equivFin (selected ⊕ {other : Fin seed.primaryOrder // other ≠ point}) (Sum.inr other)
    inj' := fun _ _ h => Sum.inr_injective ((Fintype.equivFin _).injective h) }

def pendingHigherState (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (state : PendingInput (Fin (Parameters.modulus n))) (point : Fin state.seed.primaryOrder)
    (selected : Finset (Fin 4)) : PendingInput (Fin (Parameters.modulus n)) where
  seed := pendingPrimaryHigherSeed C n beta operator charts state.seed point selected
  pending := (state.pending.erase point).attach.map {
    toFun := fun old => pendingHigherOldEmbedding C n beta operator charts state.seed point selected
      ⟨old.val,(Finset.mem_erase.mp old.property).1⟩
    inj' := by
      intro first second he
      apply Subtype.ext
      exact congrArg (fun old : {other : Fin state.seed.primaryOrder // other ≠ point} => old.val)
        ((pendingHigherOldEmbedding C n beta operator charts state.seed point selected).injective he) }

def pendingLinearState {Color : Type*} (state : PendingInput Color) : PendingInput Color :=
  if h : state.pending.Nonempty then ⟨state.seed,state.pending.erase (state.pending.min' h)⟩ else state

def pendingHigherChoices {Color : Type*} (state : PendingInput Color) : Finset (Finset (Fin 4)) :=
  if state.pending.Nonempty then Finset.univ.filter (fun selected => 2 ≤ selected.card) else ∅

def pendingNonlinearState (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (state : PendingInput (Fin (Parameters.modulus n))) (selected : Finset (Fin 4)) :
    PendingInput (Fin (Parameters.modulus n)) :=
  if h : state.pending.Nonempty then
    pendingHigherState C n beta operator charts state (state.pending.min' h) selected else state

@[simp] theorem pendingLinearState_seed {Color : Type*} (state : PendingInput Color) :
    (pendingLinearState state).seed=state.seed := by
  unfold pendingLinearState
  split_ifs <;> rfl

theorem pendingHigherState_card (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (state : PendingInput (Fin (Parameters.modulus n))) (point : Fin state.seed.primaryOrder)
    (hpoint : point ∈ state.pending) (selected : Finset (Fin 4)) :
    (pendingHigherState C n beta operator charts state point selected).pending.card+1=state.pending.card := by
  simp only [pendingHigherState,Finset.card_map,Finset.card_attach]
  exact Finset.card_erase_add_one hpoint

/-- The number of expansion steps is the number of original primary inputs. -/
def independentNumeratorTable (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (seed : InputSeed (Fin (Parameters.modulus n))) : Table (InputSeed (Fin (Parameters.modulus n))) :=
  seedExpansion PendingInput.seed pendingLinearState pendingHigherChoices
    (pendingNonlinearState C n beta operator charts) seed.primaryOrder (initialPendingInput seed)

/-- The same actual inverse preserves canonicality for every new joint seed. -/
theorem pendingPrimaryHigherSeed_canonical_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n →
    ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    ∀ seed : InputSeed (Fin (Parameters.modulus n)),∀ point : Fin seed.primaryOrder,
    Hoeffding.Canonical (inputReference (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) seed)
      Finset.univ seed.kernel → ∀ selected : Finset (Fin 4),
    Hoeffding.Canonical (inputReference (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
      (pendingPrimaryHigherSeed C n (beta n) operator charts seed point selected)) Finset.univ
      (pendingPrimaryHigherSeed C n (beta n) operator charts seed point selected).kernel := by
  filter_upwards [independentJointInverse_correct_uniform_eventually C hC beta hbeta]
    with n hi operator hop charts seed point hseed selected
  apply groupedFiniteSeed_canonical
  exact (hi ({other : Fin seed.primaryOrder // other ≠ point} ⊕ Fin seed.bodyOrder)
    operator hop charts _ (splitPrimaryKernel seed point)
    (splitPrimaryKernel_canonical _ _ seed point hseed) selected).1

/-- A single parameter threshold controls arbitrary joint input orders. The
order dependence is explicit, and the original literal variable cancels. -/
theorem independentNumeratorTable_bounds_eventually (C : ℝ) (hC : 1 ≤ C)
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
    ∀ seed : InputSeed (Fin (Parameters.modulus n)),
    Hoeffding.Canonical (inputReference (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) seed)
      Finset.univ seed.kernel →
    let weight := inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (pool n) bodyPool radius
    let delta := independentJointHigherConstant C/(n : ℝ)^(5/2 : ℝ)
    activity weight (independentNumeratorTable C n (beta n) operator charts seed) ≤
      (1+delta)^seed.primaryOrder*weight seed ∧
    activity weight (independentNumeratorTable C n (beta n) operator charts seed-MvPolynomial.X seed) ≤
      ((1+delta)^seed.primaryOrder-1)*weight seed := by
  have hbeta := htypical.mono fun _ hn => And.intro hn.1 hn.2.1
  filter_upwards [pendingPrimaryHigherTable_activity_eventually C hC beta pool htypical,
    pendingPrimaryHigherSeed_canonical_eventually C hC beta hbeta]
    with n hactivity hcanonical operator hop charts hcharts bodyPool radius hradius seed hseed
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
      seed.primaryOrder (initialPendingInput seed) hseed,
    seedExpansion_error_activity weight hweight PendingInput.seed pendingLinearState pendingHigherChoices
      (pendingNonlinearState C n (beta n) operator charts) good hlinear hhigher delta hdelta hstep
      seed.primaryOrder (initialPendingInput seed) hseed⟩

theorem independentNumeratorTable_canonical_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n →
    ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    ∀ seed : InputSeed (Fin (Parameters.modulus n)),
    Hoeffding.Canonical (inputReference (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) seed)
      Finset.univ seed.kernel →
    InputTableCanonical (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
      (independentNumeratorTable C n (beta n) operator charts seed) := by
  filter_upwards [pendingPrimaryHigherSeed_canonical_eventually C hC beta hbeta]
    with n hi operator hop charts seed hseed
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

end
end AFT.V7Calibration
