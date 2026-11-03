import CurrentAFT.RationalLegBackgroundProgram
import CurrentAFT.RationalPopulationApproximation
import CurrentAFT.ActualBackground

/-! # The three actual population products of the original fixed-queue background -/
namespace CurrentAFT.RationalBackgroundPopulationProgram
open AFT GradedControlAlgebra ActualControls BackgroundFamilies BackgroundScalarZero
open RationalActualFamilyApproximation
open scoped BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension
  PublicParameterProgram.modulus ProposalPrimary.primaryLaw bodyReference
  RationalBackgroundProgram.free RationalBackgroundProgram.translation RationalLegBackgroundProgram.current
  RationalFamilyProductProgram.binomial RationalFamilyProductProgram.product

def freeCount (security : ℕ) : ℕ := (PublicParameterProgram.modulus security).count*(security+2)^96-
  (security+2)^128-(PublicParameterProgram.modulus security).count
def freeFactor (security bits order : ℕ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  RationalFamilyProductProgram.binomial order (freeCount security) (RationalBackgroundProgram.free security bits order)
def queueFactor (security bits order : ℕ) (queue : ℤ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  RationalFamilyProductProgram.binomial order (PublicParameterProgram.modulus security).count
    (RationalBackgroundProgram.translation security bits order queue)
def legFactor (security bits order : ℕ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  RationalFamilyProductProgram.binomial order ((security+2)^128) (RationalLegBackgroundProgram.current security bits order)
def current (security bits order : ℕ) (queue : ℤ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  RationalFamilyProductProgram.product order
    (RationalFamilyProductProgram.product order (freeFactor security bits order) (queueFactor security bits order queue))
    (legFactor security bits order)

noncomputable section
open scoped Classical
local instance populationFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

theorem freeCount_value (security : ℕ) : freeCount security=BackgroundPopulationBounds.freeCount security := by
  simp only [freeCount, PublicParameterProgram.modulus_value, BackgroundPopulationBounds.freeCount,
    Parameters.bodySize_eq, Parameters.legCount_eq, Parameters.base]

def freeActual (security order : ℕ) (horder : 2≤order) : ActualFamily security order :=
  (1+freeCertificate security order (by omega))^BackgroundPopulationBounds.freeCount security
def queueActual (security order : ℕ) (horder : 2≤order) (queue : ℤ) : ActualFamily security order :=
  (1+translationCertificate security order (by omega) queue)^Parameters.modulus security
def legActual (security order : ℕ) (horder : 2≤order) : ActualFamily security order :=
  (1+LegBackgroundFamilies.completeLegAtom security order horder)^Parameters.legCount security

def freeBound (security order : ℕ) : ℝ := RationalPopulationApproximation.bound order
  (BackgroundPopulationBounds.freeCount security) (RationalMarkedPairProgram.freeBound security order)
def queueBound (security order : ℕ) : ℝ := RationalPopulationApproximation.bound order
  (Parameters.modulus security) (RationalBackgroundLinearProgram.translationBound security order)
def legAtomBound (security order : ℕ) : ℝ := coordinateFactor security order*43377248
def legBound (security order : ℕ) : ℝ := RationalPopulationApproximation.bound order
  (Parameters.legCount security) (legAtomBound security order)
def freeError (security order : ℕ) : ℝ := RationalPopulationApproximation.error order
  (BackgroundPopulationBounds.freeCount security) (RationalMarkedPairProgram.freeBound security order)
  (RationalBackgroundProgram.freeErrorConstant security)
def queueError (security order : ℕ) : ℝ := RationalPopulationApproximation.error order
  (Parameters.modulus security) (RationalBackgroundLinearProgram.translationBound security order)
  (RationalBackgroundProgram.translationErrorConstant security)
def legError (security order : ℕ) : ℝ := RationalPopulationApproximation.error order
  (Parameters.legCount security) (legAtomBound security order) (RationalLegBackgroundProgram.errorConstant security order)
def freeQueueBound (security order : ℕ) : ℝ := (Fintype.card (TruncatedArity order):ℝ)^2*freeBound security order*queueBound security order
def freeQueueError (security order : ℕ) : ℝ := productError order (freeBound security order) (queueBound security order)
  (freeError security order) (queueError security order)
def errorConstant (security order : ℕ) : ℝ := productError order (freeQueueBound security order) (legBound security order)
  (freeQueueError security order) (legError security order)

theorem leg_atom_bound (security order : ℕ) (horder : 2≤order) :
    ∀ arity colors centers, |data security order (LegBackgroundFamilies.completeLegAtom security order horder) arity colors centers| ≤ legAtomBound security order := by
  have hb : (1:ℝ)≤Parameters.base security := by
    exact_mod_cast (show 1≤Parameters.base security by have := Parameters.base_ge_two security; omega)
  exact point_bound security order _ 43377248 ((LegBackgroundFamilies.completeLegAtom_norm security order horder).trans
    (div_le_self (by norm_num) (one_le_pow₀ hb)))

theorem constants_nonneg (security order : ℕ) :
    0≤freeBound security order ∧ 0≤queueBound security order ∧ 0≤legBound security order ∧
    0≤freeError security order ∧ 0≤queueError security order ∧ 0≤legError security order := by
  have hfA : 0≤RationalMarkedPairProgram.freeBound security order := by
    unfold RationalMarkedPairProgram.freeBound coordinateFactor; positivity
  have hqA : 0≤RationalBackgroundLinearProgram.translationBound security order := by
    unfold RationalBackgroundLinearProgram.translationBound; positivity
  have hlA : 0≤legAtomBound security order := by unfold legAtomBound coordinateFactor; positivity
  rcases RationalBackgroundProgram.density_constants_nonneg security with ⟨hp, _, hb⟩
  have hfE : 0≤RationalBackgroundProgram.freeErrorConstant security := by
    unfold RationalBackgroundProgram.freeErrorConstant; positivity
  exact ⟨RationalPopulationApproximation.bound_nonneg _ _ _ hfA,
    RationalPopulationApproximation.bound_nonneg _ _ _ hqA,
    RationalPopulationApproximation.bound_nonneg _ _ _ hlA,
    RationalPopulationApproximation.error_nonneg _ _ _ _ hfA hfE,
    RationalPopulationApproximation.error_nonneg _ _ _ _ hqA (RationalLegBackgroundProgram.translationError_nonneg security),
    RationalPopulationApproximation.error_nonneg _ _ _ _ hlA (RationalLegBackgroundProgram.errorConstant_nonneg security order)⟩

theorem free_bound (security order : ℕ) (horder : 2≤order) :
    ∀ arity colors centers, |data security order (freeActual security order horder) arity colors centers| ≤ freeBound security order :=
  RationalPopulationApproximation.binomial_bound security order _ _ (freeCertificate_zero security order (by omega))
    _ (by unfold RationalMarkedPairProgram.freeBound coordinateFactor; positivity) (RationalMarkedPairProgram.free_bound security order (by omega))
theorem queue_bound (security order : ℕ) (horder : 2≤order) (queue : ℤ) :
    ∀ arity colors centers, |data security order (queueActual security order horder queue) arity colors centers| ≤ queueBound security order :=
  RationalPopulationApproximation.binomial_bound security order _ _ (translationCertificate_zero security order (by omega) queue)
    _ (by unfold RationalBackgroundLinearProgram.translationBound; positivity) (RationalBackgroundLinearProgram.translation_bound security order (by omega) queue)
theorem leg_bound (security order : ℕ) (horder : 2≤order) :
    ∀ arity colors centers, |data security order (legActual security order horder) arity colors centers| ≤ legBound security order :=
  RationalPopulationApproximation.binomial_bound security order _ _ (completeLegAtom_zero security order horder)
    _ (by unfold legAtomBound coordinateFactor; positivity) (leg_atom_bound security order horder)

theorem factor_errors (security bits order : ℕ) (horder : 2≤order) (queue : ℤ)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ))) :
    (∀ arity colors centers, |interpret security order (freeFactor security bits order) arity colors centers-
      data security order (freeActual security order horder) arity colors centers| ≤ freeError security order*(1/(2:ℝ)^bits)) ∧
    (∀ arity colors centers, |interpret security order (queueFactor security bits order queue) arity colors centers-
      data security order (queueActual security order horder queue) arity colors centers| ≤ queueError security order*(1/(2:ℝ)^bits)) ∧
    (∀ arity colors centers, |interpret security order (legFactor security bits order) arity colors centers-
      data security order (legActual security order horder) arity colors centers| ≤ legError security order*(1/(2:ℝ)^bits)) := by
  rcases RationalBackgroundProgram.density_constants_nonneg security with ⟨hp, _, hb⟩
  have hfE : 0≤RationalBackgroundProgram.freeErrorConstant security := by
    unfold RationalBackgroundProgram.freeErrorConstant; positivity
  refine ⟨?_, ?_, ?_⟩
  · unfold freeFactor
    rw [freeCount_value]
    exact RationalPopulationApproximation.binomial_error security bits order _ _ (freeCertificate_zero security order (by omega)) _ _ _
      (by unfold RationalMarkedPairProgram.freeBound coordinateFactor; positivity) hfE
      (RationalMarkedPairProgram.free_bound security order (by omega))
      (RationalBackgroundProgram.free_error security bits order (by omega) hfirst hprecision hbudget)
  · unfold queueFactor
    rw [PublicParameterProgram.modulus_value]
    exact RationalPopulationApproximation.binomial_error security bits order _ _ (translationCertificate_zero security order (by omega) queue) _ _ _
      (by unfold RationalBackgroundLinearProgram.translationBound; positivity) (RationalLegBackgroundProgram.translationError_nonneg security)
      (RationalBackgroundLinearProgram.translation_bound security order (by omega) queue)
      (RationalBackgroundProgram.translation_error security bits order (by omega) queue hfirst hprecision hbudget)
  · unfold legFactor
    have hl : (security+2)^128=Parameters.legCount security := by simp only [Parameters.legCount_eq, Parameters.base]
    rw [hl]
    have hA : 0≤legAtomBound security order := by
      exact mul_nonneg (pow_nonneg
        (mul_nonneg (mul_nonneg (show (0:ℝ)≤2 by norm_num) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) order)
        (show (0:ℝ)≤43377248 by norm_num)
    have hE := RationalLegBackgroundProgram.errorConstant_nonneg security order
    have hpoint : ∀ arity colors centers,
        |interpret security order (RationalLegBackgroundProgram.current security bits order) arity colors centers-
          data security order (LegBackgroundFamilies.completeLegAtom security order horder) arity colors centers| ≤
        RationalLegBackgroundProgram.errorConstant security order*(1/(2:ℝ)^bits) := by
      intro arity colors centers
      exact RationalLegBackgroundProgram.current_error security bits order horder hfirst hprecision hbudget arity colors centers
    intro arity colors centers
    have h := RationalPopulationApproximation.binomial_error security bits order (Parameters.legCount security)
      (LegBackgroundFamilies.completeLegAtom security order horder) (completeLegAtom_zero security order horder)
      (RationalLegBackgroundProgram.current security bits order) (legAtomBound security order)
      (RationalLegBackgroundProgram.errorConstant security order) hA hE (leg_atom_bound security order horder)
      hpoint arity colors centers
    exact h

theorem current_error (security bits order : ℕ) (horder : 2≤order) (queue : ℤ)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(current security bits order queue arity (fun index => (colors index).val) (fun index => (centers index).val.val):ℝ)-
      (ActualBackground.fixedQueueBackground security order horder queue arity).val colors centers| ≤
      errorConstant security order*(1/(2:ℝ)^bits) := by
  rcases constants_nonneg security order with ⟨hf, hq, hl, heF, heQ, heL⟩
  rcases factor_errors security bits order horder queue hfirst hprecision hbudget with ⟨hfree, hqueue, hleg⟩
  have hfirstError := product_error security bits order (freeActual security order horder) (queueActual security order horder queue)
    (freeFactor security bits order) (queueFactor security bits order queue)
    (freeBound security order) (queueBound security order) (freeError security order) (queueError security order)
    hf hq heF heQ (free_bound security order horder) (queue_bound security order horder queue) hfree hqueue
  have hfirstBound : ∀ arity colors centers,
      |data security order (freeActual security order horder*queueActual security order horder queue) arity colors centers| ≤ freeQueueBound security order := by
    intro arity colors centers
    change |data security order (familyProduct (ProposalPrimary.primaryLaw security) (bodyReference security) order
      (freeActual security order horder) (queueActual security order horder queue)) arity colors centers| ≤ _
    rw [← data_product]
    exact (RationalFamilyProductProgram.product_bound order _ _ _ _ hf hq
      (free_bound security order horder) (queue_bound security order horder queue) arity colors centers).trans_eq
        (by unfold freeQueueBound; ring)
  have hbFQ : 0≤freeQueueBound security order := by unfold freeQueueBound; positivity
  have heFQ : 0≤freeQueueError security order := productError_nonneg _ _ _ _ _ hf hq heF heQ
  exact product_error security bits order (freeActual security order horder*queueActual security order horder queue)
    (legActual security order horder)
    (RationalFamilyProductProgram.product order (freeFactor security bits order) (queueFactor security bits order queue))
    (legFactor security bits order) (freeQueueBound security order) (legBound security order)
    (freeQueueError security order) (legError security order) hbFQ hl heFQ heL hfirstBound
    (leg_bound security order horder) hfirstError hleg arity colors centers

theorem errorConstant_nonneg (security order : ℕ) : 0≤errorConstant security order := by
  rcases constants_nonneg security order with ⟨hf, hq, hl, heF, heQ, heL⟩
  exact productError_nonneg _ _ _ _ _ (by unfold freeQueueBound; positivity) hl
    (productError_nonneg _ _ _ _ _ hf hq heF heQ) heL

end
end CurrentAFT.RationalBackgroundPopulationProgram
