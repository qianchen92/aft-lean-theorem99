import AFT.IndependentJointReplacement
import AFT.CoordinateInverseKernel
import AFT.IndependentResponseCost

/-! # The sharp actual inverse replacement inside an arbitrary joint input -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration Filter MixedKernel
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance independentJointInverseFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance independentJointInverseSubtypeDecEq (selected : Finset (Fin 4)) : DecidableEq selected := Classical.decEq _
attribute [local instance] actualModulusNeZero
variable {Rest : Type} [Fintype Rest] [DecidableEq Rest]

def independentJointInverse (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (other : Rest → FiniteDist (Fin (Parameters.modulus n))) (selected : Finset (Fin 4))
    (kernel : Fin (Parameters.modulus n) → (Rest → Fin (Parameters.modulus n)) → ℝ) :
    (selected ⊕ Rest → Fin (Parameters.modulus n)) → ℝ :=
  coordinateInverseKernel ((allCoordinates (Slot := selected)).map Sum.inl)
    (Sum.elim (fun _ : selected => actualPrimaryLaw C n beta) other) (v7Activation C n) operator
    (independentReferenceReplacement C n beta charts selected kernel)

/-- Calibrating only the newly created outputs costs lambda^(-5/2),
uniformly for arbitrary joint old inputs and unequal remaining pool rates. -/
theorem independentJointInverse_activity_uniform_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n ∧
      Parameters.legs n ≤ 2*pool n ∧ pool n ≤ Parameters.legs n) :
    ∀ᶠ n in atTop,
    ∃ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n ∧
    ∀ (Rest : Type) [Fintype Rest] [DecidableEq Rest],
    ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    (∀ mark first second,publicChartRaw C n mark (charts mark) (fun _ => 1) first second =
      conditionalJointOutput C n mark (fun _ => 1) first second) →
    ∀ (other : Rest → FiniteDist (Fin (Parameters.modulus n))) (otherRate : Rest → ℝ),
    (∀ slot,0 ≤ otherRate slot) →
    ∀ kernel : Fin (Parameters.modulus n) → (Rest → Fin (Parameters.modulus n)) → ℝ,
    (∀ rest,∑ color,(actualPrimaryLaw C n (beta n)).weight color*kernel color rest=0) →
    ∀ selected : Finset (Fin 4), 2 ≤ selected.card →
    activity (Sum.elim (fun _ : selected => 1/Real.sqrt (pool n : ℝ)) otherRate)
      (Sum.elim (fun _ : selected => actualPrimaryLaw C n (beta n)) other)
      (independentJointInverse C n (beta n) operator charts other selected kernel) ≤
      (32*independentReferenceHilbertConstant*(8*activationConstant C)^selected.card/(n : ℝ)^(5/2 : ℝ))*
        activity (Sum.elim (fun _ : Unit => 1/Real.sqrt (pool n : ℝ)) otherRate)
          (Sum.elim (fun _ : Unit => actualPrimaryLaw C n (beta n)) other) (singletonJoin kernel) := by
  have hbeta := htypical.mono fun _ h => And.intro h.1 h.2.1
  have htyp := htypical.mono fun _ h => And.intro h.1 (And.intro h.2.1 h.2.2.1)
  filter_upwards [actual_primary_inverse_mixed_uniform_eventually C hC beta pool htyp,
    independentReferenceReplacement_activity_uniform_eventually C hC beta hbeta,
    htypical,eventually_ge_atTop 2] with n hi hr ht hn
  obtain ⟨operator,hop,hinverse⟩ := hi
  refine ⟨operator,hop,?_⟩
  intro Rest _ _ charts hcharts other otherRate hother kernel hcanonical selected hselected
  let rate := 1/Real.sqrt (pool n : ℝ)
  let reference := Sum.elim (fun _ : selected => actualPrimaryLaw C n (beta n)) other
  let rates := Sum.elim (fun _ : selected => rate) otherRate
  let old := activity (Sum.elim (fun _ : Unit => rate) otherRate)
    (Sum.elim (fun _ : Unit => actualPrimaryLaw C n (beta n)) other) (singletonJoin kernel)
  have hrate := independent_primary_rate_small n (pool n) hn ht.2.2.1
  have hrho : 0 < v7Activation C n := activation_positive _ _ _ _
    (legFeatureCount_positive C n hC (by omega))
  have hrates (slot : selected ⊕ Rest) : 0 ≤ rates slot := by
    cases slot with
    | inl _ => exact hrate.1.le
    | inr slot => exact hother slot
  have hold : 0 ≤ old := activity_nonneg _ _ _ (fun slot => by
    cases slot with
    | inl _ => exact hrate.1.le
    | inr slot => exact hother slot)
  have hstep (slot : selected ⊕ Rest) (hslot : slot ∈ (allCoordinates (Slot := selected)).map Sum.inl)
      (value : (selected ⊕ Rest → Fin (Parameters.modulus n)) → ℝ) :
      activity rates reference (partialInputOperator slot operator.symm.toLinearMap (reference slot).weight value) ≤
        4*activity rates reference value := by
    obtain ⟨left,_,rfl⟩ := List.mem_map.mp hslot
    exact hinverse (selected ⊕ Rest) reference rates (Sum.inl left) hrates rfl rfl value
  have hb := coordinateInverseKernel_activity_le ((allCoordinates (Slot := selected)).map Sum.inl)
    reference rates (v7Activation C n) hrho operator hstep
    (independentReferenceReplacement C n (beta n) charts selected kernel)
  simp only [List.length_map,allCoordinates_length,Fintype.card_coe] at hb
  have hl := hr Rest charts hcharts other otherRate hother kernel hcanonical selected rate
    (by omega) hrate.1.le hrate.2.1 hrate.2.2
  have hbound := hb.trans (mul_le_mul_of_nonneg_left hl (pow_nonneg (div_nonneg (by norm_num) hrho.le) _))
  have hx : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hx1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hsqrt : Real.sqrt (pool n : ℝ) ≠ 0 := by
    have hh : 0 < Real.sqrt (pool n : ℝ) := (one_div_pos.mp hrate.1)
    exact hh.ne'
  have hratepow : rate^selected.card=rate^(selected.card-1)*rate := by
    rw [← pow_succ,Nat.sub_add_cancel (by omega : 1 ≤ selected.card)]
  have heq : (4/v7Activation C n)^selected.card*
      (32*independentReferenceHilbertConstant*(n : ℝ)^4*rate^(selected.card-1)*old) =
      (32*independentReferenceHilbertConstant)*
        (Real.sqrt (pool n : ℝ)*independentCoordinateCost C n (pool n)^selected.card*(n : ℝ)^4)*old := by
    unfold independentCoordinateCost
    change _ = (32*independentReferenceHilbertConstant)*
      (Real.sqrt (pool n : ℝ)*((4/v7Activation C n)*rate)^selected.card*(n : ℝ)^4)*old
    rw [mul_pow,hratepow]
    dsimp only [rate]
    field_simp
  rw [heq] at hbound
  have hraw : (n : ℝ)^4 ≤ (n : ℝ)^(4*(selected.card/2)) := by
    apply pow_le_pow_right₀ hx1
    omega
  have hcost : Real.sqrt (pool n : ℝ)*independentCoordinateCost C n (pool n)^selected.card*(n : ℝ)^4 ≤
      independentNonlinearCost C n (pool n) selected.card := by
    apply mul_le_mul_of_nonneg_left hraw
    unfold independentCoordinateCost
    positivity
  have hnum := independentNonlinearCost_le C hC n (pool n) selected.card hn ht.2.2.1 ht.2.2.2 hselected
  apply hbound.trans
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hcost.trans hnum)
    (by norm_num [independentReferenceHilbertConstant] : 0 ≤ 32*independentReferenceHilbertConstant)) hold
  exact hh.trans_eq (by dsimp [old,rate]; ring)

theorem independentJointInverse_activity_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n ∧
      Parameters.legs n ≤ 2*pool n ∧ pool n ≤ Parameters.legs n) :
    ∀ᶠ n in atTop,
    ∃ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n ∧
    ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    (∀ mark first second,publicChartRaw C n mark (charts mark) (fun _ => 1) first second =
      conditionalJointOutput C n mark (fun _ => 1) first second) →
    ∀ (other : Rest → FiniteDist (Fin (Parameters.modulus n))) (otherRate : Rest → ℝ),
    (∀ slot,0 ≤ otherRate slot) →
    ∀ kernel : Fin (Parameters.modulus n) → (Rest → Fin (Parameters.modulus n)) → ℝ,
    (∀ rest,∑ color,(actualPrimaryLaw C n (beta n)).weight color*kernel color rest=0) →
    ∀ selected : Finset (Fin 4), 2 ≤ selected.card →
    activity (Sum.elim (fun _ : selected => 1/Real.sqrt (pool n : ℝ)) otherRate)
      (Sum.elim (fun _ : selected => actualPrimaryLaw C n (beta n)) other)
      (independentJointInverse C n (beta n) operator charts other selected kernel) ≤
      (32*independentReferenceHilbertConstant*(8*activationConstant C)^selected.card/(n : ℝ)^(5/2 : ℝ))*
        activity (Sum.elim (fun _ : Unit => 1/Real.sqrt (pool n : ℝ)) otherRate)
          (Sum.elim (fun _ : Unit => actualPrimaryLaw C n (beta n)) other) (singletonJoin kernel) := by
  filter_upwards [independentJointInverse_activity_uniform_eventually C hC beta pool htypical] with n h
  obtain ⟨operator,hop,h⟩ := h
  exact ⟨operator,hop,h Rest⟩


end
end AFT.V7Calibration
