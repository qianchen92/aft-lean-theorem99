import AFT.IndependentReferenceHilbert
import AFT.SingletonSumFibers
import AFT.MixedReplacementActivity
import AFT.ThreeFiberActivity

/-! # Literal replacement of a primary inside an arbitrary joint input -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration Filter MixedKernel
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance independentJointReplacementFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance independentJointReplacementSubtypeDecEq (selected : Finset (Fin 4)) : DecidableEq selected := Classical.decEq _
attribute [local instance] actualModulusNeZero
variable {Rest : Type} [Fintype Rest] [DecidableEq Rest]

def independentReferenceReplacement (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (selected : Finset (Fin 4))
    (kernel : Fin (Parameters.modulus n) → (Rest → Fin (Parameters.modulus n)) → ℝ) :
    (selected ⊕ Rest → Fin (Parameters.modulus n)) → ℝ :=
  fun word => LocalTensors.referenceRestrictedComponent
    (fun _ : Fin 4 => actualPrimaryLaw C n beta) (fun _ : Fin 4 => actualReferenceLaw C n beta)
    (independentPairedNumerator C n beta charts
      (fun color => (actualPrimaryLaw C n beta).weight color*kernel color (word ∘ Sum.inr)))
    selected (word ∘ Sum.inl)

/-- No product decomposition of the old input occurs: every frozen set of
its other coordinates is kept inside one exact finite Hilbert norm. -/
theorem independentReferenceReplacement_activity_uniform_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
    ∀ (Rest : Type) [Fintype Rest] [DecidableEq Rest],
    ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    (∀ mark first second,publicChartRaw C n mark (charts mark) (fun _ => 1) first second =
      conditionalJointOutput C n mark (fun _ => 1) first second) →
    ∀ (other : Rest → FiniteDist (Fin (Parameters.modulus n))) (otherRate : Rest → ℝ),
    (∀ slot,0 ≤ otherRate slot) →
    ∀ kernel : Fin (Parameters.modulus n) → (Rest → Fin (Parameters.modulus n)) → ℝ,
    (∀ rest,∑ color,(actualPrimaryLaw C n (beta n)).weight color*kernel color rest=0) →
    ∀ (selected : Finset (Fin 4)) (rate : ℝ), 1 ≤ selected.card →
      0 ≤ rate → rate ≤ 1 → rate*(n : ℝ)^4 ≤ 1 →
    activity (Sum.elim (fun _ : selected => rate) otherRate)
      (Sum.elim (fun _ : selected => actualPrimaryLaw C n (beta n)) other)
      (independentReferenceReplacement C n (beta n) charts selected kernel) ≤
      32*independentReferenceHilbertConstant*(n : ℝ)^4*rate^(selected.card-1)*
        activity (Sum.elim (fun _ : Unit => rate) otherRate)
          (Sum.elim (fun _ : Unit => actualPrimaryLaw C n (beta n)) other) (singletonJoin kernel) := by
  filter_upwards [independentPaired_reference_hilbert_eventually C hC beta hbeta]
    with n hh Rest _ _ charts hcharts other otherRate hother kernel hcanonical selected rate hselected hrate hrate1 hsmall
  let primary := actualPrimaryLaw C n (beta n)
  let K := independentReferenceHilbertConstant
  let output := independentReferenceReplacement C n (beta n) charts selected kernel
  let coefficient := fun (left : selected → Fin (Parameters.modulus n)) (right : Rest → Fin (Parameters.modulus n)) =>
    LocalTensors.referenceRestrictedComponent (fun _ : Fin 4 => primary)
      (fun _ : Fin 4 => actualReferenceLaw C n (beta n))
      (independentPairedNumerator C n (beta n) charts (fun color => primary.weight color*kernel color right)) selected left
  have hout : output = fun word => coefficient (word ∘ Sum.inl) (word ∘ Sum.inr) := rfl
  let full := fun fixed : Finset Rest => fiberNorm (Sum.elim (fun _ : Unit => primary) other)
    (singletonJoin kernel) ((∅ : Finset Unit).disjSum fixed)
  let single := fun fixed : Finset Rest => fiberNorm (Sum.elim (fun _ : Unit => primary) other)
    (singletonJoin kernel) ((Finset.univ : Finset Unit).disjSum fixed)
  have hF0 (fixed) : 0 ≤ full fixed := fiberNorm_nonneg _ _ _
  have hG0 (fixed) : 0 ≤ single fixed := fiberNorm_nonneg _ _ _
  have hK : 0 ≤ K := by norm_num [K,independentReferenceHilbertConstant]
  have hslice (fixed : Finset Rest) (values : Rest → Fin (Parameters.modulus n)) :=
    hh charts hcharts (Rest → Fin (Parameters.modulus n)) (FiniteDist.independent other)
      (singletonSlice kernel fixed values)
      (fun rest => hcanonical (freeze fixed values rest)) (full fixed) (single fixed) (hF0 fixed) (hG0 fixed)
      (singletonSlice_budgets primary other kernel fixed values).1
      (singletonSlice_budgets primary other kernel fixed values).2 selected
  have hfull (fixed : Finset Rest) : fiberNorm (Sum.elim (fun _ : selected => primary) other) output
      ((∅ : Finset selected).disjSum fixed) ≤ K*(n : ℝ)^4*full fixed := by
    apply fiberNorm_le_square_bound _ _ _ (K*(n : ℝ)^4*full fixed)
      (mul_nonneg (mul_nonneg hK (by positivity)) (hF0 fixed))
    intro values
    rw [hout,fiberSq_sum_apply]
    have hf := (hslice fixed (values ∘ Sum.inr)).1
    simpa only [fiberSq,freeze,Finset.notMem_empty,if_false] using hf
  have hone (slot : selected) (fixed : Finset Rest) :
      fiberNorm (Sum.elim (fun _ : selected => primary) other) output (({slot} : Finset selected).disjSum fixed) ≤
        K*(n : ℝ)^4*(full fixed+single fixed) := by
    apply fiberNorm_le_square_bound _ _ _ (K*(n : ℝ)^4*(full fixed+single fixed))
      (mul_nonneg (mul_nonneg hK (by positivity)) (add_nonneg (hF0 fixed) (hG0 fixed)))
    intro values
    rw [hout,fiberSq_sum_apply]
    exact (hslice fixed (values ∘ Sum.inr)).2.1 slot (values ∘ Sum.inl)
  have hmore (fixedNew : Finset selected) (fixed : Finset Rest) :
      fiberNorm (Sum.elim (fun _ : selected => primary) other) output (fixedNew.disjSum fixed) ≤
        K*(n : ℝ)^4*(n : ℝ)^4*single fixed := by
    apply fiberNorm_le_square_bound _ _ _ (K*(n : ℝ)^4*(n : ℝ)^4*single fixed)
      (mul_nonneg (mul_nonneg (mul_nonneg hK (by positivity)) (by positivity)) (hG0 fixed))
    intro values
    rw [hout,fiberSq_sum_apply]
    unfold fiberSq FiniteDist.l2Sq
    rw [FiniteDist.expectation_comm]
    calc
      _ ≤ (FiniteDist.independent (fun _ : selected => primary)).expectation
        (fun _ => (K*(n : ℝ)^8*single fixed)^2) := by
          apply Finset.sum_le_sum
          intro word _
          exact mul_le_mul_of_nonneg_left
            ((hslice fixed (values ∘ Sum.inr)).2.2 (freeze fixedNew (values ∘ Sum.inl) word)) (FiniteDist.nonneg _ _)
      _ = _ := by rw [FiniteDist.expectation_const]; ring
  have hrates (slot : Unit ⊕ Rest) : 0 ≤ Sum.elim (fun _ : Unit => rate) otherRate slot := by
    cases slot with
    | inl _ => exact hrate
    | inr slot => exact hother slot
  have ha := activity_replacement_le rate otherRate primary other (fun _ : selected => primary)
    (singletonJoin kernel) output (K*(n : ℝ)^4) ((n : ℝ)^4) hrate hrate1 hother (by positivity) hsmall
    (by simpa only [Fintype.card_coe] using hselected) hfull hone (fun fixedNew fixed _ => hmore fixedNew fixed)
  have hc4 : selected.card ≤ 4 := by simpa only [Fintype.card_fin] using Finset.card_le_univ selected
  have htwo : (2:ℝ)^(selected.card+1) ≤ 32 :=
    (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by omega : selected.card+1≤5)).trans_eq (by norm_num)
  simp only [Fintype.card_coe] at ha
  apply ha.trans
  calc
    _ ≤ 32*(K*(n : ℝ)^4)*rate^(selected.card-1)*
      activity (Sum.elim (fun _ : Unit => rate) otherRate) (Sum.elim (fun _ : Unit => primary) other) (singletonJoin kernel) := by
        gcongr
        exact activity_nonneg _ _ _ hrates
    _ = _ := by dsimp [K,primary]; ring

theorem independentReferenceReplacement_activity_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
    ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    (∀ mark first second,publicChartRaw C n mark (charts mark) (fun _ => 1) first second =
      conditionalJointOutput C n mark (fun _ => 1) first second) →
    ∀ (other : Rest → FiniteDist (Fin (Parameters.modulus n))) (otherRate : Rest → ℝ),
    (∀ slot,0 ≤ otherRate slot) →
    ∀ kernel : Fin (Parameters.modulus n) → (Rest → Fin (Parameters.modulus n)) → ℝ,
    (∀ rest,∑ color,(actualPrimaryLaw C n (beta n)).weight color*kernel color rest=0) →
    ∀ (selected : Finset (Fin 4)) (rate : ℝ), 1 ≤ selected.card →
      0 ≤ rate → rate ≤ 1 → rate*(n : ℝ)^4 ≤ 1 →
    activity (Sum.elim (fun _ : selected => rate) otherRate)
      (Sum.elim (fun _ : selected => actualPrimaryLaw C n (beta n)) other)
      (independentReferenceReplacement C n (beta n) charts selected kernel) ≤
      32*independentReferenceHilbertConstant*(n : ℝ)^4*rate^(selected.card-1)*
        activity (Sum.elim (fun _ : Unit => rate) otherRate)
          (Sum.elim (fun _ : Unit => actualPrimaryLaw C n (beta n)) other) (singletonJoin kernel) := by
  filter_upwards [independentReferenceReplacement_activity_uniform_eventually C hC beta hbeta] with n h
  exact h Rest


end
end AFT.V7Calibration
