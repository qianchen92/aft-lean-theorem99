import AFT.RootBlockCoefficients
import AFT.RootBodySourceCertificate
import AFT.ActualBlockReciprocal

/-! # Literal joint coefficients of all active physical root sources -/
namespace AFT.V7Calibration
open GaussianSource RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
local instance rootSourceChoiceFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance rootSourceChoiceSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
local instance rootSourceChoiceSubtypeDecEq {α : Type*} (selected : Finset α) : DecidableEq selected := Classical.decEq _
local instance rootSourceChoiceBlockDecEq (n : ℕ) (index : blockIndex n) : DecidableEq (blockSlots n index) := Classical.decEq _

abbrev RootLocalChoice (n : ℕ) (index : blockIndex n) :=
  { selected : Finset (blockSlots n index) // selected.Nonempty }

abbrev RootSourceChoice (n : ℕ) (selected : Finset (Fin (Parameters.bodies n))) :=
  (index : selected) → RootLocalChoice n ((actualRootIndex n).symm index)

theorem rootLocalChoice_card_le (n : ℕ) (index : blockIndex n) :
    Fintype.card (RootLocalChoice n index) ≤ 8 := by
  apply (Fintype.card_subtype_le (fun selected : Finset (blockSlots n index) => selected.Nonempty)).trans
  rw [Fintype.card_finset]
  exact (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (blockSlots_le_three n index)).trans (by norm_num)

def actualRootSourceChoiceSeed (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (sample : Window (queueCutoff n) × Equiv.Perm (blockIndex n))
    (selected : Finset (Fin (Parameters.bodies n))) (choice : RootSourceChoice n selected) :
    InputSeed (Fin (Parameters.modulus n)) :=
  actualGroupedRootInput (fun index : selected => (choice index).val) C n beta operator
    (fun index => actualRootBlockCoefficient C n beta ((actualRootIndex n).symm index)
      (actualBodyRootSourceOffset n sample index) (choice index).val)
    (actualRootSubsetKernel n selected)

/-- All nonempty local output selections occur once. Each term keeps the
complete joint root coefficient; the sum does not decompose it into tensors. -/
def actualRootSourceChoiceTable (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (sample : Window (queueCutoff n) × Equiv.Perm (blockIndex n))
    (selected : Finset (Fin (Parameters.bodies n))) : Table (InputSeed (Fin (Parameters.modulus n))) :=
  ∑ choice : RootSourceChoice n selected,MvPolynomial.X (actualRootSourceChoiceSeed C n beta operator sample selected choice)

/-- The only reciprocal factors are those of the selected physical blocks,
so a source set of size k incurs at most 2^k in activity. -/
def actualNormalizedRootSourceTable (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (sample : Window (queueCutoff n) × Equiv.Perm (blockIndex n))
    (selected : Finset (Fin (Parameters.bodies n))) (cutoff : ℕ) : Table (InputSeed (Fin (Parameters.modulus n))) :=
  actualRootSourceChoiceTable C n beta operator sample selected*
    ∏ index : selected,actualBlockReciprocal C n beta operator ((actualRootIndex n).symm index)
      (actualBodyRootSourceOffset n sample index) cutoff

/-- The concrete source input inherits all calibrated inverse costs and
one genuine root allocation per selected source. -/
theorem actual_root_source_choice_activity_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n)≤beta n ∧
      beta n≤2*(Parameters.legs n : ℝ)/Parameters.dimension n ∧ Parameters.legs n≤2*pool n)
    (cutoff : ℕ) :
    ∀ᶠ n in atTop,∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n →∀ sample,∀ selected : Finset (Fin (Parameters.bodies n)),
    2≤selected.card → selected.card≤cutoff →∀ choice : RootSourceChoice n selected,
    ∀ bodyPool radius : ℝ,0≤radius →
      inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (pool n) bodyPool radius
        (actualRootSourceChoiceSeed C n (beta n) operator sample selected choice) ≤
      rootFiniteANOVAConstant cutoff*∏ index : selected,
        ((16*pairedOutputCoordinateCost C n (pool n))^(choice index).val.card*
          rootBlockFullCost n ((actualRootIndex n).symm index) (actualBodyRootSourceOffset n sample index)*
          (1/Real.sqrt (Parameters.bodies n : ℝ))) := by
  have hbeta := htypical.mono fun _ h => And.intro h.1 h.2.1
  have hfinite : ∀ᶠ n in atTop,∀ order : Fin (cutoff+1),0<order.val →
      v7RootKernelSq order.val n≤rootANOVAConstant order.val/(Parameters.bodies n : ℝ)^(2*((order.val+1)/2)) := by
    apply Filter.eventually_all.mpr
    intro order
    by_cases ho : 0<order.val
    · exact (v7RootKernelSq_decay order.val ho).mono fun n h _ => h
    · exact Filter.Eventually.of_forall fun n h => False.elim (ho h)
  filter_upwards [actual_grouped_root_input_activity_eventually C hC beta pool htypical,
    actual_root_block_coefficient_eventually C hC beta hbeta,hfinite,eventually_ge_atTop 1]
    with n hi hc hroot hn operator hop sample selected hs hcut choice bodyPool radius hradius
  have hrho : 0<v7Activation C n := activation_positive _ _ _ _ (legFeatureCount_positive C n hC hn)
  have hcost0 : 0≤pairedOutputCoordinateCost C n (pool n) := by unfold pairedOutputCoordinateCost; positivity
  let localBound := fun index : selected => (16 : ℝ)^(choice index).val.card*
    rootBlockFullCost n ((actualRootIndex n).symm index) (actualBodyRootSourceOffset n sample index)
  have hb0 (index : selected) : 0≤localBound index := mul_nonneg (by positivity) (rootBlockFullCost_nonneg _ _ _)
  have hh := hi operator hop selected (fun index : selected => (choice index).val)
    (fun index => actualRootBlockCoefficient C n (beta n) ((actualRootIndex n).symm index)
      (actualBodyRootSourceOffset n sample index) (choice index).val)
    localBound hb0 (fun index => (hc ((actualRootIndex n).symm index) _
      (actualQueueShifts_bound n sample _) (choice index).val).1)
    (actualRootSubsetKernel n selected) bodyPool radius hradius
  change inputWeight _ _ _ _ _ (actualRootSourceChoiceSeed C n (beta n) operator sample selected choice) ≤ _ at hh
  rw [actualRootSubsetKernel_l2Sq] at hh
  have hb := hroot ⟨selected.card,by omega⟩ (show 0<selected.card by omega)
  have halloc := (Real.sqrt_le_sqrt hb).trans
    (root_anova_sqrt_allocation (Parameters.bodies n) (by exact_mod_cast Parameters.bodies_positive n) selected.card)
  have hconstant : Real.sqrt (rootANOVAConstant selected.card)≤rootFiniteANOVAConstant cutoff :=
    Finset.single_le_sum (fun order _ => Real.sqrt_nonneg _) (Finset.mem_range.mpr (by omega))
  apply hh.trans
  apply (mul_le_mul_of_nonneg_left halloc (mul_nonneg (pow_nonneg hcost0 _) (Finset.prod_nonneg fun index _ => hb0 index))).trans
  have heq : pairedOutputCoordinateCost C n (pool n)^Fintype.card (Sigma (fun index : selected => (choice index).val))*
      (∏ index : selected,localBound index)*
      (Real.sqrt (rootANOVAConstant selected.card)*(1/Real.sqrt (Parameters.bodies n : ℝ))^selected.card) =
      Real.sqrt (rootANOVAConstant selected.card)*∏ index : selected,
        ((16*pairedOutputCoordinateCost C n (pool n))^(choice index).val.card*
          rootBlockFullCost n ((actualRootIndex n).symm index) (actualBodyRootSourceOffset n sample index)*
          (1/Real.sqrt (Parameters.bodies n : ℝ))) := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_coe]
    rw [← Finset.prod_pow_eq_pow_sum]
    simp only [Finset.prod_mul_distrib,mul_pow,localBound]
    have hp : (1/Real.sqrt (Parameters.bodies n : ℝ))^selected.card = ∏ _ : selected,1/Real.sqrt (Parameters.bodies n : ℝ) := by simp
    rw [hp]
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_right hconstant (Finset.prod_nonneg fun index _ =>
    mul_nonneg (mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) hcost0) _) (rootBlockFullCost_nonneg _ _ _)) (by positivity))

theorem actual_root_source_choice_canonical_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n)≤beta n ∧
      beta n≤2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n →∀ sample,∀ selected : Finset (Fin (Parameters.bodies n)),
    ∀ choice : RootSourceChoice n selected,
      Hoeffding.Canonical (inputReference (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
        (actualRootSourceChoiceSeed C n (beta n) operator sample selected choice)) Finset.univ
        (actualRootSourceChoiceSeed C n (beta n) operator sample selected choice).kernel := by
  filter_upwards [actual_grouped_root_input_canonical_eventually C hC beta hbeta,
    actual_root_block_coefficient_eventually C hC beta hbeta] with n hi hc operator hop sample selected choice
  exact hi operator hop selected (fun index : selected => (choice index).val) _
    (fun index => (hc ((actualRootIndex n).symm index) _
      (actualQueueShifts_bound n sample _) (choice index).val).2) _

end
end AFT.V7Calibration
