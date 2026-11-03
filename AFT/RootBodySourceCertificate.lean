import AFT.RootSourceSummation

/-! # Summed literal certificates for the body-channel source expansion

This component emits the centered body output at each selected root. The
separate endpoint factors of attached triples are assembled afterwards.
-/
namespace AFT.V7Calibration
open GaussianSource RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance rootBodySourceFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance rootBodySourceSubtypeDecEq {α : Type*} (selected : Finset α) : DecidableEq selected := Classical.decEq _
local instance rootBodySourceSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _

def rootBodySourceBudget (C : ℝ) : ℝ := 2*rootBodyOrdinaryConstant C+2*rootBodyShiftedConstant C

def rootFiniteANOVAConstant (cutoff : ℕ) : ℝ :=
  ∑ order ∈ Finset.range (cutoff+1),Real.sqrt (rootANOVAConstant order)

def actualBodyRootSourceOffset (n : ℕ)
    (sample : Window (queueCutoff n) × Equiv.Perm (blockIndex n))
    (index : Fin (Parameters.bodies n)) : ℤ :=
  actualQueueShifts n sample ((actualRootIndex n).symm index)

def actualBodyRootSourceCost (C : ℝ) (n pool : ℕ)
    (sample : Window (queueCutoff n) × Equiv.Perm (blockIndex n))
    (index : Fin (Parameters.bodies n)) : ℝ :=
  rootBodyAllocatedCost C n pool (actualBodyRootSourceOffset n sample index)

def actualBodyRootSourceSeed (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (sample : Window (queueCutoff n) × Equiv.Perm (blockIndex n))
    (selected : Finset (Fin (Parameters.bodies n))) : InputSeed (Fin (Parameters.modulus n)) :=
  actualRootBodyJointInput C n beta operator (fun slot : selected => actualBodyRootSourceOffset n sample slot)
    (actualRootSubsetKernel n selected)

def actualBodyRootSourceTable (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (sample : Window (queueCutoff n) × Equiv.Perm (blockIndex n))
    (cutoff : ℕ) : Table (InputSeed (Fin (Parameters.modulus n))) :=
  ∑ selected ∈ (Finset.univ : Finset (Finset (Fin (Parameters.bodies n)))).filter
      (fun selected => 2≤selected.card ∧ selected.card≤cutoff),
    MvPolynomial.X (actualBodyRootSourceSeed C n beta operator sample selected)

/-- The half-order root estimate supplies one square-root population
allocation for every source, with additional odd-order decay retained. -/
theorem root_anova_sqrt_allocation (population : ℝ) (hn : 1≤population) (order : ℕ) :
    Real.sqrt (rootANOVAConstant order/population^(2*((order+1)/2))) ≤
      Real.sqrt (rootANOVAConstant order)*(1/Real.sqrt population)^order := by
  have hn0 : 0<population := zero_lt_one.trans_le hn
  have hC := rootANOVAConstant_pos order
  have hden : population^order ≤ population^(2*((order+1)/2)) := pow_le_pow_right₀ hn (by omega)
  apply (Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hC.le (by positivity) hden)).trans_eq
  rw [Real.sqrt_div hC.le]
  have hs : Real.sqrt (population^order)=(Real.sqrt population)^order := by
    clear hC hden
    induction order with
    | zero => simp
    | succ order ih => rw [pow_succ,Real.sqrt_mul (pow_nonneg hn0.le order),ih,pow_succ]
  rw [hs,div_pow,one_pow]
  ring

theorem actualBodyRootSourceOffset_bound (C : ℝ) (n : ℕ)
    (sample : Window (queueCutoff n) × Equiv.Perm (blockIndex n))
    (index : Fin (Parameters.bodies n)) (root : Window (v7RootCutoff n)) :
    |(root : ℤ)+actualBodyRootSourceOffset n sample index| ≤ maxBodyShift C n := by
  have hr := abs_le.mpr (Finset.mem_Icc.mp root.property)
  have hq := actualQueueShifts_bound n sample ((actualRootIndex n).symm index)
  apply (abs_add_le _ _).trans
  unfold actualBodyRootSourceOffset
  apply (add_le_add hr hq).trans
  unfold maxBodyShift
  omega

/-- Every actual selected body-source seed has the source product bound,
uniformly over the common queue and all subsets surviving the cutoff. -/
theorem actual_body_root_source_seed_activity_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n ∧ Parameters.legs n ≤ 2*pool n)
    (cutoff : ℕ) :
    ∀ᶠ n in atTop,
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n →
    ∀ sample : Window (queueCutoff n) × Equiv.Perm (blockIndex n),
    ∀ selected : Finset (Fin (Parameters.bodies n)),2≤selected.card → selected.card≤cutoff →
    ∀ bodyPool radius : ℝ,0≤radius →
      inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (pool n) bodyPool radius
        (actualBodyRootSourceSeed C n (beta n) operator sample selected) ≤
      rootFiniteANOVAConstant cutoff*∏ index ∈ selected,actualBodyRootSourceCost C n (pool n) sample index := by
  have hfinite : ∀ᶠ n in atTop, ∀ order : Fin (cutoff+1),0<order.val →
      v7RootKernelSq order.val n ≤ rootANOVAConstant order.val/(Parameters.bodies n : ℝ)^(2*((order.val+1)/2)) := by
    apply Filter.eventually_all.mpr
    intro order
    by_cases ho : 0<order.val
    · exact (v7RootKernelSq_decay order.val ho).mono fun n h _ => h
    · exact Filter.Eventually.of_forall fun n h => False.elim (ho h)
  filter_upwards [actual_root_body_joint_input_eventually C hC beta pool htypical,hfinite,eventually_ge_atTop 1]
    with n h hroot hn operator hop sample selected hs hcut bodyPool radius hradius
  have hrho : 0<v7Activation C n := activation_positive _ _ _ _ (legFeatureCount_positive C n hC hn)
  let raw := fun index => (4/v7Activation C n)*(Real.sqrt (pool n : ℝ))⁻¹*
    (rootBodyFullCost n (actualBodyRootSourceOffset n sample index)+
      (Real.sqrt (pool n : ℝ))⁻¹*rootBodyRowCost n (actualBodyRootSourceOffset n sample index))
  have hraw (index) : 0≤raw index := mul_nonneg (by positivity)
    (add_nonneg (rootBodyFullCost_nonneg n _) (mul_nonneg (by positivity) (rootBodyRowCost_nonneg n _)))
  have hh := (h operator hop selected (fun slot => actualBodyRootSourceOffset n sample slot)
    (fun slot => actualBodyRootSourceOffset_bound C n sample slot) (actualRootSubsetKernel n selected)
    bodyPool radius hradius).1
  rw [actualRootSubsetKernel_l2Sq] at hh
  have hb := hroot ⟨selected.card,by omega⟩ (show 0<selected.card by omega)
  have halloc := (Real.sqrt_le_sqrt hb).trans
    (root_anova_sqrt_allocation (Parameters.bodies n) (by exact_mod_cast Parameters.bodies_positive n) selected.card)
  have hconstant : Real.sqrt (rootANOVAConstant selected.card) ≤ rootFiniteANOVAConstant cutoff :=
    Finset.single_le_sum (fun order _ => Real.sqrt_nonneg _) (Finset.mem_range.mpr (by omega))
  change _ ≤ (∏ slot : selected,raw slot)*_ at hh
  apply hh.trans
  apply (mul_le_mul_of_nonneg_left halloc (show 0≤∏ slot : selected,raw slot from Finset.prod_nonneg fun slot _ => hraw slot)).trans
  have heq : (∏ slot : selected,raw slot)*
        (Real.sqrt (rootANOVAConstant selected.card)*(1/Real.sqrt (Parameters.bodies n : ℝ))^selected.card) =
      Real.sqrt (rootANOVAConstant selected.card)*∏ index ∈ selected,actualBodyRootSourceCost C n (pool n) sample index := by
    rw [← Finset.prod_coe_sort selected (actualBodyRootSourceCost C n (pool n) sample)]
    have hp : (1/Real.sqrt (Parameters.bodies n : ℝ))^selected.card =
        ∏ _ : selected,1/Real.sqrt (Parameters.bodies n : ℝ) := by simp
    rw [hp]
    simp only [actualBodyRootSourceCost,rootBodyAllocatedCost,independentCoordinateCost,one_div]
    simp only [Finset.prod_mul_distrib]
    dsimp only [raw]
    simp only [Finset.prod_mul_distrib]
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_right hconstant (Finset.prod_nonneg fun index _ =>
    rootBodyAllocatedCost_nonneg C n (pool n) _ hrho.le)

/-- Complete finite source-set summation, with the real source and queue
populations already substituted. -/
theorem actual_body_root_source_table_activity_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n ∧ Parameters.legs n ≤ 2*pool n)
    (cutoff : ℕ) :
    ∀ᶠ n in atTop,
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n →
    ∀ sample : Window (queueCutoff n) × Equiv.Perm (blockIndex n),
    ∀ bodyPool radius : ℝ,0≤radius →
      activity (inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (pool n) bodyPool radius)
        (actualBodyRootSourceTable C n (beta n) operator sample cutoff) ≤
      rootFiniteANOVAConstant cutoff*(rootBodySourceBudget C)^2/(n : ℝ)^24 := by
  have hpool := htypical.mono fun _ h => h.2.2
  have hsmall : ∀ᶠ n : ℕ in atTop,rootBodySourceBudget C/(n : ℝ)^12 ≤ 1 := by
    have ht : Tendsto (fun n : ℕ => rootBodySourceBudget C/(n : ℝ)^12) atTop (𝓝 0) :=
      (tendsto_pow_atTop (by norm_num : (12 : ℕ)≠0) |>.comp tendsto_natCast_atTop_atTop).const_div_atTop _
    exact ht.eventually_le_const (by norm_num)
  filter_upwards [actual_body_root_source_seed_activity_eventually C hC beta pool htypical cutoff,
    actual_root_body_source_sum_eventually C hC pool hpool,hsmall,eventually_ge_atTop 1]
    with n h hsum hsmall hn operator hop sample bodyPool radius hradius
  let cost := actualBodyRootSourceCost C n (pool n) sample
  have hrho : 0<v7Activation C n := activation_positive _ _ _ _ (legFeatureCount_positive C n hC hn)
  have hc (index) : 0≤cost index := rootBodyAllocatedCost_nonneg C n (pool n) _ hrho.le
  have hcSum : (∑ index,cost index) ≤ rootBodySourceBudget C/(n : ℝ)^12 := by
    have he : (∑ index,cost index) = ∑ index : blockIndex n,
        rootBodyAllocatedCost C n (pool n) (actualQueueShifts n sample index) := by
      exact Equiv.sum_comp (actualRootIndex n).symm (fun index => rootBodyAllocatedCost C n (pool n) (actualQueueShifts n sample index))
    rw [he]
    exact hsum sample
  have hfinite0 : 0≤rootFiniteANOVAConstant cutoff := Finset.sum_nonneg fun order _ => Real.sqrt_nonneg _
  unfold actualBodyRootSourceTable
  apply (activity_sum_le _ (fun seed => inputWeight_nonneg _ _ _ _ _ seed hradius) _ _).trans
  simp only [activity_X]
  calc
    _ ≤ ∑ selected ∈ (Finset.univ : Finset (Finset (Fin (Parameters.bodies n)))).filter
        (fun selected => 2≤selected.card ∧ selected.card≤cutoff),rootFiniteANOVAConstant cutoff*∏ index ∈ selected,cost index :=
      Finset.sum_le_sum fun selected hs => h operator hop sample selected
        (Finset.mem_filter.mp hs).2.1 (Finset.mem_filter.mp hs).2.2 bodyPool radius hradius
    _ ≤ ∑ selected : Finset (Fin (Parameters.bodies n)),if 2≤selected.card then
        rootFiniteANOVAConstant cutoff*(∏ index ∈ selected,cost index) else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro selected _
      by_cases hs : 2≤selected.card
      · simp only [hs,true_and,if_true]
        split_ifs
        · rfl
        · exact mul_nonneg hfinite0 (Finset.prod_nonneg fun index _ => hc index)
      · simp only [hs,false_and,if_false,le_refl]
    _ ≤ rootFiniteANOVAConstant cutoff*(∑ index,cost index)^2 :=
      RootTensor.source_sets_weighted_quadratic cost (fun _ => rootFiniteANOVAConstant cutoff)
        _ hc hfinite0 (fun _ _ => le_rfl) (hcSum.trans hsmall)
    _ ≤ rootFiniteANOVAConstant cutoff*(rootBodySourceBudget C/(n : ℝ)^12)^2 :=
      mul_le_mul_of_nonneg_left ((sq_le_sq₀ (Finset.sum_nonneg fun index _ => hc index)
        ((Finset.sum_nonneg fun index _ => hc index).trans hcSum)).mpr hcSum) hfinite0
    _ = _ := by rw [div_pow]; ring

end
end AFT.V7Calibration
