import AFT.PhysicalRootFactorization

/-! # Exact source cutoff for the genuine full background response -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 250000
variable {Index Source Color : Type*} [Fintype Index] [Fintype Source] [DecidableEq Index]

theorem truncate_finset_sum {Tag : Type*} (order : Color → ℕ) (cutoff : ℕ)
    (indices : Finset Tag) (tables : Tag → Table Color) :
    truncate order cutoff (∑ index ∈ indices,tables index)=∑ index ∈ indices,truncate order cutoff (tables index) := by
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert index indices hn ih => simp only [Finset.sum_insert hn,truncate_add,ih]

/-- A canonical source coefficient annihilates every polynomial that
omits one of its source coordinates, coefficient by coefficient. -/
theorem canonical_polynomial_support_zero (reference : Index → FiniteDist Source)
    (selected used : Finset Index) (kernel : (Index → Source) → ℝ)
    (hcanonical : Hoeffding.Canonical reference selected kernel)
    (polynomial : (Index → Source) → Table Color)
    (hdepends : ∀ first second, (∀ index ∈ used, first index=second index) →
      polynomial first=polynomial second) (hmissing : ¬ selected ⊆ used) :
    (∑ word, ((FiniteDist.independent reference).weight word*kernel word) • polynomial word) = 0 := by
  have hd : (inferInstance : DecidableEq Index) = Classical.decEq Index := Subsingleton.elim _ _
  cases hd
  apply MvPolynomial.ext
  intro powers
  simp only [MvPolynomial.coeff_sum,MvPolynomial.coeff_smul,MvPolynomial.coeff_zero,smul_eq_mul]
  have hh := RootSlice.canonical_support_cutoff reference selected used kernel
    (fun word => MvPolynomial.coeff powers (polynomial word)) hcanonical
    (fun first second heq => congrArg (MvPolynomial.coeff powers) (hdepends first second heq)) hmissing
  simpa only [FiniteDist.expectation,mul_assoc] using hh

/-- The full local product expands over the actual source subsets. Every
retained factor is its literal unit-subtracted polynomial. -/
theorem canonical_polynomial_product_expansion (reference : Index → FiniteDist Source)
    (selected : Finset Index) (kernel : (Index → Source) → ℝ)
    (hcanonical : Hoeffding.Canonical reference selected kernel)
    (polynomial : Index → Source → Table Color) :
    (∑ word, ((FiniteDist.independent reference).weight word*kernel word) •
      ∏ index, polynomial index (word index)) =
      ∑ used : Finset Index, if selected ⊆ used then
        ∑ word, ((FiniteDist.independent reference).weight word*kernel word) •
          ∏ index ∈ used, (polynomial index (word index)-1) else 0 := by
  have he (word : Index → Source) : (∏ index,polynomial index (word index)) =
      ∑ used : Finset Index, ∏ index ∈ used,(polynomial index (word index)-1) := by
    have hh := Fintype.prod_add (fun index => polynomial index (word index)-1) (fun _ => (1 : Table Color))
    simpa only [sub_add_cancel,Finset.prod_const_one,mul_one] using hh
  simp_rw [he,Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro used _
  by_cases hsub : selected ⊆ used
  · rw [if_pos hsub]
  rw [if_neg hsub]
  apply canonical_polynomial_support_zero reference selected used kernel hcanonical _ _ hsub
  intro first second heq
  apply Finset.prod_congr rfl
  intro index hi
  rw [heq index hi]

/-- At least one positive-degree factor is required for every canonical
source coordinate. This is an exact statement for the full polynomial. -/
theorem canonical_polynomial_product_hasOrder (reference : Index → FiniteDist Source)
    (selected : Finset Index) (kernel : (Index → Source) → ℝ)
    (hcanonical : Hoeffding.Canonical reference selected kernel)
    (polynomial : Index → Source → Table Color)
    (hconstant : ∀ index source, MvPolynomial.constantCoeff (polynomial index source)=1) :
    HasOrder (fun _ : Color => 1) selected.card
      (∑ word, ((FiniteDist.independent reference).weight word*kernel word) •
        ∏ index, polynomial index (word index)) := by
  rw [canonical_polynomial_product_expansion reference selected kernel hcanonical polynomial]
  apply hasOrder_sum
  intro used _
  split_ifs with hsub
  · apply hasOrder_sum
    intro word _
    have hp : HasOrder (fun _ : Color => 1) used.card
        (∏ index ∈ used,(polynomial index (word index)-1)) := by
      have hh := hasOrder_prod (fun _ : Color => 1) (fun _ : Index => 1)
        (fun index => polynomial index (word index)-1) used fun index _ =>
        hasOrder_one_of_constant_zero _ (by simp only [map_sub,hconstant,map_one,sub_self])
      simpa only [Finset.sum_const,smul_eq_mul,mul_one] using hh
    have hs := hasOrder_mono (fun _ : Color => 1) selected.card used.card _ hp (Finset.card_le_card hsub)
    intro powers hpower
    simp only [MvPolynomial.coeff_smul,hs powers hpower,smul_zero]
  · intro powers _
    exact MvPolynomial.coeff_zero _

end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open GaussianSource RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 250000
local instance rootPolynomialCutoffFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance rootPolynomialCutoffSigmaDecEq {ι : Type*} {fiber : ι → Type*} : DecidableEq (Sigma fiber) := Classical.decEq _
local instance rootPolynomialCutoffSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _

theorem actualRootResponseCoefficient_canonical (n : ℕ) (selected : Finset (Fin (Parameters.bodies n))) :
    Hoeffding.Canonical (fun _ : Fin (Parameters.bodies n) => bodyRootReference n) selected
      (actualRootResponseCoefficient n selected) :=
  Hoeffding.densityComponent_canonical _ (fun _ => bodyRootReference_positive n) _ selected

theorem actualBlockConditionalPolynomial_constant (C : ℝ) (n : ℕ) (beta : ℝ)
    (index : blockIndex n) (root queue : ℤ) :
    MvPolynomial.constantCoeff (actualBlockConditionalPolynomial C n beta index root queue)=1 := by
  change MvPolynomial.constantCoeff (centeredGeneratingLinear (actualReferenceLaw C n beta).weight
    (actualBlockFamily C n beta (fun _ => root) (fun _ => queue) index).weight)=1
  rw [centeredGeneratingLinear_constant]
  exact FiniteDist.sum_one _

/-- Every genuine source-set term starts at that source cardinality. The
physical laws and the conditioned root coefficient are fully instantiated. -/
theorem actual_forward_rootSet_hasOrder (C : ℝ) (n : ℕ) (beta : ℝ)
    (sample : Window (queueCutoff n) × Equiv.Perm (blockIndex n))
    (selected : Finset (Fin (Parameters.bodies n))) :
    HasOrder (fun _ : Fin (Parameters.modulus n) => 1) selected.card
      (rootSetResponseLinear n selected (fun roots => actualConditionalForwardPolynomial C n beta roots sample)) := by
  let polynomial : Fin (Parameters.bodies n) → Window (v7RootCutoff n) → Table (Fin (Parameters.modulus n)) :=
    fun index root => actualBlockConditionalPolynomial C n beta ((actualRootIndex n).symm index)
      root (actualQueueShifts n sample ((actualRootIndex n).symm index))
  have hc := canonical_polynomial_product_hasOrder (fun _ : Fin (Parameters.bodies n) => bodyRootReference n)
    selected (actualRootResponseCoefficient n selected) (actualRootResponseCoefficient_canonical n selected)
    polynomial (fun index root => actualBlockConditionalPolynomial_constant C n beta _ _ _)
  have he (roots : actualRootWord n) : actualConditionalForwardPolynomial C n beta roots sample =
      ∏ index : Fin (Parameters.bodies n), polynomial index (roots index) := by
    rw [actualConditionalForwardPolynomial_factor]
    have hh := (actualRootIndex n).symm.prod_comp (fun index => actualBlockConditionalPolynomial C n beta index
      (actualRootField n roots index) (actualQueueShifts n sample index))
    simpa only [actualRootField,Equiv.apply_symm_apply] using hh.symm
  have heq : (fun roots => actualConditionalForwardPolynomial C n beta roots sample) =
      (fun roots => ∏ index : Fin (Parameters.bodies n), polynomial index (roots index)) := funext he
  rw [heq]
  exact hc


theorem actual_forward_rootSet_truncate_zero (C : ℝ) (n : ℕ) (beta : ℝ)
    (sample : Window (queueCutoff n) × Equiv.Perm (blockIndex n))
    (selected : Finset (Fin (Parameters.bodies n))) (cutoff : ℕ) (hlarge : cutoff < selected.card) :
    truncate (fun _ : Fin (Parameters.modulus n) => 1) cutoff
      (rootSetResponseLinear n selected (fun roots => actualConditionalForwardPolynomial C n beta roots sample))=0 :=
  truncate_of_hasOrder _ cutoff _ (hasOrder_mono _ (cutoff+1) selected.card _
    (actual_forward_rootSet_hasOrder C n beta sample selected) hlarge)

/-- The true correlated-root background differs from the independent-root
background only in degrees at least two. -/
theorem actualForwardRootDefectPolynomial_hasOrder (C : ℝ) (n : ℕ) (beta : ℝ) :
    HasOrder (fun _ : Fin (Parameters.modulus n) => 1) 2
      (actualForwardRootDefectPolynomial C n beta) := by
  unfold actualForwardRootDefectPolynomial
  apply hasOrder_sum
  intro sample _
  have hroot : HasOrder (fun _ : Fin (Parameters.modulus n) => 1) 2
      (rootDefectResponseLinear n (fun roots => actualConditionalForwardPolynomial C n beta roots sample)) := by
    unfold rootDefectResponseLinear
    simp only [LinearMap.sum_apply]
    apply hasOrder_sum
    intro selected hs
    exact hasOrder_mono _ 2 selected.card _ (actual_forward_rootSet_hasOrder C n beta sample selected)
      (Finset.mem_filter.mp hs).2
  intro powers hp
  simp only [MvPolynomial.coeff_smul,hroot powers hp,smul_zero]

/-- No high source set is hidden by the finite output truncation: the
truncated true root defect is the explicit sum over sizes 2 through cutoff. -/
theorem actual_root_defect_truncated_sources (C : ℝ) (n : ℕ) (beta : ℝ) (cutoff : ℕ)
    (sample : Window (queueCutoff n) × Equiv.Perm (blockIndex n)) :
    truncate (fun _ : Fin (Parameters.modulus n) => 1) cutoff
      (rootDefectResponseLinear n (fun roots => actualConditionalForwardPolynomial C n beta roots sample)) =
      ∑ selected ∈ (Finset.univ : Finset (Finset (Fin (Parameters.bodies n)))).filter
        (fun selected => 2≤selected.card ∧ selected.card≤cutoff),
        truncate (fun _ : Fin (Parameters.modulus n) => 1) cutoff
          (rootSetResponseLinear n selected (fun roots => actualConditionalForwardPolynomial C n beta roots sample)) := by
  simp only [rootDefectResponseLinear,LinearMap.sum_apply]
  rw [truncate_finset_sum]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro selected _
  by_cases hlow : 2≤selected.card
  · simp only [if_pos hlow]
    by_cases hhigh : selected.card≤cutoff
    · rw [if_pos ⟨hlow,hhigh⟩]
    · rw [if_neg (fun h => hhigh h.2)]
      exact actual_forward_rootSet_truncate_zero C n beta sample selected cutoff (Nat.lt_of_not_ge hhigh)
  · rw [if_neg hlow,if_neg (fun h => hlow h.1)]

end
end AFT.V7Calibration
