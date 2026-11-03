import AFT.RootGroupedPolynomial
import AFT.RootSourceChoices
import AFT.ReferenceCoefficientPolynomial
import AFT.ActualBoundaryNormalizer

/-! # Exact images of the efficient joint root-source tables -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

/-- A mass-zero local physical response has precisely its nonempty
reference-centered coefficients, with the empty coefficient removed exactly. -/
theorem sum_nonempty_referenceCoefficientForm (primary reference : FiniteDist Color)
    (hp : ∀ color,0<primary.weight color) (mass : (Slot → Color) → ℝ)
    (hmass : ∑ word,mass word=0) :
    (∑ selected : {selected : Finset Slot // selected.Nonempty},
      referenceCoefficientForm primary reference mass selected.val)=
      centeredGeneratingLinear reference.weight mass := by
  rw [← Finset.sum_subtype ((Finset.univ : Finset (Finset Slot)).erase ∅)
    (by intro selected; simp only [Finset.mem_erase,Finset.mem_univ,and_true,Finset.nonempty_iff_ne_empty])]
  rw [centeredGeneratingLinear_reference_expansion primary reference hp mass]
  have hh := Finset.sum_erase_add (Finset.univ : Finset (Finset Slot))
    (referenceCoefficientForm primary reference mass) (Finset.mem_univ ∅)
  simpa only [referenceCoefficientForm_empty,hmass,map_zero,add_zero] using hh
end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open GaussianSource RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
local instance rootSourcePolyFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance rootSourcePolySumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
local instance rootSourcePolySubtypeDecEq {α : Type*} (selected : Finset α) : DecidableEq selected := Classical.decEq _
local instance rootSourcePolyBlockDecEq (n : ℕ) (index : blockIndex n) : DecidableEq (blockSlots n index) := Classical.decEq _

/-- The true root-centered block has zero total mass for every root,
including the complete attached shared-source triple. -/
theorem actual_centered_root_block_mass_zero_eventually (C : ℝ) (hC : 1≤C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n)≤beta n ∧
      beta n≤2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ index : blockIndex n,∀ queue : ℤ,|queue|≤(queueCutoff n : ℤ) →
    ∀ root : Window (v7RootCutoff n),∑ word,actualCenteredRootBlock C n (beta n) index queue root word=0 := by
  filter_upwards [actual_centered_root_block_eq_eventually C hC beta hbeta]
    with n he index queue hq root
  simp_rw [he index queue hq root]
  rw [Finset.sum_sub_distrib,FiniteDist.sum_one,Finset.sum_comm]
  simp_rw [← Finset.mul_sum,FiniteDist.sum_one,mul_one]
  rw [FiniteDist.sum_one,sub_self]

/-- Each grouped calibrated seed is exactly the product of its genuine
selected block coefficients, averaged with the one joint root kernel. -/
theorem actualRootSourceChoiceSeed_image (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (hop : operator.toLinearMap=actualResponse C n) (hrho : v7Activation C n≠0)
    (hp : ∀ color,(actualPrimaryLaw C n beta).weight color≠0)
    (sample : Window (queueCutoff n) × Equiv.Perm (blockIndex n))
    (selected : Finset (Fin (Parameters.bodies n))) (choice : RootSourceChoice n selected) :
    actualLeadingOutput C n beta (MvPolynomial.X (actualRootSourceChoiceSeed C n beta operator sample selected choice))=
      ∑ roots : selected → Window (v7RootCutoff n),
        MvPolynomial.C ((FiniteDist.independent (fun _ : selected => bodyRootReference n)).weight roots*
          actualRootSubsetKernel n selected roots)*∏ index : selected,
          referenceCoefficientForm (actualPrimaryLaw C n beta) (actualReferenceLaw C n beta)
            (actualCenteredRootBlock C n beta ((actualRootIndex n).symm index)
              (actualBodyRootSourceOffset n sample index) (roots index)) (choice index).val := by
  have hi := actualGroupedRootInput_image (fun index : selected => (choice index).val)
    C n beta operator hop hrho hp
    (fun index => actualRootBlockCoefficient C n beta ((actualRootIndex n).symm index)
      (actualBodyRootSourceOffset n sample index) (choice index).val) (actualRootSubsetKernel n selected)
  exact hi.trans (RootTensor.groupedDensity_polynomial (fun index : selected => (choice index).val)
    (fun _ => bodyRootReference n) (fun _ => actualPrimaryLaw C n beta) _ _)

/-- Summing every nonempty local selection reconstructs each complete
centered physical block before averaging its arbitrary joint root coefficient. -/
theorem actual_root_source_choice_table_image_eventually (C : ℝ) (hC : 1≤C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n)≤beta n ∧
      beta n≤2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n →∀ sample,∀ selected : Finset (Fin (Parameters.bodies n)),
    actualLeadingOutput C n (beta n) (actualRootSourceChoiceTable C n (beta n) operator sample selected)=
      ∑ roots : selected → Window (v7RootCutoff n),
        MvPolynomial.C ((FiniteDist.independent (fun _ : selected => bodyRootReference n)).weight roots*
          actualRootSubsetKernel n selected roots)*∏ index : selected,
          centeredGeneratingLinear (actualReferenceLaw C n (beta n)).weight
            (actualCenteredRootBlock C n (beta n) ((actualRootIndex n).symm index)
              (actualBodyRootSourceOffset n sample index) (roots index)) := by
  filter_upwards [actual_centered_root_block_mass_zero_eventually C hC beta hbeta,
    actual_boundary_normalizer_eventually C hC beta hbeta,eventually_ge_atTop 1]
    with n hz hp hn operator hop sample selected
  have hrho : v7Activation C n≠0 := (activation_positive _ _ _ _ (legFeatureCount_positive C n hC hn)).ne'
  unfold actualRootSourceChoiceTable
  simp_rw [map_sum,actualRootSourceChoiceSeed_image C n (beta n) operator hop hrho (fun color => (hp.1 color).ne')]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro roots _
  rw [← Finset.mul_sum]
  congr 1
  have he := Fintype.prod_sum (fun (index : selected) (choice : RootLocalChoice n ((actualRootIndex n).symm index)) =>
    referenceCoefficientForm (actualPrimaryLaw C n (beta n)) (actualReferenceLaw C n (beta n))
      (actualCenteredRootBlock C n (beta n) ((actualRootIndex n).symm index)
        (actualBodyRootSourceOffset n sample index) (roots index)) choice.val)
  rw [← he]
  apply Finset.prod_congr rfl
  intro index _
  exact sum_nonempty_referenceCoefficientForm _ _ hp.1 _
    (hz ((actualRootIndex n).symm index) _ (actualQueueShifts_bound n sample _) (roots index))
end
end AFT.V7Calibration
