import AFT.ControlPolynomialFactorization
import AFT.ActualPublicTaggedPlacement
import AFT.RootPartitionPolynomial
import AFT.IndependentPositiveDenominator
import AFT.IndependentRoleSources

/-! # Independent-root response of the actual disjoint public placements -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
local instance independentPublicFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance independentPublicSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
local instance independentPublicSubtypeDecEq {α : Type*} {p : α → Prop} : DecidableEq (Subtype p) := Classical.decEq _
attribute [local instance] actualModulusNeZero

def publicPrimaryRootPolynomial (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (input : Fin (Parameters.modulus n)) (attached compensator : Window (v7RootCutoff n)) :
    Table (Fin (Parameters.modulus n)) :=
  centeredGeneratingLinear (actualReferenceLaw C n beta).weight
    (actualPairedDensityChannel C n beta charts attached compensator 0 (Pi.single input 1))

def publicBodyRootPolynomial (C : ℝ) (n : ℕ) (beta : ℝ)
    (input : Fin (Parameters.modulus n)) (root : Window (v7RootCutoff n)) : Table (Fin (Parameters.modulus n)) :=
  centeredGeneratingLinear (actualReferenceLaw C n beta).weight
    (actualBodyDensityChannel C n beta root (Pi.single input 1))

def publicInputRootPolynomial (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    {count : ℕ} (role : Fin count → Bool) (input : Fin count → Fin (Parameters.modulus n))
    (roots : RoleSources role → Window (v7RootCutoff n)) : Table (Fin (Parameters.modulus n)) :=
  (∏ index : PrimaryRoles role,publicPrimaryRootPolynomial C n beta charts (input index.val)
    (roots (.inl (.inl index))) (roots (.inl (.inr index))))*
      ∏ index : BodyRoles role,publicBodyRootPolynomial C n beta (input index.val) (roots (.inr index))

def publicInputIndependentPolynomial (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    {count : ℕ} (role : Fin count → Bool) (input : Fin count → Fin (Parameters.modulus n)) :
    Table (Fin (Parameters.modulus n)) :=
  (∏ index : PrimaryRoles role,centeredGeneratingLinear (actualReferenceLaw C n beta).weight
    (independentPairedNumerator C n beta charts (fun color =>
      (actualPrimaryLaw C n beta).weight color*(Pi.single (input index.val) 1 : Fin (Parameters.modulus n) → ℝ) color)))*
    ∏ index : BodyRoles role,∑ root : Window (v7RootCutoff n),MvPolynomial.C ((bodyRootReference n).weight root)*
      publicBodyRootPolynomial C n beta (input index.val) root

/-- This identity uses the actual public source injection, so every role
reads precisely its own roots and the queue is absent at those positions. -/
theorem actual_public_role_polynomial_factor (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (count : ℕ) (role : Fin count → Bool) (queue : Window (queueCutoff n)) (placement : Equiv.Perm (blockIndex n))
    (primary : ActualPublicPrimaryChoice n placement (PrimaryRoles role))
    (body : ActualPublicBodyChoice n placement (BodyRoles role))
    (roots : actualRootWord n) (input : Fin count → Fin (Parameters.modulus n)) :
    (∏ index : Fin count,centeredGeneratingLinear (actualReferenceLaw C n beta).weight
      (actualRoleChannel C n beta charts
        (actualRootField n roots ((actualPublicTaggedPlacement n placement role primary body).attached index))
        (actualRootField n roots ((actualPublicTaggedPlacement n placement role primary body).compensator index))
        (actualQueueShifts n (queue,placement) ((actualPublicTaggedPlacement n placement role primary body).attached index))
        (actualRootField n roots ((actualPublicTaggedPlacement n placement role primary body).body index)+
          actualQueueShifts n (queue,placement) ((actualPublicTaggedPlacement n placement role primary body).body index))
        (role index) (Pi.single (input index) 1))) =
      publicInputRootPolynomial C n beta charts role input (fun source =>
        roots (actualRootIndex n (actualPublicSourceEmbedding n placement primary body source))) := by
  rw [← (rolePartition role).prod_comp]
  rw [Fintype.prod_sum_type]
  unfold publicInputRootPolynomial
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr (by ext; simp)
    intro index _
    simp only [show (rolePartition role) (Sum.inl index)=index.val from rfl]
    change centeredGeneratingLinear _ (actualRoleChannel C n beta charts _ _ _ _ (role index.val) _) = _
    rw [(actualPublicTaggedPlacement_primary_queue_zero n placement role primary body queue index).1,index.property]
    change centeredGeneratingLinear _ (actualPairedDensityChannel C n beta charts
      (actualRootField n roots (actualPublicAttached n placement role primary index.val))
      (actualRootField n roots (actualPublicCompensator n placement role primary index.val)) 0 _) = _
    rw [actualPublicAttached_source n placement role primary body index,
      actualPublicCompensator_source n placement role primary body index]
    rfl
  · apply Finset.prod_congr (by ext; simp)
    intro index _
    simp only [show (rolePartition role) (Sum.inr index)=index.val from rfl]
    change centeredGeneratingLinear _ (actualRoleChannel C n beta charts _ _ _ _ (role index.val) _) = _
    have hrole : role index.val=false := by simpa using index.property
    rw [actualPublicTaggedPlacement_body_queue_zero n placement role primary body queue index,hrole,add_zero]
    change centeredGeneratingLinear _ (actualBodyDensityChannel C n beta
      (actualRootField n roots (actualPublicBody n placement role body index.val)) _) = _
    rw [actualPublicBody_source n placement role primary body index]
    rfl

/-- Averaging the two actual marginal roots commutes with the complete
four-output generating map, including its constant coefficient. -/
theorem publicPrimaryRootPolynomial_average (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (input : Fin (Parameters.modulus n)) :
    (∑ attached : Window (v7RootCutoff n),∑ compensator : Window (v7RootCutoff n),
      MvPolynomial.C ((bodyRootReference n).weight attached*(bodyRootReference n).weight compensator)*
        publicPrimaryRootPolynomial C n beta charts input attached compensator) =
      centeredGeneratingLinear (actualReferenceLaw C n beta).weight
        (independentPairedNumerator C n beta charts (fun color =>
          (actualPrimaryLaw C n beta).weight color*(Pi.single input 1 : Fin (Parameters.modulus n) → ℝ) color)) := by
  have hm : independentPairedNumerator C n beta charts (fun color =>
        (actualPrimaryLaw C n beta).weight color*(Pi.single input 1 : Fin (Parameters.modulus n) → ℝ) color) =
      ∑ attached : Window (v7RootCutoff n),∑ compensator : Window (v7RootCutoff n),
        ((bodyRootReference n).weight attached*(bodyRootReference n).weight compensator) •
          actualPairedDensityChannel C n beta charts attached compensator 0 (Pi.single input 1) := by
    funext word
    simp only [independentPairedNumerator,actualJointPairedNumerator,pairedRootReference,Fintype.sum_prod_type,
      FiniteDist.prod_weight,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,actualPairedDensityChannel_apply]
    rfl
  rw [hm]
  simp only [map_sum]
  simp only [map_smul]
  simp only [publicPrimaryRootPolynomial,Algebra.smul_def,MvPolynomial.algebraMap_eq]

/-- Actual grouped-root Fubini for all selected roles. -/
theorem publicInputRootPolynomial_average (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    {count : ℕ} (role : Fin count → Bool) (input : Fin count → Fin (Parameters.modulus n)) :
    (∑ roots : RoleSources role → Window (v7RootCutoff n),
      MvPolynomial.C ((FiniteDist.independent (fun _ : RoleSources role => bodyRootReference n)).weight roots)*
        publicInputRootPolynomial C n beta charts role input roots) =
      publicInputIndependentPolynomial C n beta charts role input := by
  have hh := independent_role_sources (bodyRootReference n)
    (fun index : PrimaryRoles role => publicPrimaryRootPolynomial C n beta charts (input index.val))
    (fun index : BodyRoles role => publicBodyRootPolynomial C n beta (input index.val))
  simp only [Algebra.smul_def,MvPolynomial.algebraMap_eq] at hh
  apply Eq.trans ?_ (hh.trans ?_)
  · apply Finset.sum_congr (by ext; simp)
    intro roots _
    unfold publicInputRootPolynomial
    congr 2
  · simp only [publicPrimaryRootPolynomial_average,publicInputIndependentPolynomial]

/-- Integrate the untouched roots under their genuine law, retaining the
complete polynomial of each complementary block. -/
theorem actual_public_single_input_average_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    ∀ count : ℕ, ∀ role : Fin count → Bool, ∀ queue : Window (queueCutoff n), ∀ placement : Equiv.Perm (blockIndex n),
    ∀ primary : ActualPublicPrimaryChoice n placement (PrimaryRoles role),
    ∀ body : ActualPublicBodyChoice n placement (BodyRoles role),
    ∀ input : Fin count → Fin (Parameters.modulus n),
    (∑ roots : actualRootWord n, MvPolynomial.C ((actualIndependentRoots n).weight roots)*
      (publicInputRootPolynomial C n (beta n) charts role input (fun source =>
        roots (actualRootIndex n (actualPublicSourceEmbedding n placement primary body source)))*
        ∏ index : {index : blockIndex n // index ∉ actualPublicSelected n placement primary body},
          actualBlockConditionalPolynomial C n (beta n) index (actualRootField n roots index)
            (actualQueueShifts n (queue,placement) index))) =
      publicInputIndependentPolynomial C n (beta n) charts role input*
        ∏ index : {index : blockIndex n // index ∉ actualPublicSelected n placement primary body},
          blockPhysicalPolynomial C n (beta n) index (actualQueueShifts n (queue,placement) index) := by
  filter_upwards [actual_block_root_polynomial_eventually C hC beta hbeta] with n hb charts count role queue placement primary body input
  let selected := actualPublicSelected n placement primary body
  let joint := fun roots : selected → Window (v7RootCutoff n) =>
    publicInputRootPolynomial C n (beta n) charts role input (fun source => roots (actualPublicSourceEquiv n placement primary body source))
  let outside := fun (index : {index : blockIndex n // index ∉ selected}) (root : Window (v7RootCutoff n)) =>
    actualBlockConditionalPolynomial C n (beta n) index root (actualQueueShifts n (queue,placement) index)
  have hi := independent_polynomial_reindex (bodyRootReference n) (actualRootIndex n)
    (fun roots : Fin (Parameters.bodies n) → Window (v7RootCutoff n) =>
      publicInputRootPolynomial C n (beta n) charts role input (fun source =>
        roots (actualRootIndex n (actualPublicSourceEmbedding n placement primary body source)))*
          ∏ index : {index : blockIndex n // index ∉ selected},outside index (roots (actualRootIndex n index)))
  simp only [Equiv.symm_apply_apply] at hi
  apply Eq.trans ?_ (hi.trans ?_)
  · apply Finset.sum_congr (by ext; simp)
    intro roots _
    rfl
  have hs := independent_partition_polynomial (bodyRootReference n) selected joint outside
  apply Eq.trans ?_ (hs.trans ?_)
  · rfl
  have hselected := independent_polynomial_reindex (bodyRootReference n)
    (actualPublicSourceEquiv n placement primary body) joint
  simp only [joint,Equiv.symm_apply_apply] at hselected
  rw [hselected,publicInputRootPolynomial_average]
  apply congrArg (publicInputIndependentPolynomial C n (beta n) charts role input * ·)
  apply Finset.prod_congr (by ext; simp)
  intro index _
  simpa only [Algebra.smul_def,MvPolynomial.algebraMap_eq] using
    hb index _ (actualQueueShifts_bound n (queue,placement) index)
end
end AFT.V7Calibration
