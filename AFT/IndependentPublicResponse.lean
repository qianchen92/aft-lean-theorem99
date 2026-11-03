import AFT.IndependentPublicFactorization

/-! # Exact independent-root response for every genuine public pool selection -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
local instance independentPublicResponseFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance independentPublicResponseSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
local instance independentPublicResponseSubtypeDecEq {α : Type*} {p : α → Prop} : DecidableEq (Subtype p) := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- All old input coordinates stay in one joint kernel. The public source
matching supplies the independence of the root groups, while the queue
value and its placement remain fixed and shared throughout the identity. -/
theorem actual_independent_public_response_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    ∀ count : ℕ, ∀ role : Fin count → Bool, ∀ queue : Window (queueCutoff n), ∀ placement : Equiv.Perm (blockIndex n),
    ∀ primary : ActualPublicPrimaryChoice n placement (PrimaryRoles role),
    ∀ body : ActualPublicBodyChoice n placement (BodyRoles role),
    ∀ kernel : (Fin count → Fin (Parameters.modulus n)) → ℝ,
    independentRootResponseLinear n (fun roots =>
      actualConditionalControlPolynomialLinear C n (beta n) charts count role
        (actualPublicSelected n placement primary body) (actualPublicTaggedPlacement n placement role primary body)
        roots (queue,placement) kernel) =
      (∑ input,MvPolynomial.C (kernel input)*publicInputIndependentPolynomial C n (beta n) charts role input)*
        ∏ index : {index : blockIndex n // index ∉ actualPublicSelected n placement primary body},
          blockPhysicalPolynomial C n (beta n) index (actualQueueShifts n (queue,placement) index) := by
  filter_upwards [actual_public_single_input_average_eventually C hC beta hbeta]
    with n ht charts count role queue placement primary body kernel
  change (∑ roots : actualRootWord n,(actualIndependentRoots n).weight roots •
    actualConditionalControlPolynomialLinear C n (beta n) charts count role
      (actualPublicSelected n placement primary body) (actualPublicTaggedPlacement n placement role primary body)
      roots (queue,placement) kernel) = _
  simp_rw [actual_conditional_control_polynomial_factor,
    actual_public_role_polynomial_factor C n (beta n) charts count role queue placement primary body]
  simp only [Algebra.smul_def,MvPolynomial.algebraMap_eq,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro input _
  have hlocal (roots : actualRootWord n) :
      MvPolynomial.C ((actualIndependentRoots n).weight roots)*
        ((MvPolynomial.C (kernel input)*publicInputRootPolynomial C n (beta n) charts role input
          (fun source => roots (actualRootIndex n (actualPublicSourceEmbedding n placement primary body source))))*
            ∏ index : {index : blockIndex n // index ∉ actualPublicSelected n placement primary body},
              actualBlockConditionalPolynomial C n (beta n) index (actualRootField n roots index)
                (actualQueueShifts n (queue,placement) index)) =
      MvPolynomial.C (kernel input)*(MvPolynomial.C ((actualIndependentRoots n).weight roots)*
        (publicInputRootPolynomial C n (beta n) charts role input
          (fun source => roots (actualRootIndex n (actualPublicSourceEmbedding n placement primary body source)))*
            ∏ index : {index : blockIndex n // index ∉ actualPublicSelected n placement primary body},
              actualBlockConditionalPolynomial C n (beta n) index (actualRootField n roots index)
                (actualQueueShifts n (queue,placement) index))) := by ring
  simp_rw [hlocal]
  rw [← Finset.mul_sum,ht charts count role queue placement primary body input]
  ring
end
end AFT.V7Calibration
