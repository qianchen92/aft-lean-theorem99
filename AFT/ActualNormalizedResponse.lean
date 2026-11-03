import AFT.ActualControlResponse
import AFT.RepresentedRing

/-! # Actual finite normalization and connected root subtraction -/

namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
variable {Color : Type*}

/-- At ordinary color degree, positive order is exactly zero constant term. -/
theorem hasOrder_one_of_constant_zero (table : Table Color)
    (hconstant : MvPolynomial.constantCoeff table = 0) : HasOrder (fun _ : Color => 1) 1 table := by
  intro powers hp
  have hpzero : powers = 0 := by
    ext color
    have hle : powers color ≤ weightedOrder (fun _ : Color => 1) powers := by
      by_cases hc : color ∈ powers.support
      · simpa only [weightedOrder,Finsupp.sum,mul_one] using
          (Finset.single_le_sum (f := fun c => powers c * 1) (fun _ _ => Nat.zero_le _) hc)
      · have hz : powers color = 0 := by
          by_contra hn
          exact hc (Finsupp.mem_support_iff.mpr hn)
        rw [hz]
        exact Nat.zero_le _
    have hh : powers color = 0 := by omega
    exact hh
  subst powers
  exact hconstant

theorem quotient_reciprocal (table : Table Color) (cutoff : ℕ)
    (hconstant : MvPolynomial.constantCoeff table = 1) :
    quotientMap (fun _ : Color => 1) cutoff table *
      quotientMap (fun _ : Color => 1) cutoff (finiteCorrection (table-1) cutoff) = 1 := by
  have ho : HasOrder (fun _ : Color => 1) 1 (table-1) :=
    hasOrder_one_of_constant_zero _ (by rw [map_sub,hconstant,map_one,sub_self])
  have hh := truncate_finiteCorrection_residual (fun _ : Color => 1) cutoff (table-1) ho
  rw [add_sub_cancel] at hh
  have he := (quotient_eq_iff_truncate (fun _ : Color => 1) cutoff
    (table*finiteCorrection (table-1) cutoff) 1).mpr (by simpa only [truncate_one] using hh)
  simpa only [map_mul,map_one] using he

/-- Multiplication by a concrete finite reciprocal is a real linear map. -/
def polynomialMultiplyRight (factor : Table Color) : Module.End ℝ (Table Color) where
  toFun table := table*factor
  map_add' first second := add_mul first second factor
  map_smul' scalar table := by simp only [RingHom.id_apply,smul_mul_assoc]

variable {Slot : Type*} [Fintype Slot] [Fintype Color]

theorem centeredGeneratingLinear_constant (reference : Color → ℝ) (mass : (Slot → Color) → ℝ) :
    MvPolynomial.constantCoeff (centeredGeneratingLinear reference mass) = ∑ word, mass word := by
  simp [centeredGeneratingLinear,centeredFactor,profileForm,Algebra.smul_def]

end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open GaussianSource RepresentedPolynomial HistogramNormalization BlockProducts
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance actualNormalizedResponseFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance actualNormalizedResponseSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
local instance actualNormalizedResponseSigmaDecEq {ι : Type*} {fiber : ι → Type*} : DecidableEq (Sigma fiber) := Classical.decEq _

/-- The actual positive background at one full root word and one common
queue sample, on every original physical output slot. -/
def actualConditionalForwardPolynomial (C : ℝ) (n : ℕ) (beta : ℝ)
    (roots : actualRootWord n) (sample : Window (queueCutoff n) × Equiv.Perm (blockIndex n)) :
    Table (Fin (Parameters.modulus n)) :=
  centeredGeneratingLinear (actualReferenceLaw C n beta).weight
    (blockMass (blockSlots n) (actualBlockFamily C n beta (actualRootField n roots) (actualQueueShifts n sample)))

def actualCorrelatedForwardPolynomial (C : ℝ) (n : ℕ) (beta : ℝ) : Table (Fin (Parameters.modulus n)) :=
  ∑ sample, (FiniteDist.retype (actualQueuePlacementLaw n)).weight sample •
    actualRootResponseLinear n (fun roots => actualConditionalForwardPolynomial C n beta roots sample)

def actualIndependentForwardPolynomial (C : ℝ) (n : ℕ) (beta : ℝ) : Table (Fin (Parameters.modulus n)) :=
  ∑ sample, (FiniteDist.retype (actualQueuePlacementLaw n)).weight sample •
    independentRootResponseLinear n (fun roots => actualConditionalForwardPolynomial C n beta roots sample)

def actualForwardRootDefectPolynomial (C : ℝ) (n : ℕ) (beta : ℝ) : Table (Fin (Parameters.modulus n)) :=
  ∑ sample, (FiniteDist.retype (actualQueuePlacementLaw n)).weight sample •
    rootDefectResponseLinear n (fun roots => actualConditionalForwardPolynomial C n beta roots sample)

theorem actual_forward_root_defect (C : ℝ) (n : ℕ) (beta : ℝ) :
    actualCorrelatedForwardPolynomial C n beta =
      actualIndependentForwardPolynomial C n beta + actualForwardRootDefectPolynomial C n beta := by
  simp only [actualCorrelatedForwardPolynomial,actualIndependentForwardPolynomial,
    actualForwardRootDefectPolynomial,actual_root_response_defect,smul_add,Finset.sum_add_distrib]

/-- This background is the actual correlated output law already used in
all complete-tail estimates. -/
theorem actual_correlated_forward_physical (C : ℝ) (n : ℕ) (beta : ℝ) :
    actualCorrelatedForwardPolynomial C n beta =
      centeredGeneratingLinear (actualReferenceLaw C n beta).weight (actualRootQueueMass C n beta) := by
  unfold actualRootQueueMass
  rw [centeredGeneratingLinear_mixture]
  unfold actualCorrelatedForwardPolynomial
  apply Finset.sum_congr rfl
  intro sample _
  congr 1
  unfold actualConditionalRootMass
  rw [centeredGeneratingLinear_mixture]
  rfl

theorem actualConditionalForwardPolynomial_constant (C : ℝ) (n : ℕ) (beta : ℝ)
    (roots : actualRootWord n) (sample : Window (queueCutoff n) × Equiv.Perm (blockIndex n)) :
    MvPolynomial.constantCoeff (actualConditionalForwardPolynomial C n beta roots sample) = 1 := by
  rw [actualConditionalForwardPolynomial,centeredGeneratingLinear_constant]
  change (∑ word : Sigma (blockSlots n) → Fin (Parameters.modulus n),
    ∏ index, (actualBlockFamily C n beta (actualRootField n roots) (actualQueueShifts n sample) index).weight
      (fun slot => word ⟨index,slot⟩)) = 1
  rw [JointPhysicalChannel.product_total]
  simp only [FiniteDist.sum_one,Finset.prod_const_one]

theorem actualCorrelatedForwardPolynomial_constant (C : ℝ) (n : ℕ) (beta : ℝ) :
    MvPolynomial.constantCoeff (actualCorrelatedForwardPolynomial C n beta) = 1 := by
  simp only [actualCorrelatedForwardPolynomial,actualRootResponseLinear,LinearMap.coe_mk,AddHom.coe_mk,
    map_sum,Algebra.smul_def,MvPolynomial.algebraMap_eq,map_mul,MvPolynomial.constantCoeff_C,
    actualConditionalForwardPolynomial_constant,mul_one,FiniteDist.sum_one]

theorem actualIndependentForwardPolynomial_constant (C : ℝ) (n : ℕ) (beta : ℝ) :
    MvPolynomial.constantCoeff (actualIndependentForwardPolynomial C n beta) = 1 := by
  simp only [actualIndependentForwardPolynomial,independentRootResponseLinear,LinearMap.coe_mk,AddHom.coe_mk,
    map_sum,Algebra.smul_def,MvPolynomial.algebraMap_eq,map_mul,MvPolynomial.constantCoeff_C,
    actualConditionalForwardPolynomial_constant,mul_one,FiniteDist.sum_one]

/-- Reciprocal of the already averaged actual forward transform. -/
def actualForwardReciprocal (C : ℝ) (n : ℕ) (beta : ℝ) (cutoff : ℕ) : Table (Fin (Parameters.modulus n)) :=
  finiteCorrection (actualCorrelatedForwardPolynomial C n beta-1) cutoff

def actualIndependentForwardReciprocal (C : ℝ) (n : ℕ) (beta : ℝ) (cutoff : ℕ) : Table (Fin (Parameters.modulus n)) :=
  finiteCorrection (actualIndependentForwardPolynomial C n beta-1) cutoff

theorem actual_forward_reciprocal (C : ℝ) (n : ℕ) (beta : ℝ) (cutoff : ℕ) :
    quotientMap (fun _ : Fin (Parameters.modulus n) => 1) cutoff (actualCorrelatedForwardPolynomial C n beta) *
      quotientMap (fun _ : Fin (Parameters.modulus n) => 1) cutoff (actualForwardReciprocal C n beta cutoff) = 1 :=
  quotient_reciprocal _ cutoff (actualCorrelatedForwardPolynomial_constant C n beta)

theorem actual_independent_forward_reciprocal (C : ℝ) (n : ℕ) (beta : ℝ) (cutoff : ℕ) :
    quotientMap (fun _ : Fin (Parameters.modulus n) => 1) cutoff (actualIndependentForwardPolynomial C n beta) *
      quotientMap (fun _ : Fin (Parameters.modulus n) => 1) cutoff (actualIndependentForwardReciprocal C n beta cutoff) = 1 :=
  quotient_reciprocal _ cutoff (actualIndependentForwardPolynomial_constant C n beta)

/-- Normalization is a concrete finite polynomial operator on the full
joint input kernel; only degrees above the cutoff are identified later. -/
def actualNormalizedControlLinear (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (count : ℕ) (role : Fin count → Bool) (selected : Finset (blockIndex n))
    (placement : ActualTaggedPlacement n count role selected) (cutoff : ℕ) :
    ((Fin count → Fin (Parameters.modulus n)) → ℝ) →ₗ[ℝ] Table (Fin (Parameters.modulus n)) :=
  (polynomialMultiplyRight (actualForwardReciprocal C n beta cutoff)).comp
    (actualControlResponseLinear C n beta charts count role selected placement)

def actualIndependentNormalizedControlLinear (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (count : ℕ) (role : Fin count → Bool) (selected : Finset (blockIndex n))
    (placement : ActualTaggedPlacement n count role selected) (cutoff : ℕ) :
    ((Fin count → Fin (Parameters.modulus n)) → ℝ) →ₗ[ℝ] Table (Fin (Parameters.modulus n)) :=
  (polynomialMultiplyRight (actualIndependentForwardReciprocal C n beta cutoff)).comp
    (actualIndependentControlResponseLinear C n beta charts count role selected placement)

/-- The connected numerator subtracts the full independent normalized
response, including all nonlinear local terms. -/
def actualConnectedControlNumeratorLinear (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (count : ℕ) (role : Fin count → Bool) (selected : Finset (blockIndex n))
    (placement : ActualTaggedPlacement n count role selected) (cutoff : ℕ) :
    ((Fin count → Fin (Parameters.modulus n)) → ℝ) →ₗ[ℝ] Table (Fin (Parameters.modulus n)) :=
  actualControlRootDefectLinear C n beta charts count role selected placement -
    (polynomialMultiplyRight (actualForwardRootDefectPolynomial C n beta)).comp
      (actualIndependentNormalizedControlLinear C n beta charts count role selected placement cutoff)

def actualConnectedControlResponseLinear (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (count : ℕ) (role : Fin count → Bool) (selected : Finset (blockIndex n))
    (placement : ActualTaggedPlacement n count role selected) (cutoff : ℕ) :
    ((Fin count → Fin (Parameters.modulus n)) → ℝ) →ₗ[ℝ] Table (Fin (Parameters.modulus n)) :=
  (polynomialMultiplyRight (actualForwardReciprocal C n beta cutoff)).comp
    (actualConnectedControlNumeratorLinear C n beta charts count role selected placement cutoff)

/-- Exact normalized connected identity for the actual physical input
channel and the actual conditioned root/queue background. -/
theorem actual_normalized_connected_response (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (count : ℕ) (role : Fin count → Bool) (selected : Finset (blockIndex n))
    (placement : ActualTaggedPlacement n count role selected) (cutoff : ℕ)
    (kernel : (Fin count → Fin (Parameters.modulus n)) → ℝ) :
    quotientMap (fun _ : Fin (Parameters.modulus n) => 1) cutoff
      (actualNormalizedControlLinear C n beta charts count role selected placement cutoff kernel) =
    quotientMap (fun _ : Fin (Parameters.modulus n) => 1) cutoff
      (actualIndependentNormalizedControlLinear C n beta charts count role selected placement cutoff kernel +
        actualConnectedControlResponseLinear C n beta charts count role selected placement cutoff kernel) := by
  let Q := quotientMap (fun _ : Fin (Parameters.modulus n) => 1) cutoff
  have hactual := actual_forward_reciprocal C n beta cutoff
  have hindependent := actual_independent_forward_reciprocal C n beta cutoff
  have hbackground := congrArg Q (actual_forward_root_defect C n beta)
  have hresponse := congrArg (fun operator => Q (operator kernel))
    (actual_control_response_defect C n beta charts count role selected placement)
  change Q (actualCorrelatedForwardPolynomial C n beta)*Q (actualForwardReciprocal C n beta cutoff)=1 at hactual
  change Q (actualIndependentForwardPolynomial C n beta)*Q (actualIndependentForwardReciprocal C n beta cutoff)=1 at hindependent
  simp only [map_add,LinearMap.add_apply] at hbackground hresponse
  change Q (_*actualForwardReciprocal C n beta cutoff) = Q (_*actualIndependentForwardReciprocal C n beta cutoff+
    (_-(_*actualIndependentForwardReciprocal C n beta cutoff)*actualForwardRootDefectPolynomial C n beta)*actualForwardReciprocal C n beta cutoff)
  simp only [map_add,map_sub,map_mul]
  rw [hresponse]
  rw [hbackground] at hactual
  linear_combination (Q (actualIndependentControlResponseLinear C n beta charts count role selected placement kernel) *
    Q (actualIndependentForwardReciprocal C n beta cutoff)) * hactual -
    (Q (actualIndependentControlResponseLinear C n beta charts count role selected placement kernel) *
      Q (actualForwardReciprocal C n beta cutoff)) * hindependent

end
end AFT.V7Calibration
