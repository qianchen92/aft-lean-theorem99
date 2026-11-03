import AFT.ActualRootResponse
import AFT.SignedMassOperations

/-! # The actual finite controlled response and its exact root defect -/

namespace AFT.RepresentedPolynomial
open HistogramNormalization
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Source Slot OtherSlot Color : Type*} [Fintype Source] [Fintype Slot] [Fintype OtherSlot] [Fintype Color]

omit [Fintype OtherSlot] in
theorem centeredGeneratingLinear_mixture (reference : Color → ℝ)
    (source : FiniteDist Source) (mass : Source → (Slot → Color) → ℝ) :
    centeredGeneratingLinear reference (mixtureMass source mass) =
      ∑ point, source.weight point • centeredGeneratingLinear reference (mass point) := by
  have heq : mixtureMass source mass = ∑ point, source.weight point • mass point := by
    funext word
    simp only [mixtureMass,FiniteDist.expectation,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [heq,map_sum]
  simp only [map_smul]

omit [Fintype Source] in
theorem centeredGeneratingLinear_renamedMass (reference : Color → ℝ)
    (equiv : Slot ≃ OtherSlot) (mass : (Slot → Color) → ℝ) :
    centeredGeneratingLinear reference (renamedMass equiv mass) = centeredGeneratingLinear reference mass := by
  unfold centeredGeneratingLinear
  simp only [LinearMap.coe_mk,AddHom.coe_mk]
  rw [← (renameWord equiv).sum_comp]
  apply Finset.sum_congr rfl
  intro word _
  have hword : renamedMass equiv mass (renameWord equiv word) = mass word := by
    simp only [renamedMass,renameWord,Equiv.coe_fn_mk,Function.comp_def,Equiv.symm_apply_apply]
  rw [hword]
  congr 1
  change (∏ slot : OtherSlot, centeredFactor reference (word (equiv.symm slot))) = _
  exact equiv.symm.prod_comp (fun slot : Slot => centeredFactor reference (word slot))

end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open GaussianSource RepresentedPolynomial HistogramNormalization BlockProducts
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance actualControlResponseFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance actualControlResponseSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
local instance actualControlResponseSigmaDecEq {ι : Type*} {fiber : ι → Type*} : DecidableEq (Sigma fiber) := Classical.decEq _

/-- The literal physical conditional mass is linear on the full joint
input kernel. Each untouched block remains in its original complement. -/
def actualConditionalControlMassLinear (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (count : ℕ) (role : Fin count → Bool) (selected : Finset (blockIndex n))
    (placement : ActualTaggedPlacement n count role selected)
    (roots : actualRootWord n) (sample : Window (queueCutoff n) × Equiv.Perm (blockIndex n)) :
    ((Fin count → Fin (Parameters.modulus n)) → ℝ) →ₗ[ℝ]
      (((actualMarkedSlots n selected ⊕ actualRemainingSlots n selected) → Fin (Parameters.modulus n)) → ℝ) where
  toFun kernel := actualMarkedBlockMass C n beta selected
    (actualJointTaggedOutput C n beta charts count role selected placement kernel roots sample)
    roots (actualQueueShifts n sample)
  map_add' first second := by
    funext word
    simp only [actualMarkedBlockMass,taggedBlockMass,actualJointTaggedOutput,renamedMass,
      JointPhysicalChannel.mass,Pi.add_apply,add_mul,Finset.sum_add_distrib]
  map_smul' scalar kernel := by
    funext word
    simp only [actualMarkedBlockMass,taggedBlockMass,actualJointTaggedOutput,renamedMass,
      JointPhysicalChannel.mass,Pi.smul_apply,smul_eq_mul,RingHom.id_apply,mul_assoc,← Finset.mul_sum]

/-- Full-degree centered generating response of the genuine conditional
sampling channel, before averaging either of the two shared sources. -/
def actualConditionalControlPolynomialLinear (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (count : ℕ) (role : Fin count → Bool) (selected : Finset (blockIndex n))
    (placement : ActualTaggedPlacement n count role selected)
    (roots : actualRootWord n) (sample : Window (queueCutoff n) × Equiv.Perm (blockIndex n)) :
    ((Fin count → Fin (Parameters.modulus n)) → ℝ) →ₗ[ℝ] MvPolynomial (Fin (Parameters.modulus n)) ℝ :=
  (centeredGeneratingLinear (actualReferenceLaw C n beta).weight).comp
    (actualConditionalControlMassLinear C n beta charts count role selected placement roots sample)

/-- The root word remains an explicit argument of one joint operator. -/
def actualControlSourceResponseLinear (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (count : ℕ) (role : Fin count → Bool) (selected : Finset (blockIndex n))
    (placement : ActualTaggedPlacement n count role selected)
    (sample : Window (queueCutoff n) × Equiv.Perm (blockIndex n)) :
    ((Fin count → Fin (Parameters.modulus n)) → ℝ) →ₗ[ℝ]
      (actualRootWord n → MvPolynomial (Fin (Parameters.modulus n)) ℝ) :=
  LinearMap.pi (fun roots => actualConditionalControlPolynomialLinear C n beta charts count role selected placement roots sample)

/-- The actual signed forward transform integrates the entire conditioned
root word and then the one shared queue sample. -/
def actualControlResponseLinear (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (count : ℕ) (role : Fin count → Bool) (selected : Finset (blockIndex n))
    (placement : ActualTaggedPlacement n count role selected) :
    ((Fin count → Fin (Parameters.modulus n)) → ℝ) →ₗ[ℝ] MvPolynomial (Fin (Parameters.modulus n)) ℝ :=
  ∑ sample, (FiniteDist.retype (actualQueuePlacementLaw n)).weight sample •
    (actualRootResponseLinear n).comp (actualControlSourceResponseLinear C n beta charts count role selected placement sample)

/-- The comparison replaces only the root law. The queue still has one
common value and its original placement law. -/
def actualIndependentControlResponseLinear (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (count : ℕ) (role : Fin count → Bool) (selected : Finset (blockIndex n))
    (placement : ActualTaggedPlacement n count role selected) :
    ((Fin count → Fin (Parameters.modulus n)) → ℝ) →ₗ[ℝ] MvPolynomial (Fin (Parameters.modulus n)) ℝ :=
  ∑ sample, (FiniteDist.retype (actualQueuePlacementLaw n)).weight sample •
    (independentRootResponseLinear n).comp (actualControlSourceResponseLinear C n beta charts count role selected placement sample)

/-- A concrete finite root-set correction, prior to taking its safe input
preimage. Its physical source and output placements are unchanged. -/
def actualControlRootSetResponseLinear (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (count : ℕ) (role : Fin count → Bool) (selected : Finset (blockIndex n))
    (placement : ActualTaggedPlacement n count role selected)
    (rootSet : Finset (Fin (Parameters.bodies n))) :
    ((Fin count → Fin (Parameters.modulus n)) → ℝ) →ₗ[ℝ] MvPolynomial (Fin (Parameters.modulus n)) ℝ :=
  ∑ sample, (FiniteDist.retype (actualQueuePlacementLaw n)).weight sample •
    (rootSetResponseLinear n rootSet).comp (actualControlSourceResponseLinear C n beta charts count role selected placement sample)

def actualControlRootDefectLinear (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (count : ℕ) (role : Fin count → Bool) (selected : Finset (blockIndex n))
    (placement : ActualTaggedPlacement n count role selected) :
    ((Fin count → Fin (Parameters.modulus n)) → ℝ) →ₗ[ℝ] MvPolynomial (Fin (Parameters.modulus n)) ℝ :=
  ∑ rootSet ∈ (Finset.univ : Finset (Finset (Fin (Parameters.bodies n)))).filter (fun rootSet => 2 ≤ rootSet.card),
    actualControlRootSetResponseLinear C n beta charts count role selected placement rootSet

/-- Exact ANOVA decomposition of the actual finite joint-input operator. -/
theorem actual_control_response_defect (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (count : ℕ) (role : Fin count → Bool) (selected : Finset (blockIndex n))
    (placement : ActualTaggedPlacement n count role selected) :
    actualControlResponseLinear C n beta charts count role selected placement =
      actualIndependentControlResponseLinear C n beta charts count role selected placement +
        actualControlRootDefectLinear C n beta charts count role selected placement := by
  ext kernel
  simp only [actualControlResponseLinear,actualIndependentControlResponseLinear,actualControlRootDefectLinear,
    actualControlRootSetResponseLinear,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply,LinearMap.add_apply]
  simp_rw [actual_root_response_defect]
  simp only [smul_add,Finset.sum_add_distrib,rootDefectResponseLinear,LinearMap.sum_apply,Finset.smul_sum]
  congr 1
  rw [Finset.sum_comm]

/-- The operator is exactly the generating polynomial of the existing
actual full physical signed mass, not a formal response surrogate. -/
theorem actual_control_response_physical (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (count : ℕ) (role : Fin count → Bool) (selected : Finset (blockIndex n))
    (placement : ActualTaggedPlacement n count role selected)
    (kernel : (Fin count → Fin (Parameters.modulus n)) → ℝ) :
    actualControlResponseLinear C n beta charts count role selected placement kernel =
      centeredGeneratingLinear (actualReferenceLaw C n beta).weight
        (actualPlacedInputMass C n beta charts count role selected placement kernel) := by
  unfold actualPlacedInputMass
  rw [centeredGeneratingLinear_renamedMass]
  unfold actualMarkedRootQueueMass
  rw [centeredGeneratingLinear_mixture]
  simp only [actualControlResponseLinear,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro sample _
  congr 1
  unfold actualMarkedRootMass
  rw [centeredGeneratingLinear_mixture]
  rfl

end
end AFT.V7Calibration
