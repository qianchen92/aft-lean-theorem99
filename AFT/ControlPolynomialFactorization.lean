import AFT.PhysicalRootFactorization
import AFT.RootGroupedPolynomial

/-! # Exact physical product expansion of every finite joint controlled input -/
namespace AFT.RepresentedPolynomial
open BlockProducts
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {Index Input Color TaggedSlot : Type*} [Fintype Index] [Fintype Input] [Fintype Color] [Fintype TaggedSlot]
variable (Slots : Index → Type*) [∀ index,Fintype (Slots index)]
local instance controlPolynomialFactorizationIndexDecEq : DecidableEq Index := Classical.decEq _
local instance controlPolynomialFactorizationSigmaDecEq : DecidableEq (Sigma Slots) := Classical.decEq _
local instance controlPolynomialFactorizationSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _

omit [Fintype Input] [Fintype TaggedSlot] in
/-- Exact finite Fubini for arbitrary signed local physical masses. -/
theorem centeredGeneratingLinear_signed_product (reference : Color → ℝ)
    (mass : (index : Index) → (Slots index → Color) → ℝ) :
    centeredGeneratingLinear reference (fun word : Sigma Slots → Color =>
      ∏ index,mass index (fun slot => word ⟨index,slot⟩)) =
      ∏ index,centeredGeneratingLinear reference (mass index) := by
  unfold centeredGeneratingLinear
  simp only [LinearMap.coe_mk,AddHom.coe_mk,Algebra.smul_def,MvPolynomial.algebraMap_eq,
    map_prod,Fintype.prod_sigma,← Finset.prod_mul_distrib]
  exact RootTensor.sum_sigma_word_product Slots (fun index word =>
    MvPolynomial.C (mass index word)*∏ slot,centeredFactor reference (word slot))

omit [Fintype TaggedSlot] in
/-- A single arbitrary joint kernel is retained inside the entire input
sum; only the local physical output slots are factored. -/
theorem centeredGeneratingLinear_joint_channel (reference : Color → ℝ)
    (channel : (index : Index) → (Input → ℝ) →ₗ[ℝ] ((Slots index → Color) → ℝ))
    (kernel : (Index → Input) → ℝ) :
    centeredGeneratingLinear reference (JointPhysicalChannel.mass Slots channel kernel) =
      ∑ input,MvPolynomial.C (kernel input)*∏ index,
        centeredGeneratingLinear reference (channel index (Pi.single (input index) 1)) := by
  have hm : JointPhysicalChannel.mass Slots channel kernel=
      ∑ input,kernel input • (fun word : Sigma Slots → Color =>
        ∏ index,channel index (Pi.single (input index) 1) (fun slot => word ⟨index,slot⟩)) := by
    funext word
    simp only [JointPhysicalChannel.mass,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [hm,map_sum]
  apply Finset.sum_congr rfl
  intro input _
  rw [map_smul,centeredGeneratingLinear_signed_product]
  rw [Algebra.smul_def,MvPolynomial.algebraMap_eq]

omit [Fintype Input] in
/-- The whole physical complement remains present beside the tagged
joint mass, including its complete generating polynomial. -/
theorem centeredGeneratingLinear_tagged_product (reference : Color → ℝ)
    (tagged : (TaggedSlot → Color) → ℝ)
    (law : (index : Index) → FiniteDist (Slots index → Color)) :
    centeredGeneratingLinear reference (taggedBlockMass Slots tagged law)=
      centeredGeneratingLinear reference tagged*∏ index,centeredGeneratingLinear reference (law index).weight := by
  rw [← centeredGeneratingLinear_product]
  unfold centeredGeneratingLinear taggedBlockMass
  simp only [LinearMap.coe_mk,AddHom.coe_mk,Algebra.smul_def,MvPolynomial.algebraMap_eq,map_mul,Fintype.prod_sum_type]
  have he := (Equiv.sumArrowEquivProdArrow TaggedSlot (Sigma Slots) Color).sum_comp
    (fun point => (MvPolynomial.C (tagged point.1)*∏ slot,centeredFactor reference (point.1 slot))*
      (MvPolynomial.C (blockMass Slots law point.2)*∏ slot,centeredFactor reference (point.2 slot)))
  calc
    _ = ∑ word : TaggedSlot ⊕ Sigma Slots → Color,
        (MvPolynomial.C (tagged (word ∘ Sum.inl))*∏ slot,centeredFactor reference (word (.inl slot)))*
        (MvPolynomial.C (blockMass Slots law (word ∘ Sum.inr))*∏ slot,centeredFactor reference (word (.inr slot))) := by
      apply Finset.sum_congr rfl
      intro word _
      ring
    _ = ∑ point : (TaggedSlot → Color) × (Sigma Slots → Color),
        (MvPolynomial.C (tagged point.1)*∏ slot,centeredFactor reference (point.1 slot))*
        (MvPolynomial.C (blockMass Slots law point.2)*∏ slot,centeredFactor reference (point.2 slot)) := he
    _ = _ := by rw [Fintype.sum_prod_type,Finset.sum_mul_sum]

end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open GaussianSource RepresentedPolynomial HistogramNormalization BlockProducts
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
local instance controlPolynomialFactorizationFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance controlPolynomialFactorizationV7SumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
local instance controlPolynomialFactorizationV7SigmaDecEq {ι : Type*} {fiber : ι → Type*} : DecidableEq (Sigma fiber) := Classical.decEq _

/-- Exact actual conditional response, before either shared-source average.
No independence of a potentially overlapping placement is assumed here. -/
theorem actual_conditional_control_polynomial_factor (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (count : ℕ) (role : Fin count → Bool) (selected : Finset (blockIndex n))
    (placement : ActualTaggedPlacement n count role selected)
    (roots : actualRootWord n) (sample : Window (queueCutoff n) × Equiv.Perm (blockIndex n))
    (kernel : (Fin count → Fin (Parameters.modulus n)) → ℝ) :
    actualConditionalControlPolynomialLinear C n beta charts count role selected placement roots sample kernel=
      (∑ input,MvPolynomial.C (kernel input)*∏ index : Fin count,
        centeredGeneratingLinear (actualReferenceLaw C n beta).weight
          (actualRoleChannel C n beta charts
            (actualRootField n roots (placement.attached index))
            (actualRootField n roots (placement.compensator index))
            (actualQueueShifts n sample (placement.attached index))
            (actualRootField n roots (placement.body index)+actualQueueShifts n sample (placement.body index))
            (role index) (Pi.single (input index) 1)))*
        ∏ index : {index : blockIndex n // index ∉ selected},
          actualBlockConditionalPolynomial C n beta index
            (actualRootField n roots index) (actualQueueShifts n sample index) := by
  change centeredGeneratingLinear (actualReferenceLaw C n beta).weight
    (actualMarkedBlockMass C n beta selected
      (actualJointTaggedOutput C n beta charts count role selected placement kernel roots sample)
      roots (actualQueueShifts n sample)) = _
  rw [actualMarkedBlockMass,centeredGeneratingLinear_tagged_product,
    actualJointTaggedOutput,centeredGeneratingLinear_renamedMass,centeredGeneratingLinear_joint_channel]
  apply congrArg₂ (fun first second : Table (Fin (Parameters.modulus n)) => first*second)
  · rfl
  · apply Finset.prod_congr rfl
    intro index _
    cases index.val <;> rfl

end
end AFT.V7Calibration
