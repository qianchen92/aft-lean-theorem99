import CurrentAFT.GroupedFamilyIdentity
import CurrentAFT.DependentTensorComposition

/-! # Exact preprocessing of joint family-valued tensor inputs -/
namespace CurrentAFT.GroupedFamilyComposition
open AFT ControlCoordinates ControlProduct GradedControlAlgebra GroupedFamilyTensor
  GroupedKernelNorm
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} :
    DecidableEq (Sigma Slots) := Classical.decEq _

variable {Primary Body Group : Type*} [Fintype Primary] [Fintype Body] [Fintype Group]
  (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
  {Input Middle : Group → Type*}
  [∀ group, Fintype (Input group)] [∀ group, Fintype (Middle group)]
  (preprocess : ∀ group, (Input group → ℝ) →ₗ[ℝ] (Middle group → ℝ))
  (channels : ∀ group, (Middle group → ℝ) →ₗ[ℝ] KernelFamily primary body order)

theorem patternKernel_comp (pattern : Group → TruncatedArity order)
    (input : ((group : Group) → Input group) → ℝ) :
    patternKernel primary body order (fun group => (channels group).comp (preprocess group)) pattern input =
      patternKernel primary body order channels pattern (DependentTensorChannel.apply preprocess input) := by
  apply Subtype.ext
  change canonicalize _ _ _ _
    (DependentTensorChannel.apply
      (componentChannel primary body order (fun group => (channels group).comp (preprocess group)) pattern) input) =
    canonicalize _ _ _ _ (DependentTensorChannel.apply
      (componentChannel primary body order channels pattern) (DependentTensorChannel.apply preprocess input))
  congr 1
  have hchannel : componentChannel primary body order
      (fun group => (channels group).comp (preprocess group)) pattern =
      fun group => (componentChannel primary body order channels pattern group).comp (preprocess group) := rfl
  rw [hchannel, DependentTensorComposition.apply_comp]

theorem patternFamily_comp (pattern : Group → TruncatedArity order)
    (input : ((group : Group) → Input group) → ℝ) :
    patternFamily primary body order (fun group => (channels group).comp (preprocess group)) pattern input =
      patternFamily primary body order channels pattern (DependentTensorChannel.apply preprocess input) := by
  unfold patternFamily
  split_ifs
  · rw [patternKernel_comp]
  · rfl

/-- Coordinate preprocessing acts on the whole joint input before any
canonicalization or arity truncation. -/
theorem response_comp (input : ((group : Group) → Input group) → ℝ) :
    response primary body order (fun group => (channels group).comp (preprocess group)) input =
      response primary body order channels (DependentTensorChannel.apply preprocess input) := by
  unfold response
  simp_rw [patternFamily_comp]

/-- The actual tensor response is linear in the entire joint input. -/
def responseLinear : (((group : Group) → Middle group) → ℝ) →ₗ[ℝ] KernelFamily primary body order where
  toFun := response primary body order channels
  map_add' first second := by
    simp only [GroupedFamilyIdentity.response_eq, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' scalar input := by
    simp only [GroupedFamilyIdentity.response_eq, Pi.smul_apply, smul_eq_mul, mul_smul,
      Finset.smul_sum, RingHom.id_apply]

end
end CurrentAFT.GroupedFamilyComposition
