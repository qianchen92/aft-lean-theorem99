import CurrentAFT.GroupedKernelNorm

/-! # Exact linear finite-sum formula for the mixed grouped tensor bundle -/
namespace CurrentAFT.GroupedKernelNorm
open AFT ControlCoordinates ControlProduct ControlNorm
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
local instance linearSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} :
    DecidableEq (Sigma Slots) := Classical.decEq _

variable {Group Primary Body : Type*} [Fintype Group] [Fintype Primary] [Fintype Body]
  (PrimarySlots BodySlots : Group → Type*)
  [∀ group, Fintype (PrimarySlots group)] [∀ group, Fintype (BodySlots group)]
  {PrimaryTarget BodyTarget : Type*} [Fintype PrimaryTarget] [Fintype BodyTarget]

def canonicalizeLinear (primaryEquiv : Sigma PrimarySlots ≃ PrimaryTarget)
    (bodyEquiv : Sigma BodySlots ≃ BodyTarget) :
    (GroupWord (Primary := Primary) (Body := Body) PrimarySlots BodySlots → ℝ) →ₗ[ℝ]
      Kernel (Primary := Primary) (Body := Body) PrimaryTarget BodyTarget where
  toFun := canonicalize PrimarySlots BodySlots primaryEquiv bodyEquiv
  map_add' first second := by
    change symmetrizeLinear _ = symmetrizeLinear _ + symmetrizeLinear _
    rw [← map_add]
    rfl
  map_smul' scalar kernel := by
    change symmetrizeLinear _ = scalar • symmetrizeLinear _
    rw [← map_smul]
    rfl

variable {Input : Group → Type*} [∀ group, Fintype (Input group)]

omit [Fintype Primary] [Fintype Body] [∀ group, Fintype (PrimarySlots group)]
  [∀ group, Fintype (BodySlots group)] in
/-- Exact source-matrix expansion of the same joint tensor used for the
Hilbert estimate. No norm triangle is taken over these source coordinates. -/
theorem canonicalize_tensor_formula
    (primaryEquiv : Sigma PrimarySlots ≃ PrimaryTarget) (bodyEquiv : Sigma BodySlots ≃ BodyTarget)
    (channel : ∀ group, (Input group → ℝ) →ₗ[ℝ]
      (((PrimarySlots group → Primary) × (BodySlots group → Body)) → ℝ))
    (kernel : ((group : Group) → Input group) → ℝ) :
    canonicalize PrimarySlots BodySlots primaryEquiv bodyEquiv
        (DependentTensorChannel.apply channel kernel) =
      ∑ input, kernel input • canonicalize PrimarySlots BodySlots primaryEquiv bodyEquiv
        (fun word => ∏ group, channel group (Pi.single (input group) 1) (word group)) := by
  have hequal : DependentTensorChannel.apply channel kernel =
      ∑ input, kernel input • (fun word => ∏ group, channel group (Pi.single (input group) 1) (word group)) := by
    funext word
    simp only [DependentTensorChannel.apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change canonicalizeLinear PrimarySlots BodySlots primaryEquiv bodyEquiv _ = _
  rw [hequal, map_sum]
  simp only [map_smul]
  rfl

end
end CurrentAFT.GroupedKernelNorm
