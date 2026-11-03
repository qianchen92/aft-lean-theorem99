import CurrentAFT.RootTaggedFamilies
import CurrentAFT.GroupedKernelCanonical
import CurrentAFT.GroupedKernelProduct

/-! # Joint singleton root channels and the sharp actual population budget -/
namespace CurrentAFT.RootSingletonTensor
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct ControlNorm
  GradedControlAlgebra GradedControlNorm BackgroundFamilies BackgroundRates CycleRootExpansion
  RootTaggedLocal RootTaggedFamilies UniformBodyProfiles GroupedKernelNorm GroupedKernelProduct
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} :
    DecidableEq (Sigma Slots) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize primaryLaw bodyReference rootReference

def primaryEquiv (count : ℕ) : Sigma (fun _ : Fin count => Fin 1) ≃ Fin count where
  toFun := Sigma.fst
  invFun index := ⟨index, 0⟩
  left_inv := by
    rintro ⟨index, slot⟩
    have hequal : slot = 0 := Subsingleton.elim _ _
    subst slot
    rfl
  right_inv _ := rfl

def bodyEquiv (count : ℕ) : Sigma (fun _ : Fin count => Fin 0) ≃ Fin 0 := by
  letI : IsEmpty (Sigma (fun _ : Fin count => Fin 0)) := ⟨fun index => Fin.elim0 index.snd⟩
  exact Equiv.equivOfIsEmpty _ _

def channel (security : ℕ) (role : BodyRole) (queue : ℤ) :
    (Root security → ℝ) →ₗ[ℝ] (((Fin 1 → ActualControls.Palette security) × (Fin 0 → SafePalette security)) → ℝ) where
  toFun input output := (rootKernelLinear security role queue input).val output.1 output.2
  map_add' first second := by
    funext output
    exact congrArg (fun kernel : canonicalKernels (primaryLaw security) (bodyReference security) 1 0 =>
      kernel.val output.1 output.2) ((rootKernelLinear security role queue).map_add first second)
  map_smul' scalar input := by
    funext output
    exact congrArg (fun kernel : canonicalKernels (primaryLaw security) (bodyReference security) 1 0 =>
      kernel.val output.1 output.2) ((rootKernelLinear security role queue).map_smul scalar input)

theorem channel_energy (security count : ℕ) (role : BodyRole) (queue : ℤ)
    (index : Fin count) (input : Root security → ℝ) :
    (localReference (fun _ : Fin count => Fin 1) (fun _ : Fin count => Fin 0)
      (primaryLaw security) (bodyReference security) index).l2Sq (channel security role queue input) ≤
      rootCost security ^ 2 * (rootReference security).l2Sq input := by
  change blockEnergy (primaryLaw security) (bodyReference security)
    (primaryKernel (primaryLaw security) (bodyReference security)
      (rootLift security role queue input) (rootLift_mean security role queue input)).val ≤ _
  rw [← blockL2_sq, primaryKernel_blockL2]
  change Real.sqrt ((primaryLaw security).l2Sq (rootLift security role queue input)) ^ 2 ≤ _
  rw [Real.sq_sqrt ((primaryLaw security).l2Sq_nonneg _)]
  exact rootLift_energy_le_cost security role queue input

def tensorKernel (security count : ℕ) (roles : Fin count → BodyRole) (queues : Fin count → ℤ)
    (input : (Fin count → Root security) → ℝ) :
    canonicalKernels (primaryLaw security) (bodyReference security) count 0 :=
  canonicalTensor (fun _ : Fin count => Fin 1) (fun _ : Fin count => Fin 0)
    (primaryLaw security) (bodyReference security) (primaryEquiv count) (bodyEquiv count)
    (fun index => channel security (roles index) (queues index))
    (fun index score => (rootKernelLinear security (roles index) (queues index) score).property.1)
    (fun index score => (rootKernelLinear security (roles index) (queues index) score).property.2.1) input

theorem tensorKernel_energy (security count : ℕ) (roles : Fin count → BodyRole) (queues : Fin count → ℤ)
    (input : (Fin count → Root security) → ℝ) :
    blockEnergy (primaryLaw security) (bodyReference security) (tensorKernel security count roles queues input).val ≤
      (rootCost security ^ count) ^ 2 *
        (FiniteDist.independent (fun _ : Fin count => rootReference security)).l2Sq input := by
  have h := canonicalize_tensor_energy_le (fun _ : Fin count => Fin 1) (fun _ : Fin count => Fin 0)
    (primaryLaw security) (bodyReference security) (primaryEquiv count) (bodyEquiv count)
    (fun _ => rootReference security) (fun index => channel security (roles index) (queues index))
    (fun _ => rootCost security) (fun index => channel_energy security count (roles index) (queues index) index) input
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, Nat.mul_comm] using h

theorem tensorKernel_norm (security count : ℕ) (roles : Fin count → BodyRole) (queues : Fin count → ℤ)
    (input : (Fin count → Root security) → ℝ) :
    blockL2 (primaryLaw security) (bodyReference security) (tensorKernel security count roles queues input).val ≤
      rootCost security ^ count * Real.sqrt
        ((FiniteDist.independent (fun _ : Fin count => rootReference security)).l2Sq input) := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg (pow_nonneg (rootCost_nonneg security) _) (Real.sqrt_nonneg _), ?_⟩
  rw [mul_pow, Real.sq_sqrt (FiniteDist.l2Sq_nonneg _ input)]
  exact tensorKernel_energy security count roles queues input

def tensorFamily (security order count : ℕ) (hcount : count ≤ order)
    (roles : Fin count → BodyRole) (queues : Fin count → ℤ)
    (input : (Fin count → Root security) → ℝ) : ActualFamily security order :=
  embed (primaryLaw security) (bodyReference security) order (by omega)
    (tensorKernel security count roles queues input)

theorem tensorFamily_norm (security order count : ℕ) (hcount : count ≤ order)
    (roles : Fin count → BodyRole) (queues : Fin count → ℤ)
    (input : (Fin count → Root security) → ℝ) :
    familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
      (tensorFamily security order count hcount roles queues input) ≤
        (primaryFactor security * rootCost security) ^ count *
          Real.sqrt ((FiniteDist.independent (fun _ : Fin count => rootReference security)).l2Sq input) := by
  rw [tensorFamily, embed, familyNorm_single]
  change primaryFactor security ^ count * bodyFactor security ^ 0 * _ ≤ _
  rw [pow_zero, mul_one, mul_pow, mul_assoc]
  exact mul_le_mul_of_nonneg_left (tensorKernel_norm security count roles queues input)
    (pow_nonneg (by unfold primaryFactor; positivity) _)

end
end CurrentAFT.RootSingletonTensor
