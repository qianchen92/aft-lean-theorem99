import CurrentAFT.ControlNorm
import AFT.DependentTensorChannel

/-!
# Mixed-alphabet grouped joint kernels and exact flattening

The entire joint function is retained through the coordinate equivalence.
Reindexing is isometric and the genuine separate symmetrization contracts;
neither operation introduces a color-alphabet or tensor-rank factor.
-/

namespace CurrentAFT.GroupedKernelNorm

open AFT ControlCoordinates ControlProduct ControlNorm
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} :
    DecidableEq (Sigma Slots) := Classical.decEq _

variable {Group Primary Body : Type*} [Fintype Group] [Fintype Primary] [Fintype Body]
  (PrimarySlots BodySlots : Group → Type*)
  [∀ group, Fintype (PrimarySlots group)] [∀ group, Fintype (BodySlots group)]

abbrev GroupWord := (group : Group) →
  ((PrimarySlots group → Primary) × (BodySlots group → Body))

def wordEquiv :
    ((Sigma PrimarySlots → Primary) × (Sigma BodySlots → Body)) ≃
      GroupWord (Primary := Primary) (Body := Body) PrimarySlots BodySlots where
  toFun word group := (fun slot => word.1 ⟨group, slot⟩, fun slot => word.2 ⟨group, slot⟩)
  invFun word := (fun slot => (word slot.1).1 slot.2, fun slot => (word slot.1).2 slot.2)
  left_inv word := by cases word; rfl
  right_inv word := by rfl

def localReference (primary : FiniteDist Primary) (body : FiniteDist Body) (group : Group) :
    FiniteDist ((PrimarySlots group → Primary) × (BodySlots group → Body)) :=
  (FiniteDist.independent (fun _ : PrimarySlots group => primary)).prod
    (FiniteDist.independent (fun _ : BodySlots group => body))

def flatten (kernel : GroupWord (Primary := Primary) (Body := Body) PrimarySlots BodySlots → ℝ) :
    Kernel (Primary := Primary) (Body := Body) (Sigma PrimarySlots) (Sigma BodySlots) :=
  fun colors centers => kernel (wordEquiv PrimarySlots BodySlots (colors, centers))

/-- Genuine finite Fubini for both output alphabets at once, on an
arbitrary joint function of all grouped outputs. -/
theorem flatten_energy (primary : FiniteDist Primary) (body : FiniteDist Body)
    (kernel : GroupWord (Primary := Primary) (Body := Body) PrimarySlots BodySlots → ℝ) :
    blockEnergy primary body (flatten PrimarySlots BodySlots kernel) =
      (FiniteDist.dependentIndependent (localReference PrimarySlots BodySlots primary body)).l2Sq kernel := by
  unfold blockEnergy FiniteDist.l2Sq FiniteDist.expectation
  rw [← (wordEquiv (Primary := Primary) (Body := Body) PrimarySlots BodySlots).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro word _
  simp only [FiniteDist.prod_weight, FiniteDist.independent, wordEquiv, Equiv.coe_fn_symm_mk,
    flatten, Equiv.coe_fn_mk, FiniteDist.dependentIndependent_weight,
    localReference, Fintype.prod_sigma]
  rw [Finset.prod_mul_distrib]

theorem flatten_l2 (primary : FiniteDist Primary) (body : FiniteDist Body)
    (kernel : GroupWord (Primary := Primary) (Body := Body) PrimarySlots BodySlots → ℝ) :
    blockL2 primary body (flatten PrimarySlots BodySlots kernel) =
      Real.sqrt ((FiniteDist.dependentIndependent (localReference PrimarySlots BodySlots primary body)).l2Sq kernel) := by
  rw [blockL2, flatten_energy]

variable {PrimaryTarget BodyTarget : Type*} [Fintype PrimaryTarget] [Fintype BodyTarget]

def canonicalize (primaryEquiv : Sigma PrimarySlots ≃ PrimaryTarget)
    (bodyEquiv : Sigma BodySlots ≃ BodyTarget)
    (kernel : GroupWord (Primary := Primary) (Body := Body) PrimarySlots BodySlots → ℝ) :
    Kernel (Primary := Primary) (Body := Body) PrimaryTarget BodyTarget :=
  symmetrize (reindexKernel primaryEquiv bodyEquiv (flatten PrimarySlots BodySlots kernel))

/-- The complete joint output can be numbered and symmetrized with
operator norm one, independently of both alphabet sizes and all ranks. -/
theorem canonicalize_energy_le (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryEquiv : Sigma PrimarySlots ≃ PrimaryTarget) (bodyEquiv : Sigma BodySlots ≃ BodyTarget)
    (kernel : GroupWord (Primary := Primary) (Body := Body) PrimarySlots BodySlots → ℝ) :
    blockEnergy primary body (canonicalize PrimarySlots BodySlots primaryEquiv bodyEquiv kernel) ≤
      (FiniteDist.dependentIndependent (localReference PrimarySlots BodySlots primary body)).l2Sq kernel := by
  apply (blockEnergy_symmetrize_le primary body _).trans_eq
  rw [blockEnergy_reindex, flatten_energy]

theorem canonicalize_l2_le (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryEquiv : Sigma PrimarySlots ≃ PrimaryTarget) (bodyEquiv : Sigma BodySlots ≃ BodyTarget)
    (kernel : GroupWord (Primary := Primary) (Body := Body) PrimarySlots BodySlots → ℝ) :
    blockL2 primary body (canonicalize PrimarySlots BodySlots primaryEquiv bodyEquiv kernel) ≤
      Real.sqrt ((FiniteDist.dependentIndependent (localReference PrimarySlots BodySlots primary body)).l2Sq kernel) :=
  Real.sqrt_le_sqrt (canonicalize_energy_le PrimarySlots BodySlots primary body primaryEquiv bodyEquiv kernel)

variable {Input : Group → Type*} [∀ group, Fintype (Input group)]

/-- Tensorization followed by actual mixed flattening and symmetrization,
for arbitrary joint input kernels and different local input alphabets. -/
theorem canonicalize_tensor_energy_le (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryEquiv : Sigma PrimarySlots ≃ PrimaryTarget) (bodyEquiv : Sigma BodySlots ≃ BodyTarget)
    (input : ∀ group, FiniteDist (Input group))
    (channel : ∀ group, (Input group → ℝ) →ₗ[ℝ]
      (((PrimarySlots group → Primary) × (BodySlots group → Body)) → ℝ))
    (bound : Group → ℝ)
    (hchannel : ∀ group score,
      (localReference PrimarySlots BodySlots primary body group).l2Sq (channel group score) ≤
        bound group ^ 2 * (input group).l2Sq score)
    (kernel : ((group : Group) → Input group) → ℝ) :
    blockEnergy primary body (canonicalize PrimarySlots BodySlots primaryEquiv bodyEquiv
      (DependentTensorChannel.apply channel kernel)) ≤
      (∏ group, bound group ^ 2) * (FiniteDist.dependentIndependent input).l2Sq kernel :=
  (canonicalize_energy_le PrimarySlots BodySlots primary body primaryEquiv bodyEquiv _).trans
    (DependentTensorChannel.energy_le input _ channel bound hchannel kernel)

end
end CurrentAFT.GroupedKernelNorm
