import CurrentAFT.TypedTaggedPhysical
import CurrentAFT.FinitePolynomialTensor
import CurrentAFT.DependentTensorComposition

/-! # Exact removal of unused coordinates in the actual physical PGF

The common safe-control alphabet used for the Fock bounds and the two typed
control alphabets used for calibration define the same joint signed output.
-/
namespace CurrentAFT.TypedRolePolynomial
open AFT AFT.RepresentedPolynomial ActualBlockFock JointTaggedPhysicalFock
  LocalReferenceEnergy ControlCoordinates RaisingPatternBudget TaggedPhysicalFock
  OrdinaryPhysicalFock
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance actualGroupDecidableEq (security : ℕ) :
    DecidableEq (JointTaggedPhysicalFock.Group security) := Classical.decEq _
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw

section Generic
variable {Index : Type*} [Fintype Index] [DecidableEq Index]
  {Input Output : Index → Type*} [∀ index, Fintype (Input index)]

def pullbackLinear {First Second : Type*} (projection : Second → First) :
    (First → ℝ) →ₗ[ℝ] (Second → ℝ) where
  toFun score output := score (projection output)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A joint kernel pulled back along all local coordinate maps is still the
same joint kernel evaluated on the complete projected word. -/
theorem apply_pullback (projection : ∀ index, Output index → Input index)
    (kernel : ((index : Index) → Input index) → ℝ) (output : ∀ index, Output index) :
    DependentTensorChannel.apply (fun index => pullbackLinear (projection index)) kernel output =
      kernel (fun index => projection index (output index)) := by
  unfold DependentTensorChannel.apply
  rw [Finset.sum_eq_single (fun index => projection index (output index))]
  · simp only [pullbackLinear, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_eq_same,
      Finset.prod_const_one, mul_one]
  · intro source _ hsource
    have hsome : ∃ index, source index ≠ projection index (output index) := by
      by_contra hnone
      apply hsource
      funext index
      exact not_not.mp (not_exists.mp hnone index)
    obtain ⟨index, hindex⟩ := hsome
    have hzero : pullbackLinear (projection index) (Pi.single (source index) 1) (output index) = 0 :=
      Pi.single_eq_of_ne (Ne.symm hindex) 1
    rw [Finset.prod_eq_zero (Finset.mem_univ index) hzero, mul_zero]
  · simp

end Generic

abbrev Palette (security : ℕ) := ActualControls.Palette security

def roleProjection (security r s : ℕ) :
    (role : Role r s) → JointTaggedPhysicalFock.Group security → RoleInput security r s role
  | .inl _, group => group.1
  | .inr _, group => group.2

def lift (security r s : ℕ) (role : Role r s) :
    (RoleInput security r s role → ℝ) →ₗ[ℝ] (JointTaggedPhysicalFock.Group security → ℝ) :=
  pullbackLinear (roleProjection security r s role)

def reduce (security r s : ℕ) :
    (role : Role r s) → (JointTaggedPhysicalFock.Group security → ℝ) →ₗ[ℝ] (RoleInput security r s role → ℝ)
  | .inl _ => reducePrimary (ActualControls.bodyReference security)
  | .inr _ => reduceBody (ProposalPrimary.primaryLaw security)

theorem reduce_lift (security r s : ℕ) (role : Role r s) :
    (reduce security r s role).comp (lift security r s role) = LinearMap.id := by
  apply LinearMap.ext
  intro score
  funext output
  cases role
  · change (ActualControls.bodyReference security).expectation (fun _ => score output) = score output
    exact FiniteDist.expectation_const _ _
  · change (ProposalPrimary.primaryLaw security).expectation (fun _ => score output) = score output
    exact FiniteDist.expectation_const _ _

def typedKernel (security : ℕ) {r s : ℕ}
    (kernel : DensityKernel (Primary := Palette security) (Body := ActualControls.SafePalette security) r s)
    (word : (role : Role r s) → RoleInput security r s role) : ℝ :=
  kernel (fun index => word (.inl index)) (fun index => word (.inr index))

theorem typedKernel_eq_inputJoint (security : ℕ) {r s : ℕ}
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s) :
    typedKernel security kernel.val = RaisingPatternKernel.inputJoint security kernel := rfl

theorem unpaired_eq_tensor (security r s : ℕ)
    (kernel : DensityKernel (Primary := Palette security) (Body := ActualControls.SafePalette security) r s) :
    DependentTensorChannel.apply (lift security r s) (typedKernel security kernel) =
      unpairedKernel kernel := by
  funext word
  rw [show lift security r s = fun role => pullbackLinear (roleProjection security r s role) from rfl,
    apply_pullback]
  rfl

theorem reduced_unpaired (security r s : ℕ)
    (kernel : DensityKernel (Primary := Palette security) (Body := ActualControls.SafePalette security) r s) :
    DependentTensorChannel.apply (reduce security r s) (unpairedKernel kernel) =
      typedKernel security kernel := by
  rw [← unpaired_eq_tensor security r s kernel, ← DependentTensorComposition.apply_comp]
  have hchannels : (fun role => (reduce security r s role).comp (lift security r s role)) =
      fun role => pullbackLinear (fun value : RoleInput security r s role => value) := by
    funext role
    rw [reduce_lift]
    rfl
  rw [hchannels]
  funext word
  exact apply_pullback _ _ _

def raw (security r s : ℕ) (compensator attachment : Fin r → ℤ) (body : Fin s → ℤ) :
    (role : Role r s) → (RoleInput security r s role → ℝ) →ₗ[ℝ] MvPolynomial (Palette security) ℝ
  | .inl index => (centeredGeneratingLinear (uniformReference security).weight).comp
      (averagedPairedChannel security (compensator index) (attachment index))
  | .inr index => (centeredGeneratingLinear (uniformReference security).weight).comp
      (bodyChannel security (body index))

def common (security r s : ℕ) (compensator attachment : Fin r → ℤ) (body : Fin s → ℤ)
    (role : Role r s) : (JointTaggedPhysicalFock.Group security → ℝ) →ₗ[ℝ] MvPolynomial (Palette security) ℝ :=
  (raw security r s compensator attachment body role).comp (reduce security r s role)

theorem common_apply (security r s : ℕ) (compensator attachment : Fin r → ℤ) (body : Fin s → ℤ)
    (role : Role r s) (score : JointTaggedPhysicalFock.Group security → ℝ) :
    common security r s compensator attachment body role score =
      centeredGeneratingLinear (uniformReference security).weight
        (roleChannel security r s compensator attachment body role score) := by
  cases role <;> rfl

/-- Independent unused control coordinates integrate out as coefficient
data before any physical generating polynomial is evaluated. -/
theorem common_synthesis_eq_typed (security r s : ℕ) (compensator attachment : Fin r → ℤ)
    (body : Fin s → ℤ)
    (kernel : DensityKernel (Primary := Palette security) (Body := ActualControls.SafePalette security) r s) :
    FinitePolynomialTensor.synthesis (common security r s compensator attachment body) (unpairedKernel kernel) =
      FinitePolynomialTensor.synthesis (raw security r s compensator attachment body)
        (typedKernel security kernel) := by
  rw [show common security r s compensator attachment body =
      fun role => (raw security r s compensator attachment body role).comp (reduce security r s role) from rfl,
    FinitePolynomialTensor.synthesis_comp, reduced_unpaired]

theorem jointMass_generating_eq_typed (security r s : ℕ) (compensator attachment : Fin r → ℤ)
    (body : Fin s → ℤ)
    (kernel : DensityKernel (Primary := Palette security) (Body := ActualControls.SafePalette security) r s) :
    centeredGeneratingLinear (uniformReference security).weight
      (jointMass security r s compensator attachment body kernel) =
      FinitePolynomialTensor.synthesis (raw security r s compensator attachment body)
        (typedKernel security kernel) := by
  rw [← common_synthesis_eq_typed security r s compensator attachment body kernel,
    TypedTaggedPhysical.jointMass_generating]
  unfold FinitePolynomialTensor.synthesis
  rw [← (Equiv.piCongrLeft (fun _ : Fin (r + s) => JointTaggedPhysicalFock.Group security)
    (finSumFinEquiv : Role r s ≃ Fin (r + s))).sum_comp]
  apply Finset.sum_congr rfl
  intro input _
  have hkernel : finiteKernel kernel
      (Equiv.piCongrLeft (fun _ : Fin (r + s) => JointTaggedPhysicalFock.Group security) finSumFinEquiv input) =
      unpairedKernel kernel input := by
    unfold finiteKernel
    congr 1
    funext role
    exact Equiv.piCongrLeft_apply_apply (fun _ : Fin (r + s) => JointTaggedPhysicalFock.Group security)
      finSumFinEquiv input role
  rw [hkernel]
  congr 1
  rw [← finSumFinEquiv.prod_comp]
  apply Finset.prod_congr rfl
  intro role _
  simp only [physicalChannel, Equiv.piCongrLeft_apply_apply, common_apply]
  exact congrArg (fun other : Role r s => centeredGeneratingLinear (uniformReference security).weight
    (roleChannel security r s compensator attachment body other (Pi.single (input role) 1)))
      ((finSumFinEquiv : Role r s ≃ Fin (r + s)).symm_apply_apply role)

end
end CurrentAFT.TypedRolePolynomial
