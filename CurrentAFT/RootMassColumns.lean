import CurrentAFT.RootUnselectedBlockChannel
import CurrentAFT.RootPrimaryGroupedChannel
import CurrentAFT.RootOrdinaryGroupedChannel
import CurrentAFT.RootSignedMassProgram

/-! # Actual fixed-root mass columns without division by root atoms

The root reference is only a multiplier. The formulas below remain valid
at zero atoms. They expose the finite, fixed-root experiments that a
rational matrix-entry program evaluates before root averaging.
-/
namespace CurrentAFT.RootMassColumns

open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion
  LocalReferenceEnergy FirstHistogram ControlCoordinates GradedControlAlgebra
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw bodyReference rootReference
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

section Fiber
variable {Root Control Output : Type*} [Fintype Root]
  [AddCommMonoid Output] [Module ℝ Output]

def fiber (root : Root) (score : Control → ℝ) : Root → Control → ℝ :=
  fun other => if other = root then score else 0

theorem weighted_fiber (reference : FiniteDist Root)
    (channel : Root → (Control → ℝ) →ₗ[ℝ] Output)
    (root : Root) (score : Control → ℝ) :
    (∑ other, reference.weight other • channel other (fiber root score other)) =
      reference.weight root • channel root score := by
  classical
  calc
    _ = reference.weight root • channel root (fiber root score root) :=
      Finset.sum_eq_single root (fun other _ hne => by
        simp only [fiber, if_neg hne, map_zero, smul_zero]) (by simp)
    _ = _ := by simp [fiber]

end Fiber

/-- The real same-scalar paired experiment at two fixed roots. -/
def primaryMassAt (security : ℕ) (roots : RootTaggedSelected.RootPair security) :
    (ActualControls.Palette security → ℝ) →ₗ[ℝ]
      ((Fin 4 → ActualControls.Palette security) → ℝ) :=
  ∑ scalar : FirstHistogram.Scalar security, (scalarLaw security).weight scalar •
    PairedReferenceEnergy.pairedMassLinear security (roots.1.val : ℤ) (roots.2.val : ℤ) scalar

theorem primary_mass_average (security : ℕ)
    (score : RootTaggedSelected.RootPair security → ActualControls.Palette security → ℝ) :
    RootTaggedSelected.massLinear security score =
      ∑ roots, (RootTaggedSelected.rootsLaw security).weight roots •
        primaryMassAt security roots (score roots) := by
  funext word
  simp only [RootTaggedSelected.massLinear, RootTaggedSelected.sourceLaw, primaryMassAt,
    LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, FiniteDist.prod_weight, Fintype.sum_prod_type,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro roots _
  apply Finset.sum_congr rfl
  intro scalar _
  simp only [mul_assoc]

theorem primary_mass_fiber (security : ℕ) (roots : RootTaggedSelected.RootPair security)
    (score : ActualControls.Palette security → ℝ) :
    RootTaggedSelected.massLinear security (fiber roots score) =
      (RootTaggedSelected.rootsLaw security).weight roots • primaryMassAt security roots score := by
  rw [primary_mass_average]
  exact weighted_fiber _ (primaryMassAt security) roots score

/-- The full primary coefficient lift still has this root-mass factor.
The finite reciprocal is the actual one used by the full response. -/
def primaryResponseAt (security order : ℕ) (roots : RootTaggedSelected.RootPair security)
    (score : ActualControls.Palette security → ℝ) : LocalCoefficientFamily.Family security order :=
  LocalRaisingLinear.completeFamilyLinear security order (primaryMassAt security roots score) *
    LocalRaisingBounds.positiveInverse security order

theorem primary_response_fiber (security order : ℕ) (roots : RootTaggedSelected.RootPair security)
    (score : ActualControls.Palette security → ℝ) :
    RootTaggedSelectedChannel.responseLinear security order (fiber roots score) =
      (RootTaggedSelected.rootsLaw security).weight roots • primaryResponseAt security order roots score := by
  change LocalRaisingLinear.completeFamilyLinear security order
    (RootTaggedSelected.massLinear security (fiber roots score)) * _ = _
  rw [primary_mass_fiber, map_smul, smul_mul_assoc]
  rfl

theorem primary_roots_weight (security : ℕ) (roots : RootTaggedSelected.RootPair security) :
    (RootTaggedSelected.rootsLaw security).weight roots =
      (rootReference security).weight roots.1 * (rootReference security).weight roots.2 := rfl

/-- The actual safe-control push at one fixed ordinary root. -/
def ordinaryMassAt (security : ℕ) (root : CycleRootExpansion.Root security) :
    (SafePalette security → ℝ) →ₗ[ℝ] (ActualControls.Palette security → ℝ) :=
  SelectedOrdinaryRoot.pushLinear (bodyReference security) (SelectedOrdinaryRoot.rootEmbedding security root)

theorem ordinary_mass_fiber (security : ℕ) (root : CycleRootExpansion.Root security)
    (score : SafePalette security → ℝ) :
    SelectedOrdinaryRoot.rawMassLinear security (fun sample => fiber root score sample.1 sample.2) =
      (rootReference security).weight root • ordinaryMassAt security root score := by
  change (∑ other, (rootReference security).weight other •
    (SelectedOrdinaryRoot.pushLinear (bodyReference security) (SelectedOrdinaryRoot.rootEmbedding security other)).comp
      (SelectedOrdinaryRoot.sliceLinear security other)) (fun sample => fiber root score sample.1 sample.2) = _
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  change (∑ other, (rootReference security).weight other • ordinaryMassAt security other
    (fiber root score other)) = _
  exact weighted_fiber _ (ordinaryMassAt security) root score

theorem singleton_mass_column (security : ℕ) (role : UniformBodyProfiles.BodyRole) (queue : ℤ)
    (root : CycleRootExpansion.Root security) :
    RootTaggedLocal.rootMass security role queue (Pi.single root 1) =
      (rootReference security).weight root • RootTaggedLocal.deviationProfile security role queue root := by
  funext color
  simp [RootTaggedLocal.rootMass, Pi.single_apply]

theorem leg_raw_mass_column (security : ℕ) (root : CycleRootExpansion.Root security) :
    RootTaggedLegHigher.rawMassLinear security (Pi.single root 1) =
      (rootReference security).weight root • (ActualBlockFock.primaryLawAt security root.val).weight := by
  funext word
  simp [RootTaggedLegHigher.rawMassLinear, Pi.single_apply]

theorem leg_mass_column (security : ℕ) (root : CycleRootExpansion.Root security) :
    RootTaggedLegHigher.massLinear security (Pi.single root 1) =
      (rootReference security).weight root •
        ((ActualBlockFock.primaryLawAt security root.val).weight -
          RootTaggedLegHigher.rawMassLinear security (fun _ => 1)) := by
  have hcenter : TensorChannel.center (rootReference security) (Pi.single root 1) =
      Pi.single root 1 - (rootReference security).weight root • (fun _ => (1 : ℝ)) := by
    funext other
    simp only [TensorChannel.center_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one]
    congr 1
    simp [FiniteDist.expectation, Pi.single_apply]
  rw [RootTaggedLegHigher.massLinear, LinearMap.comp_apply, hcenter, map_sub, map_smul,
    leg_raw_mass_column, smul_sub]

theorem primary_massAt_formula (security : ℕ) (roots : RootTaggedSelected.RootPair security)
    (score : ActualControls.Palette security → ℝ) (word : Fin 4 → ActualControls.Palette security) :
    primaryMassAt security roots score word =
      ∑ scalar : FirstHistogram.Scalar security, (scalarLaw security).weight scalar *
        ∑ group : PhysicalSynthesis.Group security,
          (PhysicalSynthesis.groupLaw security).weight group *
            PhysicalSynthesis.pairedChannel security score group *
              PairedReferenceEnergy.controlMass security (roots.1.val : ℤ) (roots.2.val : ℤ) scalar group word := by
  simp only [primaryMassAt, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, PairedReferenceEnergy.pairedMassLinear, LinearMap.coe_mk, AddHom.coe_mk]

end
end CurrentAFT.RootMassColumns
