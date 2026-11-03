import CurrentAFT.PhysicalPolynomialAverages

/-! # The literal coefficient-family output PGF -/
namespace CurrentAFT.ActualFamilyPolynomial
open AFT AFT.RepresentedPolynomial PhysicalPolynomialAverages CoefficientOutputFock
  UniformTaggedOutput ActualFockBound ConditionalHistogramMean ActualCycleMeanMGF
  LocalReferenceEnergy CycleRootExpansion
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance finDecEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

theorem baseline_generating (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security)) :
    centeredGeneratingLinear (uniformReference security).weight
      (baselineMass security layout queue permutation) =
    centeredGeneratingLinear (uniformReference security).weight
      (outputLaw security layout queue permutation).weight :=
  generating_renamed _ _ _

theorem uniform_generating (security r s : ℕ) (hprimary : r ≤ Parameters.legCount security)
    (hbody : s ≤ BackgroundRates.ordinaryPool security)
    (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security))
    (kernel : ControlCoordinates.DensityKernel
      (Primary := ActualControls.Palette security) (Body := ActualControls.SafePalette security) r s) :
    centeredGeneratingLinear (uniformReference security).weight
      (uMass security r s hprimary hbody layout queue permutation kernel) =
      ∑ choice : Choice security r s, (choiceLaw security r s hprimary hbody).weight choice •
        centeredGeneratingLinear (uniformReference security).weight
          (TaggedOutputFock.outputMass security r s (selection security r s choice)
            layout queue permutation kernel) := by
  unfold uMass
  rw [generating_average]
  simp_rw [flatMass, generating_renamed]

theorem family_generating (security order : ℕ) (hroom : 2 * order ≤ security)
    (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security))
    (coefficient : ActualControls.Coefficients security order) :
    centeredGeneratingLinear (uniformReference security).weight
      (familyMass security order hroom layout queue permutation coefficient) =
      coefficient.1 • centeredGeneratingLinear (uniformReference security).weight
        (outputLaw security layout queue permutation).weight +
      ∑ arity : ControlCoordinates.PositiveArity order,
        ∑ choice : Choice security arity.val.1.val arity.val.2.val,
          (choiceLaw security arity.val.1.val arity.val.2.val
            (primary_room security order hroom arity) (body_room security order hroom arity)).weight choice •
          centeredGeneratingLinear (uniformReference security).weight
            (TaggedOutputFock.outputMass security arity.val.1.val arity.val.2.val
              (selection security arity.val.1.val arity.val.2.val choice) layout queue permutation
              (coefficient.2 arity).val) := by
  have hmass : familyMass security order hroom layout queue permutation coefficient =
      coefficient.1 • baselineMass security layout queue permutation +
        ∑ arity : ControlCoordinates.PositiveArity order,
          uMass security arity.val.1.val arity.val.2.val
            (primary_room security order hroom arity) (body_room security order hroom arity)
            layout queue permutation (coefficient.2 arity).val := by
    funext word
    simp only [familyMass, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  rw [hmass, map_add, map_smul, map_sum, baseline_generating]
  simp_rw [uniform_generating]

end
end CurrentAFT.ActualFamilyPolynomial
