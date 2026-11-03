import AFT.CenteredGaussianEvaluation
import AFT.SymmetricCoefficients

/-! # Literal centered PGFs under the final independent permutation -/
namespace CurrentAFT.CenteredPolynomialSymmetry
open AFT RepresentedPolynomial HistogramNormalization
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]

theorem precompose (reference : Color → ℝ) (mass : (Slot → Color) → ℝ) (permutation : Equiv.Perm Slot) :
    centeredGeneratingLinear reference (fun word => mass (word ∘ permutation)) =
      centeredGeneratingLinear reference mass := by
  have hprod (word : Slot → Color) :
      (∏ slot, centeredFactor reference ((word ∘ permutation) slot)) =
        ∏ slot, centeredFactor reference (word slot) :=
    Equiv.prod_comp permutation (fun slot => centeredFactor reference (word slot))
  have h := (precomposeEquiv (Color := Color) permutation).sum_comp
    (fun word => mass word • ∏ slot, centeredFactor reference (word slot))
  change (∑ word, mass (word ∘ permutation) • ∏ slot, centeredFactor reference ((word ∘ permutation) slot)) = _ at h
  simpa only [hprod] using h

theorem symmetrized (reference : Color → ℝ) (mass : (Slot → Color) → ℝ) :
    centeredGeneratingLinear reference (symmetrizedMass mass) = centeredGeneratingLinear reference mass := by
  have hequal : symmetrizedMass mass =
      ∑ permutation : Equiv.Perm Slot, (FiniteDist.uniform (Equiv.Perm Slot)).weight permutation •
        (fun word => mass (word ∘ permutation)) := by
    funext word
    simp only [symmetrizedMass, BlockFock.symmetrize, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hequal, map_sum]
  simp_rw [map_smul, precompose]
  rw [← Finset.sum_smul, FiniteDist.sum_one, one_smul]

end
end CurrentAFT.CenteredPolynomialSymmetry
