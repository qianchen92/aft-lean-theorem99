import CurrentAFT.ActualWeightedFourier

/-! # Final uniform endpoint permutations remove arbitrary finite numberings -/
namespace CurrentAFT.SymmetrizedOutputRename
open AFT HistogramNormalization
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable {Slot Color : Type*} [Fintype Slot]

theorem precompose (mass : (Slot → Color) → ℝ) (permutation : Equiv.Perm Slot) :
    symmetrizedMass (fun word => mass (word ∘ permutation)) = symmetrizedMass mass := by
  funext word
  simp only [symmetrizedMass, BlockFock.symmetrize, FiniteDist.uniform_weight, ← Finset.mul_sum]
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight permutation) (fun point : Equiv.Perm Slot => mass (word ∘ point))

theorem renamings {Source : Type*} (first second : Source ≃ Slot) (mass : (Source → Color) → ℝ) :
    symmetrizedMass (renamedMass first mass) = symmetrizedMass (renamedMass second mass) := by
  let permutation : Equiv.Perm Slot := second.symm.trans first
  have hmass : renamedMass first mass = fun word => renamedMass second mass (word ∘ permutation) := by
    funext word
    apply congrArg mass
    funext point
    simp only [Function.comp_apply, permutation, Equiv.trans_apply, Equiv.symm_apply_apply]
  rw [hmass, precompose]

theorem average {Source : Type*} [Fintype Source] (law : FiniteDist Source)
    (mass : Source → (Slot → Color) → ℝ) :
    symmetrizedMass (fun word => law.expectation (fun source => mass source word)) =
      fun word => law.expectation (fun source => symmetrizedMass (mass source) word) := by
  funext word
  unfold symmetrizedMass BlockFock.symmetrize FiniteDist.expectation
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro source _
  apply Finset.sum_congr rfl
  intro permutation _
  ring

theorem add (first second : (Slot → Color) → ℝ) :
    symmetrizedMass (fun word => first word + second word) =
      fun word => symmetrizedMass first word + symmetrizedMass second word := by
  funext word
  simp only [symmetrizedMass, BlockFock.symmetrize, mul_add, Finset.sum_add_distrib]

theorem smul (scalar : ℝ) (mass : (Slot → Color) → ℝ) :
    symmetrizedMass (fun word => scalar * mass word) = fun word => scalar * symmetrizedMass mass word := by
  funext word
  simp only [symmetrizedMass, BlockFock.symmetrize, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro permutation _
  ring

theorem sum {Index : Type*} [Fintype Index] (mass : Index → (Slot → Color) → ℝ) :
    symmetrizedMass (fun word => ∑ index, mass index word) =
      fun word => ∑ index, symmetrizedMass (mass index) word := by
  funext word
  simp only [symmetrizedMass, BlockFock.symmetrize, Finset.mul_sum]
  rw [Finset.sum_comm]

end
end CurrentAFT.SymmetrizedOutputRename
