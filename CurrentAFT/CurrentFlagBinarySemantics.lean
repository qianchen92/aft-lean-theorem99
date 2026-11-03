import CurrentAFT.CurrentFlagBinary

/-! The stored binary iteration computes the same rational arrays as the canonical response. -/

namespace CurrentAFT.CurrentFlagBinary

open AFT AFT.RationalNumerics AFT.BoundaryCalibration AFT.BinaryArithmetic
open AFT.BinaryArithmetic.RationalBits CurrentRationalFlagLaw CurrentFlagIteration
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 400000

theorem projection_program_eq (charts colors features : ℕ)
    (feature : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (profile : Fin charts → ℚ) (point : Fin charts) :
    chartProjectionProgram charts colors features feature allowed profile point =
      projectionQ feature allowed profile point := by
  rw [← CurrentFlagArray.projection_eq charts feature allowed profile point]
  simp only [chartProjectionProgram, chartExpectationProgram, CurrentFlagArray.projection,
    CurrentFlagArray.mean, component_eq]

theorem deletion_program_eq (charts colors features : ℕ)
    (feature : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (safe : Finset (Fin charts)) (profile : Fin charts → ℚ) (point : Fin charts) :
    chartDeletionProgram charts colors features feature allowed safe profile point =
      projectionQ feature allowed (badMaskQ (fun input => input ∈ safe) profile) point := by
  rw [chartDeletionProgram, projection_program_eq]
  apply congrArg (fun value => projectionQ feature allowed value point)
  funext input
  simp only [badMaskQ, LinearMap.coe_mk, AddHom.coe_mk]
  split_ifs <;> rfl

theorem matrix_program_eq (charts colors features : ℕ)
    (feature : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (safe : Finset (Fin charts)) :
    chartDeletionMatrixProgram charts colors features feature allowed safe =
      iterationMatrix feature allowed (fun input => input ∈ safe) := by
  funext output input
  have hb : (fun point : Fin charts => if point = input then (1 : ℚ) else 0) = Pi.single input 1 := by
    funext point
    by_cases hp : point = input
    · subst point
      simp
    · simp only [if_neg hp, Pi.single_eq_of_ne hp]
  rw [chartDeletionMatrixProgram, hb, deletion_program_eq]
  simp only [iterationMatrix, LinearMap.toMatrix'_apply, LinearMap.sub_apply, LinearMap.id_apply,
    responseQ, LinearMap.comp_apply, Pi.sub_apply]
  ring

theorem regular_eq_array {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (safe fiber : Vector Bool charts) (atom : RationalBits)
    (steps : ℕ) (point : Fin charts) :
    ((regular feature allowed line safe fiber atom steps).data.get point).decode =
      (CurrentFlagArray.regular charts (fun index => (feature.get index).get)
        (fun index => maskSet (allowed.get index)) line.get safe.get atom.decode
        (chartSpikeProgram charts (maskSet fiber)) steps).get point := by
  have hs : (fun input => input ∈ maskSet safe) = (fun input => safe.get input = true) := by
    funext input
    apply propext
    simp only [maskSet, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [regular_value, CurrentFlagArray.regular_eq, matrix_program_eq, hs]
  simp only [CurrentFlagArray.target_eq, regularIterate, CurrentFlagIteration.iterate]

end
end CurrentAFT.CurrentFlagBinary
