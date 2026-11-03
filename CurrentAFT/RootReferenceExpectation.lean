import CurrentAFT.RootIndependentBackground

/-! # Exact conversion between modular roots and the original integer blur -/
namespace CurrentAFT.RootReferenceExpectation
open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy FirstHistogram CycleRootExpansion
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize

theorem rootReference_periodic_expectation (security : ℕ) (value : ℤ → ℝ)
    (hperiodic : ∀ first second : ℤ, (first : Root security) = (second : Root security) →
      value first = value second) :
    (rootReference security).expectation (fun root => value (root.val : ℤ)) =
      (publicBlurLaw security).expectation (fun pair => value (pair.2.val - pair.1.val)) := by
  unfold rootReference ProtectedCycle.differenceLaw
  rw [FiniteDist.expectation_map]
  have hvalue (pair : BlurSeed security) :
      value (((((pair.1 : ℤ) : Root security) - ((pair.2 : ℤ) : Root security)).val : ℕ) : ℤ) =
        value (pair.1.val - pair.2.val) := by
    apply hperiodic
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val, Int.cast_sub]
  simp only [FiniteDist.expectation, Function.comp_apply, hvalue, publicBlurLaw,
    Fintype.sum_prod_type, FiniteDist.prod_weight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  ring

theorem publicBlur_seed_expectation (security : ℕ) (value : ℤ → ℝ) :
    (publicBlurLaw security).expectation (fun pair => value (pair.2.val - pair.1.val)) =
      (actualSeedLaw security).expectation (fun seed => value (actualBlur security seed)) := by
  simp only [FiniteDist.expectation, publicBlurLaw, actualSeedLaw, actualBlur,
    Fintype.sum_prod_type, FiniteDist.prod_weight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, FiniteDist.sum_one, one_mul]
  ring

theorem rootReference_seed_expectation (security : ℕ) (value : ℤ → ℝ)
    (hperiodic : ∀ first second : ℤ, (first : Root security) = (second : Root security) →
      value first = value second) :
    (rootReference security).expectation (fun root => value (root.val : ℤ)) =
      (actualSeedLaw security).expectation (fun seed => value (actualBlur security seed)) :=
  (rootReference_periodic_expectation security value hperiodic).trans (publicBlur_seed_expectation security value)

end
end CurrentAFT.RootReferenceExpectation
