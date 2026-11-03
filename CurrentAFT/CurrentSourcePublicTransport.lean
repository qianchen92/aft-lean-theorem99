import CurrentAFT.CurrentSourceTail
import AFT.FiniteChannelIdentities

/-! # One complete-source cost under an independent positive public law

The public law may contain the whole core, the complete conditional map
draws and both permutations. The physical channel is shared by the full
and protected experiments, and the output may retain all public data.
-/
namespace CurrentAFT.CurrentSourcePublicTransport

open AFT CurrentSourceProtection GaussianProductProtection
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
attribute [local irreducible] Parameters.bodySize Parameters.legCount sourceCount
  protectedSourceLaw cutoff

def gaussianOutputLaw {Output : Type*} [Fintype Output] (security : ℕ)
    (channel : (Fin (sourceCount security) → ℤ) → FiniteDist Output) : FiniteDist Output :=
  FiniteDist.countableMix (fullMass (width security) (sourceCount security))
    (fullMass_nonneg (width security) (width_pos security) (sourceCount security))
    (fullMass_summable (width security) (width_pos security) (sourceCount security))
    (fullMass_sum (width security) (width_pos security) (sourceCount security)) channel

/-- The public law is arbitrary, normalized and nonnegative, and is drawn
independently of the full Gaussian source. Its mixture costs one source
budget, regardless of the number of public choices or endpoint outputs. -/
theorem public_channel_tv {Public Output : Type*} [Fintype Public] [Fintype Output]
    (security : ℕ) (publicLaw : FiniteDist Public)
    (physical : Public → (Fin (sourceCount security) → ℤ) → FiniteDist Output) :
    FiniteDist.TVBound
      (publicLaw.mix (fun draw => gaussianOutputLaw security (physical draw)))
      (publicLaw.mix (fun draw => (protectedSourceLaw security).mix
        (fun word => physical draw (sourceEmbedding (cutoff security) word))))
      (budget security) := by
  exact FiniteDist.TVBound.mix_right publicLaw (fun draw => channel_tv security (physical draw))

theorem protected_product_law {Public Output : Type*} [Fintype Public] [Fintype Output]
    (security : ℕ) (publicLaw : FiniteDist Public)
    (physical : Public → (Fin (sourceCount security) → ℤ) → FiniteDist Output) :
    (publicLaw.mix (fun draw => (protectedSourceLaw security).mix
      (fun word => physical draw (sourceEmbedding (cutoff security) word)))) =
      (publicLaw.prod (protectedSourceLaw security)).mix
        (fun pair => physical pair.1 (sourceEmbedding (cutoff security) pair.2)) := by
  apply FiniteDist.ext
  intro output
  simp only [FiniteDist.mix_weight, FiniteDist.prod_weight, Fintype.sum_prod_type,
    Finset.mul_sum, mul_assoc]

/-- Literal product-law form of the protected experiment. -/
theorem public_product_channel_tv {Public Output : Type*} [Fintype Public] [Fintype Output]
    (security : ℕ) (publicLaw : FiniteDist Public)
    (physical : Public → (Fin (sourceCount security) → ℤ) → FiniteDist Output) :
    FiniteDist.TVBound
      (publicLaw.mix (fun draw => gaussianOutputLaw security (physical draw)))
      ((publicLaw.prod (protectedSourceLaw security)).mix
        (fun pair => physical pair.1 (sourceEmbedding (cutoff security) pair.2)))
      (budget security) := by
  rw [← protected_product_law]
  exact public_channel_tv security publicLaw physical

/-- The same budget transfers to a different description of the protected
output once pointwise protected-input agreement has been established. Only
public data in the support of the actual public law must be checked. -/
theorem public_channel_tv_of_agreement {Public Output : Type*}
    [Fintype Public] [Fintype Output] (security : ℕ) (publicLaw : FiniteDist Public)
    (physical : Public → (Fin (sourceCount security) → ℤ) → FiniteDist Output)
    (protectedPhysical : Public → ProtectedWord (cutoff security) → FiniteDist Output)
    (hagree : ∀ draw, publicLaw.weight draw ≠ 0 → ∀ word,
      physical draw (sourceEmbedding (cutoff security) word) = protectedPhysical draw word) :
    FiniteDist.TVBound
      (publicLaw.mix (fun draw => gaussianOutputLaw security (physical draw)))
      (publicLaw.mix (fun draw => (protectedSourceLaw security).mix (protectedPhysical draw)))
      (budget security) := by
  have heq : (publicLaw.mix (fun draw => (protectedSourceLaw security).mix
      (fun word => physical draw (sourceEmbedding (cutoff security) word)))) =
        publicLaw.mix (fun draw => (protectedSourceLaw security).mix (protectedPhysical draw)) := by
    apply FiniteDist.mix_congr_support
    intro draw hpublic
    congr 1
    funext word
    exact hagree draw hpublic word
  rw [← heq]
  exact public_channel_tv security publicLaw physical

end
end CurrentAFT.CurrentSourcePublicTransport
