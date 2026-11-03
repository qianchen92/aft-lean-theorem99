import AFT.TransportBound

/-!
# The finite full-support obstruction

This file proves the probability argument of V7 Proposition
`prop:aft-full-support-floor`. The source law is any finite, full-support
probability distribution. Source-independent mixtures of permutations cannot
remove its positive minimum atom, hence cannot approach a law supported on a
proper subset with arbitrarily small total variation error.

The analytic fact that a discrete Gaussian reduced modulo the modulus has
full support is proved in `AFT.GaussianSource`, which instantiates these
general finite theorems without an assumed Gaussian full-support premise.
-/

namespace AFT
namespace FiniteDist

open scoped BigOperators Classical

variable {α Ω : Type*} [Fintype α] [Fintype Ω]

/-- Every point has strictly positive probability. -/
def FullSupport (source : FiniteDist α) : Prop :=
  ∀ a, 0 < source.weight a

/-- The smallest atom of a probability distribution on a nonempty finite type. -/
noncomputable def minimumMass [Nonempty α] (source : FiniteDist α) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty source.weight

theorem minimumMass_le [Nonempty α] (source : FiniteDist α) (a : α) :
    source.minimumMass ≤ source.weight a :=
  Finset.inf'_le source.weight (Finset.mem_univ a)

theorem minimumMass_pos [Nonempty α] {source : FiniteDist α}
    (hsource : source.FullSupport) : 0 < source.minimumMass := by
  exact (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun a _ => hsource a)

/-- Draw the permutation independently of the source. All correlations among
parameters used to select the permutation are allowed. -/
noncomputable def permutationMixture (sampler : FiniteDist Ω)
    (source : FiniteDist α) (permutation : Ω → α ≃ α) : FiniteDist α :=
  sampler.mix (fun seed => source.map (permutation seed))

/-- A source-independent mixture of permutations preserves the lower bound
on every atom, even if its individual permutations are not identical. -/
theorem minimumMass_le_permutationMixture_weight [Nonempty α]
    (sampler : FiniteDist Ω) (source : FiniteDist α)
    (permutation : Ω → α ≃ α) (a : α) :
    source.minimumMass ≤ (permutationMixture sampler source permutation).weight a := by
  simp only [permutationMixture, mix_weight, map_equiv_weight]
  calc
    source.minimumMass = ∑ seed, sampler.weight seed * source.minimumMass := by
      rw [← Finset.sum_mul, sampler.sum_one, one_mul]
    _ ≤ ∑ seed, sampler.weight seed * source.weight ((permutation seed).symm a) := by
      apply Finset.sum_le_sum
      intro seed _
      exact mul_le_mul_of_nonneg_left (source.minimumMass_le _) (sampler.nonneg seed)

/-- Summing the atom bound gives a lower bound for every event. -/
theorem permutationMixture_event_lower_bound [Nonempty α]
    (sampler : FiniteDist Ω) (source : FiniteDist α)
    (permutation : Ω → α ≃ α) (s : Finset α) :
    (s.card : ℝ) * source.minimumMass ≤
      (permutationMixture sampler source permutation).event s := by
  calc
    (s.card : ℝ) * source.minimumMass = ∑ a ∈ s, source.minimumMass := by simp
    _ ≤ (permutationMixture sampler source permutation).event s := by
      apply Finset.sum_le_sum
      intro a _
      exact minimumMass_le_permutationMixture_weight sampler source permutation a

/-- The explicit finite-parameter error floor from V7: the probability outside
`fiber` is at least its complement's cardinality times the minimum atom. -/
theorem permutationMixture_complement_lower_bound [Nonempty α]
    (sampler : FiniteDist Ω) (source : FiniteDist α)
    (permutation : Ω → α ≃ α) (fiber : Finset α) :
    ((Fintype.card α - fiber.card : ℕ) : ℝ) * source.minimumMass ≤
      (permutationMixture sampler source permutation).event fiberᶜ := by
  simpa only [Finset.card_compl] using
    permutationMixture_event_lower_bound sampler source permutation fiberᶜ

/-- Any target assigning zero mass outside `fiber` is separated from every
source-independent permutation mixture by the same error floor. -/
theorem support_obstruction_tv_floor [Nonempty α]
    (sampler : FiniteDist Ω) (source target : FiniteDist α)
    (permutation : Ω → α ≃ α) (fiber : Finset α)
    (htarget : ∀ a, a ∉ fiber → target.weight a = 0)
    {error : ℝ}
    (herror : TVBound (permutationMixture sampler source permutation) target error) :
    ((Fintype.card α - fiber.card : ℕ) : ℝ) * source.minimumMass ≤ error := by
  have hzero : target.event fiberᶜ = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    exact htarget a (Finset.mem_compl.mp ha)
  have htv := herror fiberᶜ
  rw [hzero, sub_zero,
    abs_of_nonneg ((permutationMixture sampler source permutation).event_nonneg fiberᶜ)] at htv
  exact (permutationMixture_complement_lower_bound sampler source permutation fiber).trans htv

/-- A full-support source and a proper target support give a strictly positive
floor at each fixed finite parameter. -/
theorem support_obstruction_floor_pos [Nonempty α]
    {source : FiniteDist α} (hsource : source.FullSupport)
    (fiber : Finset α) (hproper : fiber ≠ Finset.univ) :
    0 < ((Fintype.card α - fiber.card : ℕ) : ℝ) * source.minimumMass := by
  apply mul_pos
  · exact_mod_cast (Nat.sub_pos_of_lt (Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ fiber, hproper⟩)))
  · exact minimumMass_pos hsource

/-- Even allowing the sampler and its permutations to change with the
requested accuracy cannot achieve every positive accuracy at a fixed source
and proper target support. -/
theorem no_arbitrarily_accurate_permutation_mixtures [Nonempty α]
    (source target : FiniteDist α) (hsource : source.FullSupport)
    (fiber : Finset α) (hproper : fiber ≠ Finset.univ)
    (htarget : ∀ a, a ∉ fiber → target.weight a = 0) :
    ¬ (∀ error : ℝ, 0 < error →
      ∃ sampler : FiniteDist Ω, ∃ permutation : Ω → α ≃ α,
        TVBound (permutationMixture sampler source permutation) target error) := by
  intro hall
  have hpositive := support_obstruction_floor_pos hsource fiber hproper
  obtain ⟨sampler, permutation, herror⟩ := hall
    (((Fintype.card α - fiber.card : ℕ) : ℝ) * source.minimumMass / 2)
    (half_pos hpositive)
  have hlower := support_obstruction_tv_floor sampler source target permutation fiber htarget herror
  linarith

end FiniteDist
end AFT
