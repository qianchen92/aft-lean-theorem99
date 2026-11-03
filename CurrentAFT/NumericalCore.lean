import CurrentAFT.PublicCore
import CurrentAFT.Conditioning

/-!
# Numerical perturbation of the clipped public core

This is the numerical-error part of `lem:df-bounded-rejection` in the
current manuscript. The same public charge test is used throughout, at
one fixed placement. Changing the proposal by TV at most `epsilon` and
the public weight uniformly by at most `eta` changes the unnormalized
clipped charged measure by L1 at most `4 * epsilon + eta`.

The mass and normalization estimates below are proved for these actual
public measures. They do not provide the physical numerical evaluator,
its requested precision, or the complete sampler's runtime bound.
-/

namespace CurrentAFT

open AFT
open scoped BigOperators Classical

noncomputable section

variable {Core : Type*} [Fintype Core]

/-- Bounded clipping controls a proposal error by twice its L1 norm;
its nonexpansiveness controls the uniform public-weight error. -/
theorem clipped_public_core_l1 (proposal numericalProposal : FiniteDist Core)
    (weight numericalWeight : Core → ℝ) (publicCharge : Core → Prop)
    (epsilon eta : ℝ) (hproposal : proposal.totalVariation numericalProposal ≤ epsilon)
    (hweight : ∀ core, |numericalWeight core - weight core| ≤ eta) :
    (∑ core, |clippedPublicCoreWeight numericalProposal numericalWeight publicCharge core -
      clippedPublicCoreWeight proposal weight publicCharge core|) ≤ 4 * epsilon + eta := by
  have hproposalL1 :
      (∑ core, |numericalProposal.weight core - proposal.weight core|) ≤ 2 * epsilon := by
    rw [FiniteDist.totalVariation_eq_half_l1] at hproposal
    have hsymmetry :
        (∑ core, |numericalProposal.weight core - proposal.weight core|) =
          ∑ core, |proposal.weight core - numericalProposal.weight core| := by
      apply Finset.sum_congr rfl
      intro core _
      exact abs_sub_comm _ _
    rw [hsymmetry]
    linarith
  have hpoint (core : Core) :
      |numericalProposal.weight core * clip (numericalWeight core) -
          proposal.weight core * clip (weight core)| ≤
        2 * |numericalProposal.weight core - proposal.weight core| +
          proposal.weight core * eta := by
    have hclip : |clip (numericalWeight core) - clip (weight core)| ≤ eta :=
      (clip_abs_sub_le (numericalWeight core) (weight core)).trans (hweight core)
    calc
      _ = |(numericalProposal.weight core - proposal.weight core) * clip (numericalWeight core) +
          proposal.weight core * (clip (numericalWeight core) - clip (weight core))| := by
        congr 1
        ring
      _ ≤ |numericalProposal.weight core - proposal.weight core| * clip (numericalWeight core) +
          proposal.weight core * |clip (numericalWeight core) - clip (weight core)| := by
        simpa only [abs_mul, abs_of_nonneg (clip_nonneg _),
          abs_of_nonneg (proposal.nonneg core)] using abs_add_le
            ((numericalProposal.weight core - proposal.weight core) * clip (numericalWeight core))
            (proposal.weight core * (clip (numericalWeight core) - clip (weight core)))
      _ ≤ |numericalProposal.weight core - proposal.weight core| * 2 +
          proposal.weight core * eta :=
        add_le_add (mul_le_mul_of_nonneg_left (clip_le_two _) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hclip (proposal.nonneg core))
      _ = _ := by ring
  have huncharged :
      (∑ core, |numericalProposal.weight core * clip (numericalWeight core) -
        proposal.weight core * clip (weight core)|) ≤ 4 * epsilon + eta := by
    calc
      _ ≤ ∑ core, (2 * |numericalProposal.weight core - proposal.weight core| +
          proposal.weight core * eta) := Finset.sum_le_sum (fun core _ => hpoint core)
      _ = 2 * (∑ core, |numericalProposal.weight core - proposal.weight core|) + eta := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, proposal.sum_one, one_mul]
      _ ≤ _ := by linarith
  exact (AFT.SignedConditioning.restriction_l1_le
    (fun core => numericalProposal.weight core * clip (numericalWeight core))
    (fun core => proposal.weight core * clip (weight core)) publicCharge).trans huncharged

/-- The perturbation bound applies to the purely public charge mass;
no endpoint-channel or independence hypothesis is needed. -/
theorem public_core_mass_perturbation (proposal numericalProposal : FiniteDist Core)
    (weight numericalWeight : Core → ℝ) (publicCharge : Core → Prop)
    (epsilon eta : ℝ) (hproposal : proposal.totalVariation numericalProposal ≤ epsilon)
    (hweight : ∀ core, |numericalWeight core - weight core| ≤ eta) :
    |publicCoreMass numericalProposal numericalWeight publicCharge -
      publicCoreMass proposal weight publicCharge| ≤ 4 * epsilon + eta :=
  (AFT.SignedConditioning.mass_difference_le_l1
    (clippedPublicCoreWeight numericalProposal numericalWeight publicCharge)
    (clippedPublicCoreWeight proposal weight publicCharge)).trans
      (clipped_public_core_l1 proposal numericalProposal weight numericalWeight publicCharge
        epsilon eta hproposal hweight)

/-- An ideal mass of at least `1 / (4*q)` and a numerical error of at
most `1 / (8*q)` leave numerical public mass at least `1 / (8*q)`. -/
theorem numerical_public_core_mass_lower (proposal numericalProposal : FiniteDist Core)
    (weight numericalWeight : Core → ℝ) (publicCharge : Core → Prop)
    (q epsilon eta : ℝ) (hq : 0 < q)
    (hproposal : proposal.totalVariation numericalProposal ≤ epsilon)
    (hweight : ∀ core, |numericalWeight core - weight core| ≤ eta)
    (hideal : 1 / (4 * q) ≤ publicCoreMass proposal weight publicCharge)
    (hsmall : 4 * epsilon + eta ≤ 1 / (8 * q)) :
    1 / (8 * q) ≤ publicCoreMass numericalProposal numericalWeight publicCharge := by
  have hmass := public_core_mass_perturbation proposal numericalProposal weight numericalWeight
    publicCharge epsilon eta hproposal hweight
  have hfractions : 1 / (4 * q) - 1 / (8 * q) = 1 / (8 * q) := by
    field_simp
    ring
  linarith [(abs_le.mp hmass).1]

/-- The normalized numerical core has TV error at most `4*q*E`, for
`E = 4*epsilon + eta`. The normalization argument uses the ideal mass
as its denominator, retaining the manuscript's constant. -/
theorem numerical_public_core_accuracy (proposal numericalProposal : FiniteDist Core)
    (weight numericalWeight : Core → ℝ) (publicCharge : Core → Prop)
    (q epsilon eta : ℝ) (hq : 0 < q)
    (hproposal : proposal.totalVariation numericalProposal ≤ epsilon)
    (hweight : ∀ core, |numericalWeight core - weight core| ≤ eta)
    (hideal : 1 / (4 * q) ≤ publicCoreMass proposal weight publicCharge)
    (hsmall : 4 * epsilon + eta ≤ 1 / (8 * q)) :
    ∃ (hidealPositive : 0 < publicCoreMass proposal weight publicCharge)
      (hnumericalPositive : 0 < publicCoreMass numericalProposal numericalWeight publicCharge),
      1 / (8 * q) ≤ publicCoreMass numericalProposal numericalWeight publicCharge ∧
      (positivePublicCoreLaw numericalProposal numericalWeight publicCharge hnumericalPositive).totalVariation
        (positivePublicCoreLaw proposal weight publicCharge hidealPositive) ≤
          4 * q * (4 * epsilon + eta) := by
  have hl1 := clipped_public_core_l1 proposal numericalProposal weight numericalWeight
    publicCharge epsilon eta hproposal hweight
  have herrorNonneg : 0 ≤ 4 * epsilon + eta :=
    (Finset.sum_nonneg (fun core _ => abs_nonneg
      (clippedPublicCoreWeight numericalProposal numericalWeight publicCharge core -
        clippedPublicCoreWeight proposal weight publicCharge core))).trans hl1
  have hlower := numerical_public_core_mass_lower proposal numericalProposal weight numericalWeight
    publicCharge q epsilon eta hq hproposal hweight hideal hsmall
  have hidealPositive : 0 < publicCoreMass proposal weight publicCharge :=
    lt_of_lt_of_le (by positivity) hideal
  have hnumericalPositive : 0 < publicCoreMass numericalProposal numericalWeight publicCharge :=
    lt_of_lt_of_le (by positivity) hlower
  refine ⟨hidealPositive, hnumericalPositive, hlower, ?_⟩
  have hnormalized := AFT.SignedConditioning.normalized_signed_l1
    (clippedPublicCoreWeight proposal weight publicCharge)
    (clippedPublicCoreWeight numericalProposal numericalWeight publicCharge)
    (clippedPublicCoreWeight_nonneg numericalProposal numericalWeight publicCharge)
    hidealPositive hnumericalPositive
  have hsymmetry :
      (∑ core, |clippedPublicCoreWeight proposal weight publicCharge core -
        clippedPublicCoreWeight numericalProposal numericalWeight publicCharge core|) ≤
          4 * epsilon + eta := by
    simpa only [abs_sub_comm] using hl1
  have hnormalizedBound :
      (∑ core, |clippedPublicCoreWeight numericalProposal numericalWeight publicCharge core /
          publicCoreMass numericalProposal numericalWeight publicCharge -
        clippedPublicCoreWeight proposal weight publicCharge core /
          publicCoreMass proposal weight publicCharge|) ≤
        2 * (4 * epsilon + eta) / publicCoreMass proposal weight publicCharge := by
    have hbound := hnormalized.trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsymmetry (by norm_num)) hidealPositive.le)
    simpa only [abs_sub_comm, publicCoreMass] using hbound
  rw [FiniteDist.totalVariation_eq_half_l1]
  change (∑ core, |clippedPublicCoreWeight numericalProposal numericalWeight publicCharge core /
      publicCoreMass numericalProposal numericalWeight publicCharge -
    clippedPublicCoreWeight proposal weight publicCharge core /
      publicCoreMass proposal weight publicCharge|) / 2 ≤ _
  calc
    _ ≤ (2 * (4 * epsilon + eta) / publicCoreMass proposal weight publicCharge) / 2 := by
      linarith
    _ = (4 * epsilon + eta) / publicCoreMass proposal weight publicCharge := by ring
    _ ≤ (4 * epsilon + eta) / (1 / (4 * q)) :=
      div_le_div_of_nonneg_left herrorNonneg (by positivity) hideal
    _ = 4 * q * (4 * epsilon + eta) := by field_simp

end

end CurrentAFT
