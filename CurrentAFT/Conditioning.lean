import AFT.SignedConditioning
import CurrentAFT.BoundedClipping

/-!
# Bounded clipping followed by public charge conditioning

This module proves the finite-measure part of the current manuscript's
`thm:df-positive-conditioning`. The endpoint kernel may contain correlated
hidden inputs, the protected body cycle, a shared queue, and final relabeling.
Only its normalization is used. The construction-specific ambient error and
the physical weight moments remain separate proof obligations.
-/

namespace CurrentAFT

open scoped BigOperators Classical
open AFT

noncomputable section

variable {Core Endpoint : Type*} [Fintype Core] [Fintype Endpoint]

/-- The signed endpoint image, relative to the uncharged public proposal. -/
def endpointMass (proposal : FiniteDist Core) (weight : Core → ℝ)
    (channel : Core → FiniteDist Endpoint) (output : Endpoint) : ℝ :=
  ∑ core, proposal.weight core * weight core * (channel core).weight output

/-- Clipping loss is measured under the uncharged proposal, at fixed placement. -/
def clippingLoss (proposal : FiniteDist Core) (weight : Core → ℝ) : ℝ :=
  ∑ core, proposal.weight core * |weight core - clip (weight core)|

theorem endpointMass_nonneg (proposal : FiniteDist Core) (weight : Core → ℝ)
    (channel : Core → FiniteDist Endpoint) (hweight : ∀ core, 0 ≤ weight core)
    (output : Endpoint) : 0 ≤ endpointMass proposal weight channel output := by
  exact Finset.sum_nonneg fun core _ =>
    mul_nonneg (mul_nonneg (proposal.nonneg core) (hweight core))
      ((channel core).nonneg output)

theorem endpointMass_sum (proposal : FiniteDist Core) (weight : Core → ℝ)
    (channel : Core → FiniteDist Endpoint) :
    (∑ output, endpointMass proposal weight channel output) =
      ∑ core, proposal.weight core * weight core := by
  unfold endpointMass
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, FiniteDist.sum_one, mul_one]

/-- Clipping commutes with passing through the same stochastic channel up to
its public L1 loss. No independence of the endpoint coordinates is assumed. -/
theorem clipped_endpoint_l1 (proposal : FiniteDist Core) (weight : Core → ℝ)
    (channel : Core → FiniteDist Endpoint) :
    (∑ output, |endpointMass proposal (fun core => clip (weight core)) channel output -
      endpointMass proposal weight channel output|) ≤ clippingLoss proposal weight := by
  have hd (output) :
      endpointMass proposal (fun core => clip (weight core)) channel output -
        endpointMass proposal weight channel output =
      ∑ core, (proposal.weight core * (clip (weight core) - weight core)) *
        (channel core).weight output := by
    simp only [endpointMass, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro core _
    ring
  simp_rw [hd]
  have h := FiniteDist.signed_kernel_l1_contraction
    (fun core => proposal.weight core * (clip (weight core) - weight core)) channel
  simpa only [abs_mul, abs_of_nonneg (proposal.nonneg _), abs_sub_comm, clippingLoss]
    using h

theorem clipped_ambient_l1 (proposal : FiniteDist Core) (weight : Core → ℝ)
    (channel : Core → FiniteDist Endpoint) (reference : FiniteDist Endpoint)
    (ambientError clipError : ℝ)
    (hambient : (∑ output, |endpointMass proposal weight channel output -
      reference.weight output|) ≤ 2 * ambientError)
    (hclip : clippingLoss proposal weight ≤ clipError) :
    (∑ output, |endpointMass proposal (fun core => clip (weight core)) channel output -
      reference.weight output|) ≤ 2 * ambientError + clipError := by
  have ht := Finset.sum_le_sum (s := Finset.univ) (fun output _ =>
    abs_sub_le (endpointMass proposal (fun core => clip (weight core)) channel output)
      (endpointMass proposal weight channel output) (reference.weight output))
  rw [Finset.sum_add_distrib] at ht
  exact ht.trans (by linarith [clipped_endpoint_l1 proposal weight channel])

/-- The mass of the positive clipped endpoint measure on the charge event. -/
def chargedMass (proposal : FiniteDist Core) (weight : Core → ℝ)
    (channel : Core → FiniteDist Endpoint) (charge : Endpoint → Prop) : ℝ :=
  ∑ output, AFT.SignedConditioning.restricted
    (endpointMass proposal (fun core => clip (weight core)) channel) charge output

/-- The actual probability law obtained by restricting and normalizing the
clipped endpoint measure. The positive-mass proof is required explicitly. -/
def positiveEndpointLaw (proposal : FiniteDist Core) (weight : Core → ℝ)
    (channel : Core → FiniteDist Endpoint) (charge : Endpoint → Prop)
    (hpositive : 0 < chargedMass proposal weight channel charge) : FiniteDist Endpoint :=
  FiniteDist.normalize
    (AFT.SignedConditioning.restricted
      (endpointMass proposal (fun core => clip (weight core)) channel) charge)
    (fun output => by
      unfold AFT.SignedConditioning.restricted
      split_ifs
      · exact endpointMass_nonneg proposal _ channel (fun core => clip_nonneg _) output
      · rfl)
    hpositive

/-- Stronger mass bound in the manuscript's conditioning proof. This is a
finite-measure theorem, not an assertion that the calibrated weight exists. -/
theorem chargedMass_lower_bound (proposal : FiniteDist Core) (weight : Core → ℝ)
    (channel : Core → FiniteDist Endpoint) (reference : FiniteDist Endpoint)
    (charge : Endpoint → Prop) (q ambientError clipError : ℝ) (hq : 0 < q)
    (hcharge : reference.eventMass charge = 1 / q)
    (hambient : (∑ output, |endpointMass proposal weight channel output -
      reference.weight output|) ≤ 2 * ambientError)
    (hclip : clippingLoss proposal weight ≤ clipError)
    (hsmall : 2 * ambientError + clipError ≤ 1 / (2 * q)) :
    1 / (2 * q) ≤ chargedMass proposal weight channel charge := by
  let clipped := endpointMass proposal (fun core => clip (weight core)) channel
  have hl1 := clipped_ambient_l1 proposal weight channel reference ambientError clipError
    hambient hclip
  have hrestricted := (AFT.SignedConditioning.restriction_l1_le clipped
    reference.weight charge).trans hl1
  have hmass := (AFT.SignedConditioning.mass_difference_le_l1
    (AFT.SignedConditioning.restricted clipped charge)
    (AFT.SignedConditioning.restricted reference.weight charge)).trans hrestricted
  have hreference : (∑ output, AFT.SignedConditioning.restricted reference.weight charge output) =
      1 / q := hcharge
  rw [hreference] at hmass
  change |chargedMass proposal weight channel charge - 1 / q| ≤ _ at hmass
  have hhalf : 1 / q - 1 / (2 * q) = 1 / (2 * q) := by field_simp; ring
  linarith [(abs_le.mp hmass).1]

/-- Current `thm:df-positive-conditioning`, with the stronger mass bound from
its proof. The TV bound concerns the complete endpoint law after charge. -/
theorem bounded_positive_conditioning (proposal : FiniteDist Core) (weight : Core → ℝ)
    (channel : Core → FiniteDist Endpoint) (reference : FiniteDist Endpoint)
    (charge : Endpoint → Prop) (q ambientError clipError : ℝ) (hq : 0 < q)
    (hcharge : reference.eventMass charge = 1 / q)
    (hambient : (∑ output, |endpointMass proposal weight channel output -
      reference.weight output|) ≤ 2 * ambientError)
    (hclip : clippingLoss proposal weight ≤ clipError)
    (hsmall : 2 * ambientError + clipError ≤ 1 / (2 * q)) :
    ∃ hpositive : 0 < chargedMass proposal weight channel charge,
      1 / (2 * q) ≤ chargedMass proposal weight channel charge ∧
      (positiveEndpointLaw proposal weight channel charge hpositive).totalVariation
        (reference.condition charge (by rw [hcharge]; positivity)) ≤
          2 * q * (2 * ambientError + clipError) := by
  have hlower := chargedMass_lower_bound proposal weight channel reference charge
    q ambientError clipError hq hcharge hambient hclip hsmall
  have hpositive : 0 < chargedMass proposal weight channel charge :=
    lt_of_lt_of_le (by positivity) hlower
  refine ⟨hpositive, hlower, ?_⟩
  have hbound := AFT.SignedConditioning.conditional_signed_l1
    (endpointMass proposal (fun core => clip (weight core)) channel) reference charge
    (1 / q) (2 * ambientError + clipError) (by positivity) hcharge.ge
    (clipped_ambient_l1 proposal weight channel reference ambientError clipError hambient hclip)
    (by convert hsmall using 1; ring)
  rw [FiniteDist.totalVariation_eq_half_l1]
  change (∑ output, |AFT.SignedConditioning.conditionalMass
    (endpointMass proposal (fun core => clip (weight core)) channel) charge output -
    AFT.SignedConditioning.conditionalMass reference.weight charge output|) / 2 ≤ _
  calc
    _ ≤ (4 * (2 * ambientError + clipError) / (1 / q)) / 2 := by linarith [hbound.2]
    _ = _ := by field_simp; ring

end

end CurrentAFT
