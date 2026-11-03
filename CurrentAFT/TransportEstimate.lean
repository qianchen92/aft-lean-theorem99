import CurrentAFT.AmbientFourier
import CurrentAFT.SupportTail
import CurrentAFT.ChargedEndpoint
import CurrentAFT.PublicCore

/-!
# From explicit Fourier and moment estimates to a positive public law

This theorem composes the checked ambient Fourier, full-frequency tail,
bounded clipping, and public conditioning arguments. Its low-support
cancellation, weighted-energy and physical-moment premises are explicit.
They are the construction-specific estimates that remain to be proved for
the current calibrated response. No sampler existence or complexity
conclusion is assumed or asserted.
-/

namespace CurrentAFT

open AFT
open scoped BigOperators Classical

noncomputable section

/-- Support counts nonzero coordinates of an actual coordinate frequency. -/
def frequencySupportDegree {Index : Type*} [Fintype Index] {modulus : ℕ}
    (frequency : Index → ZMod modulus) : ℕ :=
  (Finset.univ.filter fun index => frequency index ≠ 0).card

@[simp] theorem frequencySupportDegree_zero {Index : Type*} [Fintype Index]
    (modulus : ℕ) : frequencySupportDegree (0 : Index → ZMod modulus) = 0 := by
  simp [frequencySupportDegree]

/-- The complete error implication for a fixed public placement and its
actual coordinate endpoint channel. The conclusion samples public cores
before the hidden channel; it does not condition on an observed hidden input. -/
theorem calibrated_channel_zeroSum_error {Core : Type*} [Fintype Core]
    (dimension modulus : ℕ) [NeZero modulus]
    (proposal : FiniteDist Core) (weight : Core → ℝ)
    (channel : Core → FiniteDist (EndpointSpace dimension modulus))
    (publicCharge : Core → Prop)
    (hcharge : ∀ core, (channel core).eventMass (fun endpoint => ∑ index, endpoint index = 0) =
      if publicCharge core then 1 else 0)
    (hmean : ∑ core, proposal.weight core * weight core = 1)
    (order moment : ℕ) (hmoment : 1 ≤ moment)
    (radius bound momentBudget : ℝ) (hradius : 1 ≤ radius)
    (hcancel : ∀ frequency : EndpointSpace dimension modulus, frequency ≠ 0 →
      frequencySupportDegree frequency ≤ order →
        signedFourier (endpointMass proposal weight channel) (coordinateCharacter frequency) = 0)
    (hweighted : weightedSupportEnergy Finset.univ frequencySupportDegree
      (fun frequency : EndpointSpace dimension modulus =>
        ‖signedFourier (endpointMass proposal weight channel) (coordinateCharacter frequency)‖ ^ 2)
      radius ≤ bound)
    (hmomentBound : (∑ core, proposal.weight core * |weight core - 1| ^ (2 * moment)) ≤
      momentBudget)
    (hsmall : Real.sqrt ((bound - 1) / radius ^ (2 * (order + 1))) + momentBudget ≤
      1 / (2 * (modulus : ℝ))) :
    ∃ hpositive : 0 < publicCoreMass proposal weight publicCharge,
      1 / (2 * (modulus : ℝ)) ≤ publicCoreMass proposal weight publicCharge ∧
      ((positivePublicCoreLaw proposal weight publicCharge hpositive).mix channel).totalVariation
        (uniformZeroSum dimension modulus) ≤
          2 * (modulus : ℝ) *
            (Real.sqrt ((bound - 1) / radius ^ (2 * (order + 1))) + momentBudget) := by
  let mass := endpointMass proposal weight channel
  have hmass : ∑ endpoint, mass endpoint = 1 := by
    rw [endpointMass_sum]
    exact hmean
  have hzero : signedFourier mass (coordinateCharacter (0 : EndpointSpace dimension modulus)) = 1 := by
    rw [coordinateCharacter_zero, signedFourier_zero, hmass]
    norm_num
  have htail := complete_fourier_tail_of_full_weighted_bound
    frequencySupportDegree (fun frequency : EndpointSpace dimension modulus =>
      signedFourier mass (coordinateCharacter frequency)) order radius bound hradius
      (frequencySupportDegree_zero modulus) hzero hcancel hweighted
  have hfourier := coordinate_ambient_signed_half_l1 mass hmass
  have hroot := Real.sqrt_le_sqrt htail
  have hambient : (∑ endpoint, |mass endpoint -
      (FiniteDist.uniform (EndpointSpace dimension modulus)).weight endpoint|) ≤
        2 * (Real.sqrt ((bound - 1) / radius ^ (2 * (order + 1))) / 2) := by
    simp only [uniformDeviation] at hfourier
    simp only [FiniteDist.uniform_weight]
    nlinarith
  have hclip : clippingLoss proposal weight ≤ momentBudget :=
    clipping_loss_le_of_even_moment proposal.weight weight proposal.nonneg
      moment hmoment momentBudget hmomentBound
  have hsmall' : 2 * (Real.sqrt ((bound - 1) / radius ^ (2 * (order + 1))) / 2) +
      momentBudget ≤ 1 / (2 * (modulus : ℝ)) := by linarith
  obtain ⟨hpositiveEndpoint, hlower, herror⟩ := bounded_zeroSum_conditioning dimension modulus
    proposal weight channel (Real.sqrt ((bound - 1) / radius ^ (2 * (order + 1))) / 2)
      momentBudget hambient hclip hsmall'
  have heq := chargedMass_eq_publicCoreMass proposal weight channel
    (fun endpoint => ∑ index, endpoint index = 0) publicCharge hcharge
  have hpositive : 0 < publicCoreMass proposal weight publicCharge := by
    rwa [heq] at hpositiveEndpoint
  refine ⟨hpositive, ?_, ?_⟩
  · rwa [heq] at hlower
  · rw [positivePublicCoreLaw_mix proposal weight channel
      (fun endpoint => ∑ index, endpoint index = 0) publicCharge hcharge hpositive]
    convert herror using 1; ring

end

end CurrentAFT
