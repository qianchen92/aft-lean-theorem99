import CurrentAFT.Conditioning
import CurrentAFT.ZeroSumTarget
import CurrentAFT.PublicCharge

/-!
# Conditioning onto the actual zero-sum target

The reference event mass is proved by finite counting. It is not an
extra analytic premise. At a fixed placement, the channel may average any
remaining finite randomness, including correlated protected inputs.
-/

namespace CurrentAFT

open AFT
open scoped BigOperators Classical

noncomputable section

theorem uniform_eventMass_zeroSum (dimension modulus : ℕ) [NeZero modulus] :
    (FiniteDist.uniform (EndpointSpace dimension modulus)).eventMass
      (fun endpoint => ∑ index, endpoint index = 0) = 1 / (modulus : ℝ) := by
  unfold FiniteDist.eventMass
  rw [← uniform_zeroSum_mass dimension modulus]
  apply Finset.sum_congr rfl
  intro endpoint _
  by_cases h : (∑ index, endpoint index) = 0 <;> simp [h]

theorem uniform_condition_eq_zeroSum (dimension modulus : ℕ) [NeZero modulus] :
    (FiniteDist.uniform (EndpointSpace dimension modulus)).condition
      (fun endpoint => ∑ index, endpoint index = 0)
      (by
        rw [uniform_eventMass_zeroSum]
        exact one_div_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne modulus)))) =
      uniformZeroSum dimension modulus := by
  ext endpoint
  rw [uniformZeroSum_eq_conditional_weight]
  simp only [FiniteDist.condition, uniform_eventMass_zeroSum]
  by_cases h : (∑ index, endpoint index) = 0 <;> simp [h]

/-- The clipping/charge bound with the actual uniform hyperplane target. -/
theorem bounded_zeroSum_conditioning {Core : Type*} [Fintype Core]
    (dimension modulus : ℕ) [NeZero modulus]
    (proposal : FiniteDist Core) (weight : Core → ℝ)
    (channel : Core → FiniteDist (EndpointSpace dimension modulus))
    (ambientError clipError : ℝ)
    (hambient : (∑ endpoint, |endpointMass proposal weight channel endpoint -
      (FiniteDist.uniform (EndpointSpace dimension modulus)).weight endpoint|) ≤
        2 * ambientError)
    (hclip : clippingLoss proposal weight ≤ clipError)
    (hsmall : 2 * ambientError + clipError ≤ 1 / (2 * (modulus : ℝ))) :
    ∃ hpositive : 0 < chargedMass proposal weight channel
        (fun endpoint => ∑ index, endpoint index = 0),
      1 / (2 * (modulus : ℝ)) ≤ chargedMass proposal weight channel
        (fun endpoint => ∑ index, endpoint index = 0) ∧
      (positiveEndpointLaw proposal weight channel
        (fun endpoint => ∑ index, endpoint index = 0) hpositive).totalVariation
          (uniformZeroSum dimension modulus) ≤
            2 * (modulus : ℝ) * (2 * ambientError + clipError) := by
  have hq : (0 : ℝ) < modulus := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne modulus)
  have h := bounded_positive_conditioning proposal weight channel
    (FiniteDist.uniform (EndpointSpace dimension modulus))
    (fun endpoint => ∑ index, endpoint index = 0) (modulus : ℝ)
    ambientError clipError hq (uniform_eventMass_zeroSum dimension modulus)
    hambient hclip hsmall
  simpa only [uniform_condition_eq_zeroSum] using h

/-- Event probabilities under an actual deterministic pushforward. -/
theorem eventMass_map {Seed Output : Type*} [Fintype Seed] [Fintype Output]
    (law : FiniteDist Seed) (output : Seed → Output) (event : Output → Prop) :
    (law.map output).eventMass event =
      ∑ seed, if event (output seed) then law.weight seed else 0 := by
  unfold FiniteDist.eventMass
  simp only [FiniteDist.map_weight]
  trans ∑ endpoint, ∑ seed,
    if output seed = endpoint then (if event endpoint then law.weight seed else 0) else 0
  · apply Finset.sum_congr rfl
    intro endpoint _
    by_cases h : event endpoint <;> simp [h]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro seed _
    simp

/-- Pointwise public charge implies an exact zero-or-one event probability
even when the hidden seed coordinates are correlated. -/
theorem eventMass_of_pointwise_charge {Seed Output : Type*}
    [Fintype Seed] [Fintype Output]
    (law : FiniteDist Seed) (output : Seed → Output) (event : Output → Prop)
    (publicCharge : Prop) (hcharge : ∀ seed, event (output seed) ↔ publicCharge) :
    (law.map output).eventMass event = if publicCharge then 1 else 0 := by
  rw [eventMass_map]
  by_cases h : publicCharge
  · have hevent seed : event (output seed) := (hcharge seed).2 h
    simp [hevent, h, law.sum_one]
  · have hevent seed : ¬event (output seed) := by simpa only [hcharge seed] using h
    simp [hevent, h]

end

end CurrentAFT
