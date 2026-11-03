import CurrentAFT.ChargedEndpoint
import CurrentAFT.PublicCore

/-! # Public conditioning on a nonempty finite endpoint index set -/
namespace CurrentAFT.FiniteZeroSum
open AFT
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable {Index : Type*} [Fintype Index] [DecidableEq Index] [Nonempty Index] (modulus : ℕ) [NeZero modulus]

def indexEquiv : Index ≃ Fin (Fintype.card Index - 1 + 1) :=
  (Fintype.equivFin Index).trans (finCongr (by have := Fintype.card_pos (α := Index); omega))

def wordEquiv : (Index → ZMod modulus) ≃ EndpointSpace (Fintype.card Index - 1) modulus :=
  Equiv.arrowCongr (indexEquiv (Index := Index)) (Equiv.refl _)

omit [NeZero modulus] [DecidableEq Index] in
theorem wordEquiv_sum (word : Index → ZMod modulus) :
    ∑ index, wordEquiv modulus word index = ∑ index, word index :=
  Equiv.sum_comp (indexEquiv (Index := Index)).symm word

theorem uniform_charge_mass :
    (FiniteDist.uniform (Index → ZMod modulus)).eventMass (fun word => ∑ index, word index = 0) =
      1 / (modulus : ℝ) := by
  have h := uniform_eventMass_zeroSum (Fintype.card Index - 1) modulus
  rw [← FiniteDist.uniform_map_equiv (wordEquiv (Index := Index) modulus), eventMass_map] at h
  refine Eq.trans ?_ h
  unfold FiniteDist.eventMass
  apply Finset.sum_congr rfl
  intro word _
  rw [wordEquiv_sum]

/-- Ambient uniformity conditioned on exactly the zero-sum event. -/
def uniformLaw : FiniteDist (Index → ZMod modulus) :=
  (FiniteDist.uniform (Index → ZMod modulus)).condition (fun word => ∑ index, word index = 0)
    (by rw [uniform_charge_mass]; exact one_div_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne modulus))))

theorem uniformLaw_weight (word : Index → ZMod modulus) :
    (uniformLaw modulus).weight word =
      if ∑ index, word index = 0 then (modulus : ℝ) / (Fintype.card (Index → ZMod modulus) : ℝ) else 0 := by
  by_cases hzero : (∑ index, word index) = 0 <;>
    simp [uniformLaw, FiniteDist.condition, uniform_charge_mass, FiniteDist.uniform_weight,
      hzero, div_eq_mul_inv, mul_comm]

/-- The exact publicly conditioned law and its error, for the actual
finite endpoint type, without a successor-dimension cast. -/
theorem bounded_public_conditioning {Core : Type*} [Fintype Core]
    (proposal : FiniteDist Core) (weight : Core → ℝ) (channel : Core → FiniteDist (Index → ZMod modulus))
    (publicCharge : Core → Prop)
    (hcharge : ∀ core, (channel core).eventMass (fun word => ∑ index, word index = 0) =
      if publicCharge core then 1 else 0)
    (ambientError clipError : ℝ)
    (hambient : (∑ word, |endpointMass proposal weight channel word -
      (FiniteDist.uniform (Index → ZMod modulus)).weight word|) ≤ 2 * ambientError)
    (hclip : clippingLoss proposal weight ≤ clipError)
    (hsmall : 2 * ambientError + clipError ≤ 1 / (2 * (modulus : ℝ))) :
    ∃ hpositive : 0 < publicCoreMass proposal weight publicCharge,
      1 / (2 * (modulus : ℝ)) ≤ publicCoreMass proposal weight publicCharge ∧
      ((positivePublicCoreLaw proposal weight publicCharge hpositive).mix channel).totalVariation
        (uniformLaw modulus) ≤ 2 * (modulus : ℝ) * (2 * ambientError + clipError) := by
  obtain ⟨hpositive, hlower, herror⟩ := bounded_positive_conditioning proposal weight channel
    (FiniteDist.uniform (Index → ZMod modulus)) (fun word => ∑ index, word index = 0) modulus
    ambientError clipError (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne modulus)))
    (uniform_charge_mass modulus) hambient hclip hsmall
  have hequal := chargedMass_eq_publicCoreMass proposal weight channel
    (fun word => ∑ index, word index = 0) publicCharge hcharge
  have hcore : 0 < publicCoreMass proposal weight publicCharge := by rwa [hequal] at hpositive
  refine ⟨hcore, ?_, ?_⟩
  · rwa [hequal] at hlower
  · rw [positivePublicCoreLaw_mix proposal weight channel
      (fun word => ∑ index, word index = 0) publicCharge hcharge hcore]
    exact herror

end
end CurrentAFT.FiniteZeroSum
