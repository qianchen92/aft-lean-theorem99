import AFT.Charge
import AFT.CanonicalVariance
import AFT.RootSlice

/-! # Exact arbitrary-coordinate marginals of the actual center charge slice -/

namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Slot G : Type*} [Fintype Slot] [Fintype G] [AddCommGroup G]

/-- The finite product's charge probability, for any actual coordinate type. -/
theorem independent_sum_eventMass (center : FiniteDist G) (required : G) :
    (independent (fun _ : Slot => center)).eventMass (fun word => ∑ slot, word slot = required) =
      (center.sumLaw (Fintype.card Slot)).weight required := by
  let e := (Fintype.equivFin Slot).symm
  have he := CanonicalMoments.independent_equiv_expectation e center
    (fun word => if (∑ slot, word slot) = required then 1 else 0)
  have hs (word : Slot → G) : (∑ slot, (word ∘ e) slot) = ∑ slot, word slot := e.sum_comp word
  simp only [hs] at he
  have hm := congrArg (fun law : FiniteDist G => law.weight required)
    (independent_sum_map center (Fintype.card Slot))
  unfold eventMass
  unfold expectation at he
  simp only [mul_ite, mul_one, mul_zero] at he
  apply he.trans
  simp only [map_weight] at hm
  apply Eq.trans ?_ hm
  apply Finset.sum_congr (by ext; simp)
  intro word _
  rfl

def chargeWordLaw (center : FiniteDist G) (required : G)
    (hpos : 0 < (center.sumLaw (Fintype.card Slot)).weight required) : FiniteDist (Slot → G) :=
  (independent (fun _ : Slot => center)).condition (fun word => ∑ slot, word slot = required)
    (by rw [independent_sum_eventMass]; exact hpos)

/-- Integrating every unexposed center gives the exact remaining sum law.
This is a marginal of one full charge slice, for arbitrary chosen coordinates. -/
theorem chargeWordLaw_restriction_expectation (center : FiniteDist G) (required : G)
    (hpos : 0 < (center.sumLaw (Fintype.card Slot)).weight required)
    (selected : Finset Slot) (function : (selected → G) → ℝ) :
    (chargeWordLaw center required hpos).expectation (fun word => function (fun slot => word slot)) =
      ∑ chosen : selected → G,
        (∏ slot : selected, center.weight (chosen slot)) * function chosen *
          (center.sumLaw (Fintype.card Slot - selected.card)).weight (required - ∑ slot, chosen slot) /
            (center.sumLaw (Fintype.card Slot)).weight required := by
  let split := Equiv.piEquivPiSubtypeProd (fun slot => slot ∈ selected) (fun _ : Slot => G)
  unfold expectation chargeWordLaw condition
  change (∑ word : Slot → G, (if (∑ slot, word slot) = required then
    ∏ slot, center.weight (word slot) else 0) /
      (independent (fun _ : Slot => center)).eventMass (fun word => ∑ slot, word slot = required) *
        function (fun slot => word slot)) = _
  rw [independent_sum_eventMass]
  rw [← split.symm.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro chosen _
  have hweight (rest : {slot : Slot // slot ∉ selected} → G) :
      (∏ slot, center.weight (split.symm (chosen, rest) slot)) =
        (∏ slot : selected, center.weight (chosen slot)) *
          ∏ slot : {slot : Slot // slot ∉ selected}, center.weight (rest slot) := by
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun slot => slot ∈ selected)]
    apply congrArg₂ (· * ·)
    · apply Finset.prod_congr (by ext; simp)
      intro slot _
      change center.weight (if h : (slot : Slot) ∈ selected then chosen ⟨slot, h⟩ else rest ⟨slot, h⟩) = _
      simp only [dif_pos slot.property]
    · apply Finset.prod_congr (by ext; simp)
      intro slot _
      change center.weight (if h : (slot : Slot) ∈ selected then chosen ⟨slot, h⟩ else rest ⟨slot, h⟩) = _
      simp only [dif_neg slot.property]
  have hsum (rest : {slot : Slot // slot ∉ selected} → G) :
      (∑ slot, split.symm (chosen, rest) slot) =
        (∑ slot : selected, chosen slot) + ∑ slot : {slot : Slot // slot ∉ selected}, rest slot := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun slot => slot ∈ selected)]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr (by ext; simp)
      intro slot _
      change (if h : (slot : Slot) ∈ selected then chosen ⟨slot, h⟩ else rest ⟨slot, h⟩) = _
      simp only [dif_pos slot.property]
    · apply Finset.sum_congr (by ext; simp)
      intro slot _
      change (if h : (slot : Slot) ∈ selected then chosen ⟨slot, h⟩ else rest ⟨slot, h⟩) = _
      simp only [dif_neg slot.property]
  have hrestriction (rest : {slot : Slot // slot ∉ selected} → G) :
      (fun slot : selected => split.symm (chosen, rest) slot) = chosen := by
    funext slot
    change (if h : (slot : Slot) ∈ selected then chosen ⟨slot, h⟩ else rest ⟨slot, h⟩) = _
    simp only [dif_pos slot.property]
  have hm := independent_sum_eventMass (Slot := {slot : Slot // slot ∉ selected}) center
    (required - ∑ slot, chosen slot)
  have hcard : Fintype.card {slot : Slot // slot ∉ selected} = Fintype.card Slot - selected.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe]
  rw [hcard] at hm
  unfold eventMass independent at hm
  simp_rw [hweight, hsum, hrestriction]
  rw [← hm, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr (by ext; simp)
  intro rest _
  have hevent : (∑ slot : selected, chosen slot) + (∑ slot : {slot : Slot // slot ∉ selected}, rest slot) = required ↔
      (∑ slot : {slot : Slot // slot ∉ selected}, rest slot) = required - ∑ slot : selected, chosen slot := by
    rw [eq_sub_iff_add_eq, add_comm]
  rw [hevent]
  split_ifs <;> ring


/-- Signed local expectation transfer on the very same full charge proposal. -/
theorem chargeWordLaw_restriction_deviation (center : FiniteDist G) (required : G)
    (hpos : 0 < (center.sumLaw (Fintype.card Slot)).weight required)
    (selected : Finset Slot) (function : (selected → G) → ℝ) (error : ℝ)
    (hratio : ∀ partialCharge, |(center.sumLaw (Fintype.card Slot - selected.card)).weight
      (required - partialCharge) / (center.sumLaw (Fintype.card Slot)).weight required - 1| ≤ error) :
    |(chargeWordLaw center required hpos).expectation (fun word => function (fun slot => word slot)) -
      (independent (fun _ : Slot => center)).expectation (fun word => function (fun slot => word slot))| ≤
      error * (independent (fun _ : Slot => center)).expectation (fun word => |function (fun slot => word slot)|) := by
  rw [chargeWordLaw_restriction_expectation,
    LocalTensors.independent_restriction_expectation (fun _ : Slot => center) selected function,
    LocalTensors.independent_restriction_expectation (fun _ : Slot => center) selected (fun chosen => |function chosen|)]
  change |(∑ chosen, (∏ slot, center.weight (chosen slot)) * function chosen *
      (center.sumLaw (Fintype.card Slot - selected.card)).weight (required - ∑ slot, chosen slot) /
        (center.sumLaw (Fintype.card Slot)).weight required) -
      ∑ chosen, (∏ slot, center.weight (chosen slot)) * function chosen| ≤
    error * ∑ chosen, (∏ slot, center.weight (chosen slot)) * |function chosen|
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro chosen _
  have hf : (∏ slot : selected, center.weight (chosen slot)) * function chosen *
      (center.sumLaw (Fintype.card Slot - selected.card)).weight (required - ∑ slot, chosen slot) /
        (center.sumLaw (Fintype.card Slot)).weight required -
      (∏ slot : selected, center.weight (chosen slot)) * function chosen =
    (∏ slot : selected, center.weight (chosen slot)) * function chosen *
      ((center.sumLaw (Fintype.card Slot - selected.card)).weight (required - ∑ slot, chosen slot) /
        (center.sumLaw (Fintype.card Slot)).weight required - 1) := by ring
  rw [hf, abs_mul, abs_mul, abs_of_nonneg (Finset.prod_nonneg fun slot _ => center.nonneg (chosen slot))]
  exact (mul_le_mul_of_nonneg_left (hratio _) (mul_nonneg (Finset.prod_nonneg fun slot _ => center.nonneg (chosen slot)) (abs_nonneg _))).trans_eq (by ring)

theorem chargeWordLaw_local_deviation (center : FiniteDist G) (required : G)
    (hpos : 0 < (center.sumLaw (Fintype.card Slot)).weight required)
    (selected : Finset Slot) (function : (Slot → G) → ℝ)
    (hdepends : Hoeffding.DependsOn selected function) (error : ℝ)
    (hratio : ∀ partialCharge, |(center.sumLaw (Fintype.card Slot - selected.card)).weight
      (required - partialCharge) / (center.sumLaw (Fintype.card Slot)).weight required - 1| ≤ error) :
    |(chargeWordLaw center required hpos).expectation function -
      (independent (fun _ : Slot => center)).expectation function| ≤
      error * (independent (fun _ : Slot => center)).expectation (fun word => |function word|) := by
  let localFunction (chosen : selected → G) :=
    function (fun slot => if hs : slot ∈ selected then chosen ⟨slot, hs⟩ else 0)
  have heq : (fun word : Slot → G => localFunction (fun slot => word slot)) = function := by
    funext word
    apply hdepends
    intro slot hs
    simp only [dif_pos hs]
  have hh := chargeWordLaw_restriction_deviation center required hpos selected localFunction error hratio
  simp_rw [show ∀ word : Slot → G, localFunction (fun slot => word slot) = function word from congrFun heq] at hh
  exact hh

end
end AFT.FiniteDist
