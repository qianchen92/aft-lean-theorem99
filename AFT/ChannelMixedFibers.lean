import AFT.MixedKernel
import AFT.SignedChannelFibers

/-! # Exact one-coordinate fibers of finite product output channels -/

namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color] [DecidableEq Slot]

/-- Freeze precisely one actual coordinate and integrate all remaining
coordinates under their original product reference. -/
theorem fiberSq_singleton_split (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (slot : Slot) (values : Slot → Color) :
    fiberSq reference kernel {slot} values =
      (FiniteDist.independent (fun other : {other : Slot // other ≠ slot} => reference other)).l2Sq
        (fun rest => kernel ((Equiv.funSplitAt slot Color).symm (values slot, rest))) := by
  cases Subsingleton.elim (inferInstance : DecidableEq Slot) (Classical.decEq Slot)
  unfold fiberSq FiniteDist.l2Sq
  rw [FiniteDist.expectation_independent_split _ slot]
  apply Finset.sum_congr rfl
  intro rest _
  have heq (color : Color) : freeze {slot} values ((Equiv.funSplitAt slot Color).symm (color, rest)) =
      (Equiv.funSplitAt slot Color).symm (values slot, rest) := by
    funext other
    by_cases ho : other = slot
    · subst other
      simp [freeze, Equiv.funSplitAt, Equiv.piSplitAt]
    · simp [freeze, ho, Equiv.funSplitAt, Equiv.piSplitAt]
  simp only [heq, ← Finset.sum_mul, FiniteDist.sum_one, one_mul]
  rfl

/-- Exact product density after splitting off a specified coordinate. -/
theorem independent_split_weight (reference : Slot → FiniteDist Color) (slot : Slot)
    (color : Color) (rest : {other : Slot // other ≠ slot} → Color) :
    (FiniteDist.independent reference).weight ((Equiv.funSplitAt slot Color).symm (color, rest)) =
      (reference slot).weight color *
        (FiniteDist.independent (fun other : {other : Slot // other ≠ slot} => reference other)).weight rest := by
  change (∏ other, (reference other).weight ((Equiv.funSplitAt slot Color).symm (color, rest) other)) = _
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ slot)]
  have hself : (Equiv.funSplitAt slot Color).symm (color, rest) slot = color := by
    simp [Equiv.funSplitAt, Equiv.piSplitAt]
  rw [hself]
  congr 1
  rw [Finset.prod_subtype (Finset.univ.erase slot) (p := fun other : Slot => other ≠ slot)
    (by intro other; simp)]
  change (∏ other : {other : Slot // other ≠ slot},
    (reference other).weight ((Equiv.funSplitAt slot Color).symm (color, rest) other)) =
    ∏ other : {other : Slot // other ≠ slot}, (reference other).weight (rest other)
  apply Finset.prod_congr rfl
  intro other _
  simp [Equiv.funSplitAt, Equiv.piSplitAt, other.property]

/-- A singleton marginal is the sum over exactly the remaining outputs. -/
theorem singleton_slice_sum (mass : (Slot → Color) → ℝ) (slot : Slot) (color : Color) :
    (∑ word, if word slot = color then mass word else 0) =
      ∑ rest : {other : Slot // other ≠ slot} → Color,
        mass ((Equiv.funSplitAt slot Color).symm (color, rest)) := by
  rw [← (Equiv.funSplitAt slot Color).symm.sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro rest _
  simp [Equiv.funSplitAt, Equiv.piSplitAt]

/-- The normalized actual signed channel, before canonical projection. -/
def channelDensity {Input : Type*} [Fintype Input]
    (input : FiniteDist Input) (reference : Slot → FiniteDist Color)
    (kernel : Input → (Slot → Color) → ℝ) (score : Input → ℝ) (word : Slot → Color) : ℝ :=
  (∑ point, input.weight point * score point * kernel point word) /
    (FiniteDist.independent reference).weight word

/-- A positive singleton marginal gives the sharp fixed-one fiber bound.
In particular the density ceiling is not squared. -/
theorem channelDensity_singleton_square_le {Input : Type*} [Fintype Input]
    (input : FiniteDist Input) (reference : Slot → FiniteDist Color)
    (kernel : Input → (Slot → Color) → ℝ) (densityBound marginalBound scoreBound : ℝ)
    (href : ∀ slot color, 0 < (reference slot).weight color)
    (hD : 0 ≤ densityBound) (hL : 0 ≤ scoreBound)
    (hkernel : ∀ point output, 0 ≤ kernel point output)
    (hdensity : ∀ output, (∑ point, input.weight point * kernel point output) ≤
      densityBound * (FiniteDist.independent reference).weight output)
    (hmarginal : ∀ slot color,
      (∑ word, if word slot = color then ∑ point, input.weight point * kernel point word else 0) ≤
        marginalBound * (reference slot).weight color)
    (score : Input → ℝ) (hscore : ∀ point, |score point| ≤ scoreBound)
    (slot : Slot) (values : Slot → Color) :
    fiberSq reference (channelDensity input reference kernel score) {slot} values ≤
      densityBound * marginalBound * scoreBound ^ 2 := by
  rw [fiberSq_singleton_split]
  have hh := signedChannel_fixed_fiber_square_le input
    (FiniteDist.independent (fun other : {other : Slot // other ≠ slot} => reference other))
    (fun point rest => kernel point ((Equiv.funSplitAt slot Color).symm (values slot, rest)))
    ((reference slot).weight (values slot)) densityBound marginalBound scoreBound
    (href slot (values slot))
    (fun word => Finset.prod_pos fun other _ => href other (word other)) hD hL
    (fun point rest => hkernel point _) (fun rest => by
      simpa only [independent_split_weight] using hdensity ((Equiv.funSplitAt slot Color).symm (values slot, rest)))
    (by simpa only [singleton_slice_sum] using hmarginal slot (values slot)) score hscore
  simpa only [channelDensity, independent_split_weight] using hh

/-- The same one-fixed estimate leaves any old remaining joint fiber
inside its original Hilbert norm. -/
theorem channelDensity_singleton_hilbert_square_le {Input Fiber : Type*}
    [Fintype Input] [Fintype Fiber]
    (input : FiniteDist Input) (reference : Slot → FiniteDist Color) (fiber : FiniteDist Fiber)
    (kernel : Input → (Slot → Color) → ℝ) (densityBound marginalBound squareBound : ℝ)
    (href : ∀ slot color, 0 < (reference slot).weight color)
    (hD : 0 ≤ densityBound) (hL : 0 ≤ squareBound)
    (hkernel : ∀ point output, 0 ≤ kernel point output)
    (hdensity : ∀ output, (∑ point, input.weight point * kernel point output) ≤
      densityBound * (FiniteDist.independent reference).weight output)
    (hmarginal : ∀ slot color,
      (∑ word, if word slot = color then ∑ point, input.weight point * kernel point word else 0) ≤
        marginalBound * (reference slot).weight color)
    (score : Input → Fiber → ℝ) (hscore : ∀ point, fiber.l2Sq (score point) ≤ squareBound)
    (slot : Slot) (color : Color) :
    (FiniteDist.independent (fun other : {other : Slot // other ≠ slot} => reference other)).expectation
      (fun rest => fiber.l2Sq (fun remaining => channelDensity input reference kernel
        (fun point => score point remaining) ((Equiv.funSplitAt slot Color).symm (color,rest)))) ≤
      densityBound * marginalBound * squareBound := by
  have hh := signedChannel_fixed_hilbert_square_le input
    (FiniteDist.independent (fun other : {other : Slot // other ≠ slot} => reference other)) fiber
    (fun point rest => kernel point ((Equiv.funSplitAt slot Color).symm (color, rest)))
    ((reference slot).weight color) densityBound marginalBound squareBound
    (href slot color)
    (fun word => Finset.prod_pos fun other _ => href other (word other)) hD hL
    (fun point rest => hkernel point _) (fun rest => by
      simpa only [independent_split_weight] using hdensity ((Equiv.funSplitAt slot Color).symm (color, rest)))
    (by simpa only [singleton_slice_sum] using hmarginal slot color) score hscore
  simpa only [channelDensity, independent_split_weight] using hh

end
end AFT.MixedKernel
