import AFT.MixedTransfer

/-! # Exact coordinate refresh operators on finite product probability laws -/

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]

/-- The actual deterministic finite law. -/
noncomputable def pointLaw (value : Color) : FiniteDist Color where
  weight color := if value = color then 1 else 0
  nonneg color := by split_ifs <;> norm_num
  sum_one := by simp

omit [Fintype Slot] in
@[simp] theorem pointLaw_expectation (value : Color) (function : Color → ℝ) :
    (pointLaw value).expectation function = function value := by
  simp [FiniteDist.expectation, pointLaw]

omit [Fintype Slot] in
@[simp] theorem pointLaw_mix (value : Color) (kernel : Color → FiniteDist Color) :
    (pointLaw value).mix kernel = kernel value := by
  ext color
  simp [FiniteDist.mix_weight, pointLaw]

omit [Fintype Slot] in
@[simp] theorem mix_pointLaw (law : FiniteDist Color) : law.mix pointLaw = law := by
  ext color
  simp [FiniteDist.mix_weight, pointLaw]

/-- Independent coordinate transitions preserve an exact product law. -/
theorem independent_mix (reference : Slot → FiniteDist Color)
    (kernel : Slot → Color → FiniteDist Color) :
    (FiniteDist.independent reference).mix (fun word => FiniteDist.independent (fun slot => kernel slot (word slot))) =
      FiniteDist.independent (fun slot => (reference slot).mix (kernel slot)) := by
  ext word
  simp only [FiniteDist.mix_weight, FiniteDist.independent, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun slot color => (reference slot).weight color * (kernel slot color).weight (word slot))).symm

/-- Resample precisely the indicated coordinates from their product laws. -/
noncomputable def refreshLaw (reference : Slot → FiniteDist Color) (resampled : Finset Slot)
    (word : Slot → Color) : FiniteDist (Slot → Color) :=
  FiniteDist.independent (fun slot => if slot ∈ resampled then reference slot else pointLaw (word slot))

/-- The concrete partial integration operator. -/
noncomputable def refresh (reference : Slot → FiniteDist Color) (resampled : Finset Slot)
    (function : (Slot → Color) → ℝ) (word : Slot → Color) : ℝ :=
  (refreshLaw reference resampled word).expectation function

/-- Coordinate refresh has an exact union semigroup law. -/
theorem refreshLaw_mix (reference : Slot → FiniteDist Color) (first second : Finset Slot)
    (word : Slot → Color) :
    (refreshLaw reference first word).mix (refreshLaw reference second) =
      refreshLaw reference (first ∪ second) word := by
  unfold refreshLaw
  rw [independent_mix _ (fun slot color => if slot ∈ second then reference slot else pointLaw color)]
  congr 1
  funext slot
  by_cases hf : slot ∈ first <;> by_cases hs : slot ∈ second <;> simp [hf, hs]

omit [Fintype Slot] in
/-- Finite mixtures integrate by the exact iterated expectation formula. -/
theorem expectation_mix (law : FiniteDist Color) (kernel : Color → FiniteDist Color)
    (function : Color → ℝ) :
    (law.mix kernel).expectation function = law.expectation (fun value => (kernel value).expectation function) := by
  unfold FiniteDist.expectation
  simp only [FiniteDist.mix_weight, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro value _
  apply Finset.sum_congr rfl
  intro color _
  ring

/-- Partial integrations commute and repeated refreshes are idempotent. -/
theorem refresh_refresh (reference : Slot → FiniteDist Color) (first second : Finset Slot)
    (function : (Slot → Color) → ℝ) (word : Slot → Color) :
    refresh reference first (refresh reference second function) word =
      refresh reference (first ∪ second) function word := by
  unfold refresh
  rw [← expectation_mix, refreshLaw_mix]

/-- Refreshing independent input leaves its actual distribution unchanged. -/
theorem independent_mix_refresh (reference : Slot → FiniteDist Color) (resampled : Finset Slot) :
    (FiniteDist.independent reference).mix (refreshLaw reference resampled) = FiniteDist.independent reference := by
  unfold refreshLaw
  rw [independent_mix _ (fun slot color => if slot ∈ resampled then reference slot else pointLaw color)]
  congr 1
  funext slot
  by_cases hs : slot ∈ resampled <;> simp [hs]

/-- Partial integration leaves the complete expectation unchanged. -/
theorem expectation_refresh (reference : Slot → FiniteDist Color) (resampled : Finset Slot)
    (function : (Slot → Color) → ℝ) :
    (FiniteDist.independent reference).expectation (refresh reference resampled function) =
      (FiniteDist.independent reference).expectation function := by
  unfold refresh
  rw [← expectation_mix, independent_mix_refresh]

/-- Coordinatewise deterministic maps preserve actual finite product laws. -/
theorem independent_map_coordinates (reference : Slot → FiniteDist Color) (function : Slot → Color → Color) :
    (FiniteDist.independent reference).map (fun word slot => function slot (word slot)) =
      FiniteDist.independent (fun slot => (reference slot).map (function slot)) := by
  ext target
  simp only [FiniteDist.map_weight, FiniteDist.independent]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro word _
  rw [Finset.prod_ite_zero]
  have heq : (∀ slot ∈ (Finset.univ : Finset Slot), function slot (word slot) = target slot) ↔
      (fun slot => function slot (word slot)) = target := by
    simp only [Finset.mem_univ, forall_true_left, funext_iff]
  simp only [heq]

omit [Fintype Slot] in
@[simp] theorem map_identity (law : FiniteDist Color) : law.map id = law := by
  ext color
  exact FiniteDist.map_equiv_weight law (Equiv.refl Color) color

omit [Fintype Slot] in
@[simp] theorem map_constant (law : FiniteDist Color) (value : Color) :
    law.map (fun _ => value) = pointLaw value := by
  ext color
  by_cases h : value = color
  · simp [FiniteDist.map_weight, pointLaw, h, law.sum_one]
  · simp [FiniteDist.map_weight, pointLaw, h]

/-- The refresh law is exactly the product draw with the complementary
coordinates frozen, as used by the full mixed-fiber definition. -/
theorem refreshLaw_eq_map (reference : Slot → FiniteDist Color) (resampled : Finset Slot)
    (word : Slot → Color) :
    refreshLaw reference resampled word =
      (FiniteDist.independent reference).map (MixedKernel.freeze resampledᶜ word) := by
  have hfreeze : MixedKernel.freeze resampledᶜ word =
      (fun integrated slot => (fun color => if slot ∈ resampled then color else word slot) (integrated slot)) := by
    funext integrated slot
    by_cases hs : slot ∈ resampled <;> simp [MixedKernel.freeze, hs]
  rw [hfreeze, independent_map_coordinates reference
    (fun slot color => if slot ∈ resampled then color else word slot)]
  unfold refreshLaw
  congr 1
  funext slot
  by_cases hs : slot ∈ resampled
  · simp only [hs, if_true]
    exact (map_identity _).symm
  · simp only [hs, if_false]
    exact (map_constant _ _).symm

/-- Exact partial integration as the genuine frozen-coordinate expectation. -/
theorem refresh_eq_freeze (reference : Slot → FiniteDist Color) (resampled : Finset Slot)
    (function : (Slot → Color) → ℝ) (word : Slot → Color) :
    refresh reference resampled function word =
      (FiniteDist.independent reference).expectation (fun integrated =>
        function (MixedKernel.freeze resampledᶜ word integrated)) := by
  unfold refresh
  rw [refreshLaw_eq_map, FiniteDist.expectation_map]
  rfl

/-- Refresh preserves exact dependence on the remaining coordinates. -/
theorem refresh_dependsOn (reference : Slot → FiniteDist Color) (resampled selected : Finset Slot)
    (function : (Slot → Color) → ℝ) (hdepends : Hoeffding.DependsOn selected function) :
    Hoeffding.DependsOn (selected \ resampled) (refresh reference resampled function) := by
  intro first second hequal
  simp only [refresh_eq_freeze, FiniteDist.expectation]
  apply Finset.sum_congr rfl
  intro integrated _
  congr 1
  apply hdepends
  intro slot hslot
  by_cases hs : slot ∈ resampled
  · simp [MixedKernel.freeze, hs]
  · simp only [MixedKernel.freeze, Finset.mem_compl, hs, not_false_eq_true, if_true]
    exact hequal slot (Finset.mem_sdiff.mpr ⟨hslot, hs⟩)

/-- A factor independent of the refreshed coordinates passes through the
actual partial integration unchanged. -/
theorem refresh_mul_fixed (reference : Slot → FiniteDist Color) (resampled : Finset Slot)
    (first second : (Slot → Color) → ℝ) (hfixed : Hoeffding.DependsOn resampledᶜ second)
    (word : Slot → Color) :
    refresh reference resampled (fun values => first values * second values) word =
      refresh reference resampled first word * second word := by
  have hs (integrated : Slot → Color) : second (MixedKernel.freeze resampledᶜ word integrated) = second word := by
    apply hfixed
    intro slot hslot
    simp [MixedKernel.freeze, hslot]
  simp only [refresh_eq_freeze, hs, FiniteDist.expectation, Finset.sum_mul, mul_assoc]

end AFT.CanonicalMoments
