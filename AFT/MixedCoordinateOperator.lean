import AFT.MixedKernel

/-! # A genuine coordinate operator on every mixed input fiber

The operator acts on the literal joint kernel. Grouping fixed-coordinate
sets in pairs gives a dimension-free bound on the full mixed activity.
-/

namespace AFT.MixedKernel

open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {Slot Color : Type*} [Fintype Slot] [Fintype Color] [DecidableEq Slot]

/-- Apply a profile operator in one actual input coordinate. -/
def partialInputOperator (slot : Slot) (operator : Module.End ℝ (Color → ℝ))
    (primary : Color → ℝ) (kernel : (Slot → Color) → ℝ) : (Slot → Color) → ℝ :=
  fun word => operator (fun input => primary input * kernel (Function.update word slot input))
    (word slot) / primary (word slot)

private def splitWord (slot : Slot) (color : Color) (rest : {j : Slot // j ≠ slot} → Color) : Slot → Color :=
  (Equiv.funSplitAt slot Color).symm (color, rest)

omit [Fintype Slot] [Fintype Color] in
private theorem splitWord_self (slot : Slot) (color : Color) (rest : {j : Slot // j ≠ slot} → Color) :
    splitWord slot color rest slot = color := by simp [splitWord, Equiv.funSplitAt, Equiv.piSplitAt]

omit [Fintype Slot] [Fintype Color] in
private theorem splitWord_ne (slot : Slot) (color : Color) (rest : {j : Slot // j ≠ slot} → Color)
    (j : Slot) (hj : j ≠ slot) : splitWord slot color rest j = rest ⟨j, hj⟩ := by
  simp [splitWord, Equiv.funSplitAt, Equiv.piSplitAt, hj]

private def slicedKernel (slot : Slot) (fixed : Finset Slot) (values : Slot → Color)
    (kernel : (Slot → Color) → ℝ) : Color → ({j : Slot // j ≠ slot} → Color) → ℝ :=
  fun color rest => kernel (freeze fixed values (splitWord slot color rest))

omit [Fintype Slot] [Fintype Color] in
private theorem freeze_split_update (slot : Slot) (fixed : Finset Slot) (hslot : slot ∉ fixed)
    (values : Slot → Color) (color next : Color) (rest : {j : Slot // j ≠ slot} → Color) :
    Function.update (freeze fixed values (splitWord slot color rest)) slot next =
      freeze fixed values (splitWord slot next rest) := by
  funext j
  by_cases hj : j = slot
  · subst j
    simp [freeze, hslot, splitWord_self]
  · simp only [Function.update_of_ne hj, freeze, splitWord_ne slot color rest j hj,
      splitWord_ne slot next rest j hj]

omit [Fintype Slot] [Fintype Color] in
private theorem slicedKernel_operator (slot : Slot) (fixed : Finset Slot) (hslot : slot ∉ fixed)
    (values : Slot → Color) (operator : Module.End ℝ (Color → ℝ))
    (primary : Color → ℝ) (kernel : (Slot → Color) → ℝ) :
    slicedKernel slot fixed values (partialInputOperator slot operator primary kernel) =
      partialProfileOperator operator primary (slicedKernel slot fixed values kernel) := by
  funext color rest
  simp only [slicedKernel, partialInputOperator, partialProfileOperator,
    freeze_split_update slot fixed hslot, freeze, if_neg hslot, splitWord_self]

private theorem slicedKernel_integrated (reference : Slot → FiniteDist Color) (slot : Slot)
    (fixed : Finset Slot) (values : Slot → Color) (kernel : (Slot → Color) → ℝ) :
    integratedFiberNorm (reference slot).weight
      (FiniteDist.independent (fun j : {j : Slot // j ≠ slot} => reference j)).weight
      (slicedKernel slot fixed values kernel) = Real.sqrt (fiberSq reference kernel fixed values) := by
  cases Subsingleton.elim (inferInstance : DecidableEq Slot) (Classical.decEq Slot)
  unfold integratedFiberNorm fiberSq FiniteDist.l2Sq
  rw [FiniteDist.expectation_independent_split _ slot]
  rfl

private theorem fiberSq_insert_split (reference : Slot → FiniteDist Color) (slot : Slot)
    (fixed : Finset Slot) (hslot : slot ∉ fixed) (values : Slot → Color)
    (kernel : (Slot → Color) → ℝ) :
    fiberSq reference kernel (insert slot fixed) values =
      ∑ rest, (FiniteDist.independent (fun j : {j : Slot // j ≠ slot} => reference j)).weight rest *
        slicedKernel slot fixed values kernel (values slot) rest ^ 2 := by
  cases Subsingleton.elim (inferInstance : DecidableEq Slot) (Classical.decEq Slot)
  unfold fiberSq FiniteDist.l2Sq
  rw [FiniteDist.expectation_independent_split _ slot]
  apply Finset.sum_congr rfl
  intro rest _
  have heq (color : Color) : freeze (insert slot fixed) values (splitWord slot color rest) =
      freeze fixed values (splitWord slot (values slot) rest) := by
    funext j
    by_cases hj : j = slot
    · subst j
      simp [freeze, hslot, splitWord_self]
    · simp [freeze, hj, splitWord_ne slot color rest j hj, splitWord_ne slot (values slot) rest j hj]
  dsimp only [splitWord] at heq
  simp only [heq, ← Finset.sum_mul, FiniteDist.sum_one, one_mul]
  rfl

private theorem slicedKernel_fixed_le (reference : Slot → FiniteDist Color) (slot : Slot)
    (fixed : Finset Slot) (hslot : slot ∉ fixed) (values : Slot → Color)
    (kernel : (Slot → Color) → ℝ) :
    fixedFiberNorm (FiniteDist.independent (fun j : {j : Slot // j ≠ slot} => reference j)).weight
      (slicedKernel slot fixed values kernel) ≤ fiberNorm reference kernel (insert slot fixed) := by
  apply (pi_norm_le_iff_of_nonneg (fiberNorm_nonneg _ _ _)).mpr
  intro color
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hf : slicedKernel slot fixed (Function.update values slot color) kernel =
      slicedKernel slot fixed values kernel := by
    funext a rest
    unfold slicedKernel
    congr 1
    funext j
    by_cases hj : j = slot
    · subst j; simp [freeze, hslot]
    · simp [freeze, Function.update_of_ne hj]
  have hh := norm_le_pi_norm (fun values => Real.sqrt (fiberSq reference kernel (insert slot fixed) values))
    (Function.update values slot color)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), fiberSq_insert_split reference slot fixed hslot,
    hf, Function.update_self] at hh
  exact hh

private theorem sqrt_fiberSq_insert_le (reference : Slot → FiniteDist Color) (slot : Slot)
    (fixed : Finset Slot) (hslot : slot ∉ fixed) (values : Slot → Color)
    (kernel : (Slot → Color) → ℝ) :
    Real.sqrt (fiberSq reference kernel (insert slot fixed) values) ≤
      fixedFiberNorm (FiniteDist.independent (fun j : {j : Slot // j ≠ slot} => reference j)).weight
        (slicedKernel slot fixed values kernel) := by
  rw [fiberSq_insert_split reference slot fixed hslot]
  have hh := norm_le_pi_norm (fun color => Real.sqrt (∑ rest,
    (FiniteDist.independent (fun j : {j : Slot // j ≠ slot} => reference j)).weight rest *
      slicedKernel slot fixed values kernel color rest ^ 2)) (values slot)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using hh

/-- The two fibers differing only at the distinguished coordinate obey a
uniform bound, including suprema over every other fixed coordinate. -/
theorem partialInputOperator_fiber_pair_le (reference : Slot → FiniteDist Color) (slot : Slot)
    (operator : Module.End ℝ (Color → ℝ)) (rate constant : ℝ) (hrate : 0 < rate)
    (hconstant : 0 ≤ constant)
    (hoperator : ∀ kernel : Color → ({j : Slot // j ≠ slot} → Color) → ℝ,
      coordinateActivity rate (reference slot).weight
        (FiniteDist.independent (fun j : {j : Slot // j ≠ slot} => reference j)).weight
        (partialProfileOperator operator (reference slot).weight kernel) ≤
      constant * coordinateActivity rate (reference slot).weight
        (FiniteDist.independent (fun j : {j : Slot // j ≠ slot} => reference j)).weight kernel)
    (kernel : (Slot → Color) → ℝ) (fixed : Finset Slot) (hslot : slot ∉ fixed) :
    fiberNorm reference (partialInputOperator slot operator (reference slot).weight kernel) fixed +
      rate * fiberNorm reference (partialInputOperator slot operator (reference slot).weight kernel) (insert slot fixed) ≤
    2 * constant * (fiberNorm reference kernel fixed + rate * fiberNorm reference kernel (insert slot fixed)) := by
  let budget := constant * (fiberNorm reference kernel fixed + rate * fiberNorm reference kernel (insert slot fixed))
  have hbudget : 0 ≤ budget := mul_nonneg hconstant (add_nonneg (fiberNorm_nonneg _ _ _)
    (mul_nonneg hrate.le (fiberNorm_nonneg _ _ _)))
  have hpoint (values : Slot → Color) :
      integratedFiberNorm (reference slot).weight
        (FiniteDist.independent (fun j : {j : Slot // j ≠ slot} => reference j)).weight
        (slicedKernel slot fixed values (partialInputOperator slot operator (reference slot).weight kernel)) +
      rate * fixedFiberNorm
        (FiniteDist.independent (fun j : {j : Slot // j ≠ slot} => reference j)).weight
        (slicedKernel slot fixed values (partialInputOperator slot operator (reference slot).weight kernel)) ≤ budget := by
    have hh := hoperator (slicedKernel slot fixed values kernel)
    rw [← slicedKernel_operator slot fixed hslot] at hh
    have hi := norm_le_pi_norm (fun values => Real.sqrt (fiberSq reference kernel fixed values)) values
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at hi
    change Real.sqrt (fiberSq reference kernel fixed values) ≤ fiberNorm reference kernel fixed at hi
    have hf := slicedKernel_fixed_le reference slot fixed hslot values kernel
    have hinput : coordinateActivity rate (reference slot).weight
        (FiniteDist.independent (fun j : {j : Slot // j ≠ slot} => reference j)).weight
        (slicedKernel slot fixed values kernel) ≤
      rate * (fiberNorm reference kernel fixed + rate * fiberNorm reference kernel (insert slot fixed)) := by
      unfold coordinateActivity
      rw [slicedKernel_integrated]
      nlinarith [mul_le_mul_of_nonneg_left hi hrate.le, mul_le_mul_of_nonneg_left hf (sq_nonneg rate)]
    have hbound := hh.trans (mul_le_mul_of_nonneg_left hinput hconstant)
    apply le_of_mul_le_mul_left (a := rate) _ hrate
    convert hbound using 1 <;> dsimp [coordinateActivity, budget] <;> ring
  have hi : fiberNorm reference (partialInputOperator slot operator (reference slot).weight kernel) fixed ≤ budget := by
    apply (pi_norm_le_iff_of_nonneg hbudget).mpr
    intro values
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hh := hpoint values
    rw [slicedKernel_integrated] at hh
    exact le_trans (le_add_of_nonneg_right (mul_nonneg hrate.le (norm_nonneg _))) hh
  have hf : fiberNorm reference (partialInputOperator slot operator (reference slot).weight kernel) (insert slot fixed) ≤ budget / rate := by
    apply (pi_norm_le_iff_of_nonneg (div_nonneg hbudget hrate.le)).mpr
    intro values
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    apply (le_div_iff₀ hrate).mpr
    have hh := hpoint values
    have hs := sqrt_fiberSq_insert_le reference slot fixed hslot values
      (partialInputOperator slot operator (reference slot).weight kernel)
    have hm := mul_le_mul_of_nonneg_left hs hrate.le
    have hn : 0 ≤ integratedFiberNorm (reference slot).weight
        (FiniteDist.independent (fun j : {j : Slot // j ≠ slot} => reference j)).weight
        (slicedKernel slot fixed values (partialInputOperator slot operator (reference slot).weight kernel)) := Real.sqrt_nonneg _
    nlinarith only [hh, hm, hn]
  have hf' : rate * fiberNorm reference (partialInputOperator slot operator (reference slot).weight kernel) (insert slot fixed) ≤ budget := by
    have hh := (le_div_iff₀ hrate).mp hf
    simpa only [mul_comm] using hh
  dsimp only [budget] at hi hf'
  linarith only [hi, hf']

private theorem sum_fixed_pairs (slot : Slot) (value : Finset Slot → ℝ) :
    (∑ fixed : Finset Slot, value fixed) =
      ∑ fixed ∈ (Finset.univ.erase slot).powerset, (value fixed + value (insert slot fixed)) := by
  have h := Finset.sum_powerset_insert (Finset.notMem_erase slot Finset.univ) value
  rw [Finset.insert_erase (Finset.mem_univ slot), Finset.powerset_univ] at h
  simpa only [Finset.sum_add_distrib] using h

/-- A uniform coordinate mixed bound controls the literal mixed input
activity, with a factor two independent of the palette and slot count. -/
theorem partialInputOperator_activity_le (reference : Slot → FiniteDist Color)
    (rates : Slot → ℝ) (hrates : ∀ slot, 0 ≤ rates slot) (slot : Slot) (hrate : 0 < rates slot)
    (operator : Module.End ℝ (Color → ℝ)) (constant : ℝ) (hconstant : 0 ≤ constant)
    (hoperator : ∀ kernel : Color → ({j : Slot // j ≠ slot} → Color) → ℝ,
      coordinateActivity (rates slot) (reference slot).weight
        (FiniteDist.independent (fun j : {j : Slot // j ≠ slot} => reference j)).weight
        (partialProfileOperator operator (reference slot).weight kernel) ≤
      constant * coordinateActivity (rates slot) (reference slot).weight
        (FiniteDist.independent (fun j : {j : Slot // j ≠ slot} => reference j)).weight kernel)
    (kernel : (Slot → Color) → ℝ) :
    activity rates reference (partialInputOperator slot operator (reference slot).weight kernel) ≤
      (2 * constant) * activity rates reference kernel := by
  unfold activity
  rw [mul_left_comm (2 * constant)]
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun i _ => hrates i)
  rw [sum_fixed_pairs slot, sum_fixed_pairs slot, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro fixed hfixed
  have hslot : slot ∉ fixed := fun h =>
    Finset.notMem_erase slot Finset.univ ((Finset.mem_powerset.mp hfixed) h)
  rw [Finset.prod_insert hslot]
  have hh := mul_le_mul_of_nonneg_left
    (partialInputOperator_fiber_pair_le reference slot operator (rates slot) constant hrate hconstant
      hoperator kernel fixed hslot)
    (Finset.prod_nonneg (s := fixed) (fun i _ => hrates i))
  convert hh using 1 <;> ring

end
end AFT.MixedKernel
