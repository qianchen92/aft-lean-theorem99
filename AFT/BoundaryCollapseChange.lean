import AFT.BoundaryCollapseFibers

/-! # Changing the interior normalizer in every finite Hilbert fiber -/
namespace AFT
open scoped BigOperators Classical
noncomputable section
variable {Color Rest : Type*} [Fintype Color] [DecidableEq Color] [Fintype Rest]

omit [DecidableEq Color] in
/-- A bounded pointwise multiplier acts uniformly on the integrated fiber. -/
theorem integratedFiberNorm_multiplier_le (primary : Color → ℝ) (remaining : Rest → ℝ)
    (hp : ∀ color, 0 ≤ primary color) (hq : ∀ rest, 0 ≤ remaining rest)
    (factor : Color → ℝ) (bound : ℝ) (hbound : 0 ≤ bound)
    (hfactor : ∀ color, |factor color| ≤ bound) (kernel : Color → Rest → ℝ) :
    integratedFiberNorm primary remaining (fun color rest => factor color * kernel color rest) ≤
      bound * integratedFiberNorm primary remaining kernel := by
  have hs (color : Color) : (factor color)^2 ≤ bound^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hbound).mpr (hfactor color)
  unfold integratedFiberNorm
  calc
    _ ≤ Real.sqrt (bound^2 * (∑ rest, remaining rest * ∑ color, primary color * kernel color rest^2)) := by
      apply Real.sqrt_le_sqrt
      conv_rhs => rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro rest _
      calc
        _ ≤ remaining rest * ∑ color, primary color * (bound^2 * kernel color rest^2) := by
          apply mul_le_mul_of_nonneg_left _ (hq rest)
          apply Finset.sum_le_sum
          intro color _
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hs color) (sq_nonneg _)) (hp color)
        _ = _ := by simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro color _; ring
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hbound]

omit [DecidableEq Color] in
/-- A bounded pointwise multiplier also acts uniformly on all fixed fibers. -/
theorem fixedFiberNorm_multiplier_le (remaining : Rest → ℝ)
    (factor : Color → ℝ) (bound : ℝ) (hbound : 0 ≤ bound)
    (hfactor : ∀ color, |factor color| ≤ bound) (kernel : Color → Rest → ℝ) :
    fixedFiberNorm remaining (fun color rest => factor color * kernel color rest) ≤
      bound * fixedFiberNorm remaining kernel := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hbound (norm_nonneg _))).mpr
  intro color
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have he : (∑ rest, remaining rest * (factor color * kernel color rest)^2) =
      (factor color)^2 * ∑ rest, remaining rest * kernel color rest^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro rest _
    ring
  rw [he, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  apply mul_le_mul (hfactor color) _ (Real.sqrt_nonneg _) hbound
  have hh := norm_le_pi_norm (fun point => Real.sqrt (∑ rest, remaining rest * kernel point rest^2)) color
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using hh

omit [DecidableEq Color] in
/-- The multiplier estimate includes arbitrary remaining-coordinate weights. -/
theorem coordinateActivity_multiplier_le (primary : Color → ℝ) (remaining : Rest → ℝ)
    (hp : ∀ color, 0 ≤ primary color) (hq : ∀ rest, 0 ≤ remaining rest)
    (factor : Color → ℝ) (bound : ℝ) (hbound : 0 ≤ bound)
    (hfactor : ∀ color, |factor color| ≤ bound) (rate : ℝ) (hrate : 0 ≤ rate)
    (kernel : Color → Rest → ℝ) :
    coordinateActivity rate primary remaining (fun color rest => factor color * kernel color rest) ≤
      bound * coordinateActivity rate primary remaining kernel := by
  unfold coordinateActivity
  have hi := mul_le_mul_of_nonneg_left
    (integratedFiberNorm_multiplier_le primary remaining hp hq factor bound hbound hfactor kernel) hrate
  have hf := mul_le_mul_of_nonneg_left
    (fixedFiberNorm_multiplier_le remaining factor bound hbound hfactor kernel) (sq_nonneg rate)
  nlinarith only [hi, hf]

/-- Exact density multiplier relating two interior collapse normalizers. -/
def boundaryNormalizerFactor (interior : Finset Color) (primary target : Color → ℝ) (color : Color) : ℝ :=
  if color ∈ interior then
    (∑ point ∈ interior, primary point) * target color /
      ((∑ point ∈ interior, target point) * primary color)
  else 1

omit [Fintype Color] [Fintype Rest] in
/-- The target-normalized collapse equals the primary-normalized collapse
followed by a diagonal multiplier. -/
theorem partialProfileOperator_boundaryCollapse_change (interior : Finset Color)
    (primary target : Color → ℝ) (hp : ∀ color, 0 < primary color)
    (hmass : (∑ point ∈ interior, primary point) ≠ 0)
    (kernel : Color → Rest → ℝ) :
    partialProfileOperator (boundaryCollapse interior target) primary kernel =
      fun color rest => boundaryNormalizerFactor interior primary target color *
        partialProfileOperator (boundaryCollapse interior primary) primary kernel color rest := by
  funext color rest
  rw [partialProfileOperator_boundaryCollapse interior primary hp]
  unfold partialProfileOperator boundaryCollapse boundaryNormalizerFactor
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  split_ifs <;> field_simp [hmass, (hp color).ne']

/-- Changing the normalizer costs only its bounded density ratio, including
all integrated and fixed Hilbert fibers. -/
theorem boundaryCollapse_change_coordinateActivity_le (interior : Finset Color)
    (primary target : Color → ℝ) (remaining : Rest → ℝ)
    (hp : ∀ color, 0 < primary color) (hq : ∀ rest, 0 ≤ remaining rest)
    (hmass : (∑ point ∈ interior, primary point) ≠ 0)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hfactor : ∀ color, |boundaryNormalizerFactor interior primary target color| ≤ bound)
    (rate : ℝ) (hrate : 0 ≤ rate) (kernel : Color → Rest → ℝ) :
    coordinateActivity rate primary remaining (partialProfileOperator (boundaryCollapse interior target) primary kernel) ≤
      bound * coordinateActivity rate primary remaining kernel := by
  rw [partialProfileOperator_boundaryCollapse_change interior primary target hp hmass]
  exact (coordinateActivity_multiplier_le primary remaining (fun color => (hp color).le) hq
    (boundaryNormalizerFactor interior primary target) bound hbound hfactor rate hrate _).trans
    (mul_le_mul_of_nonneg_left
      (boundaryCollapse_coordinateActivity_contracts interior primary remaining hp hq rate hrate kernel) hbound)
end
end AFT

namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color] [DecidableEq Color]

/-- The full mixed activity of target-normalized boundary collapse has a
constant independent of alphabet size, pool size, and input kernel. -/
theorem boundaryCollapse_change_activity_le (reference : Slot → FiniteDist Color)
    (rates : Slot → ℝ) (hrates : ∀ slot, 0 ≤ rates slot) (slot : Slot) (hrate : 0 < rates slot)
    (interior : Finset Color) (target : Color → ℝ)
    (hp : ∀ color, 0 < (reference slot).weight color)
    (hmass : (∑ point ∈ interior, (reference slot).weight point) ≠ 0)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hfactor : ∀ color, |boundaryNormalizerFactor interior (reference slot).weight target color| ≤ bound)
    (kernel : (Slot → Color) → ℝ) :
    activity rates reference (partialInputOperator slot (boundaryCollapse interior target) (reference slot).weight kernel) ≤
      (2 * bound) * activity rates reference kernel := by
  apply partialInputOperator_activity_le reference rates hrates slot hrate _ bound hbound
  intro fiber
  exact boundaryCollapse_change_coordinateActivity_le interior (reference slot).weight target _
    hp (FiniteDist.nonneg _) hmass bound hbound hfactor (rates slot) hrate.le fiber
end
end AFT.MixedKernel
