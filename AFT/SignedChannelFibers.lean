import AFT.SignedChannelEnergy

/-! # Schur bounds retaining the input's fixed-coordinate fibers -/

namespace AFT
open scoped BigOperators Classical
noncomputable section

/-- A bounded signed input retains the true positive output mass. -/
theorem signedChannel_abs_le {Input Output : Type*} [Fintype Input]
    (input : FiniteDist Input) (kernel : Input → Output → ℝ)
    (hkernel : ∀ point output, 0 ≤ kernel point output)
    (score : Input → ℝ) (bound : ℝ) (hscore : ∀ point, |score point| ≤ bound)
    (output : Output) :
    |∑ point, input.weight point * score point * kernel point output| ≤
      bound * ∑ point, input.weight point * kernel point output := by
  calc
    _ ≤ ∑ point, |input.weight point * score point * kernel point output| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ point, bound * (input.weight point * kernel point output) := by
      apply Finset.sum_le_sum
      intro point _
      rw [abs_mul, abs_mul, abs_of_nonneg (input.nonneg point),
        abs_of_nonneg (hkernel point output)]
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hscore point) (input.nonneg point))
        (hkernel point output)).trans_eq (by ring)
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- All fixed fibers use the genuine output-density ceiling; no palette
cardinality is paid for fixing an output. -/
theorem signedChannel_density_abs_le {Input Output : Type*} [Fintype Input]
    (input : FiniteDist Input) (reference : Output → ℝ)
    (kernel : Input → Output → ℝ) (densityBound scoreBound : ℝ)
    (href : ∀ output, 0 < reference output)
    (hscoreBound : 0 ≤ scoreBound)
    (hkernel : ∀ point output, 0 ≤ kernel point output)
    (hdensity : ∀ output, (∑ point, input.weight point * kernel point output) ≤
      densityBound * reference output)
    (score : Input → ℝ) (hscore : ∀ point, |score point| ≤ scoreBound)
    (output : Output) :
    |(∑ point, input.weight point * score point * kernel point output) / reference output| ≤
      densityBound * scoreBound := by
  rw [abs_div, abs_of_pos (href output)]
  apply (div_le_iff₀ (href output)).mpr
  exact (signedChannel_abs_le input kernel hkernel score scoreBound hscore output).trans
    ((mul_le_mul_of_nonneg_left (hdensity output) hscoreBound).trans_eq (by ring))

/-- With one output fixed, use its actual positive marginal. This keeps
only the square root of the full density ceiling, rather than that ceiling. -/
theorem signedChannel_fixed_fiber_square_le {Input Free : Type*}
    [Fintype Input] [Fintype Free]
    (input : FiniteDist Input) (reference : FiniteDist Free)
    (kernel : Input → Free → ℝ) (fixedWeight densityBound marginalBound scoreBound : ℝ)
    (hfixed : 0 < fixedWeight) (href : ∀ output, 0 < reference.weight output)
    (hD : 0 ≤ densityBound) (hL : 0 ≤ scoreBound)
    (hkernel : ∀ point output, 0 ≤ kernel point output)
    (hdensity : ∀ output, (∑ point, input.weight point * kernel point output) ≤
      densityBound * (fixedWeight * reference.weight output))
    (hmarginal : (∑ output, ∑ point, input.weight point * kernel point output) ≤
      marginalBound * fixedWeight)
    (score : Input → ℝ) (hscore : ∀ point, |score point| ≤ scoreBound) :
    reference.l2Sq (fun output =>
      (∑ point, input.weight point * score point * kernel point output) /
        (fixedWeight * reference.weight output)) ≤
      densityBound * marginalBound * scoreBound ^ 2 := by
  have hpoint (output : Free) :
      reference.weight output *
        ((∑ point, input.weight point * score point * kernel point output) /
          (fixedWeight * reference.weight output)) ^ 2 ≤
        densityBound * scoreBound ^ 2 / fixedWeight *
          ∑ point, input.weight point * kernel point output := by
    let mass := ∑ point, input.weight point * kernel point output
    let signed := ∑ point, input.weight point * score point * kernel point output
    have hm : 0 ≤ mass := Finset.sum_nonneg fun point _ =>
      mul_nonneg (input.nonneg point) (hkernel point output)
    have habs : |signed| ≤ scoreBound * mass :=
      signedChannel_abs_le input kernel hkernel score scoreBound hscore output
    have hsq : signed ^ 2 ≤ scoreBound ^ 2 * mass ^ 2 := by
      have hh := sq_le_sq₀ (abs_nonneg signed) (mul_nonneg hL hm) |>.mpr habs
      simpa only [sq_abs, mul_pow] using hh
    have hden := mul_le_mul_of_nonneg_left (hdensity output) hm
    have hsigned : signed ^ 2 ≤
        densityBound * scoreBound ^ 2 * fixedWeight * reference.weight output * mass := by
      apply hsq.trans
      have hh := mul_le_mul_of_nonneg_left hden (sq_nonneg scoreBound)
      convert hh using 1 <;> ring
    have hpos : 0 < fixedWeight ^ 2 * reference.weight output := mul_pos (sq_pos_of_pos hfixed) (href output)
    have heq : reference.weight output * (signed / (fixedWeight * reference.weight output)) ^ 2 =
        signed ^ 2 / (fixedWeight ^ 2 * reference.weight output) := by
      field_simp
    change reference.weight output * (signed / (fixedWeight * reference.weight output)) ^ 2 ≤ _
    rw [heq]
    apply (div_le_iff₀ hpos).mpr
    convert hsigned using 1
    field_simp
    ring
  calc
    _ ≤ ∑ output, densityBound * scoreBound ^ 2 / fixedWeight *
        ∑ point, input.weight point * kernel point output := Finset.sum_le_sum fun output _ => hpoint output
    _ = densityBound * scoreBound ^ 2 / fixedWeight *
        (∑ output, ∑ point, input.weight point * kernel point output) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ densityBound * scoreBound ^ 2 / fixedWeight * (marginalBound * fixedWeight) :=
      mul_le_mul_of_nonneg_left hmarginal (by positivity)
    _ = _ := by field_simp

/-- A positive linear combination contracts Hilbert-valued sup fibers.
The remaining finite probability space can contain an arbitrary joint
kernel; its coordinates are never separated into rank-one terms. -/
theorem positiveCombination_l2Sq_le {Index Fiber : Type*} [Fintype Index] [Fintype Fiber]
    (fiber : FiniteDist Fiber) (weight : Index → ℝ) (value : Index → Fiber → ℝ)
    (bound : ℝ) (hweight : ∀ index, 0 ≤ weight index)
    (hvalue : ∀ index, fiber.l2Sq (value index) ≤ bound) :
    fiber.l2Sq (fun point => ∑ index, weight index * value index point) ≤
      (∑ index, weight index) ^ 2 * bound := by
  have hp (point : Fiber) : (∑ index, weight index * value index point) ^ 2 ≤
      (∑ index, weight index) * ∑ index, weight index * value index point ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    · intro index _; exact hweight index
    · intro index _; exact mul_nonneg (hweight index) (sq_nonneg _)
    · intro index _; ring
  calc
    _ ≤ ∑ point, fiber.weight point *
        ((∑ index, weight index) * ∑ index, weight index * value index point ^ 2) :=
      Finset.sum_le_sum fun point _ => mul_le_mul_of_nonneg_left (hp point) (fiber.nonneg point)
    _ = (∑ index, weight index) * ∑ index, weight index * fiber.l2Sq (value index) := by
      simp only [FiniteDist.l2Sq, FiniteDist.expectation, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro point _
      apply Finset.sum_congr rfl
      intro index _
      ring
    _ ≤ (∑ index, weight index) * ∑ index, weight index * bound := by
      apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg fun index _ => hweight index)
      exact Finset.sum_le_sum fun index _ => mul_le_mul_of_nonneg_left (hvalue index) (hweight index)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- Schur's one-fixed estimate remains valid with every other old input
fiber left jointly Hilbert-valued. -/
theorem signedChannel_fixed_hilbert_square_le {Input Free Fiber : Type*}
    [Fintype Input] [Fintype Free] [Fintype Fiber]
    (input : FiniteDist Input) (reference : FiniteDist Free) (fiber : FiniteDist Fiber)
    (kernel : Input → Free → ℝ) (fixedWeight densityBound marginalBound scoreSquare : ℝ)
    (hfixed : 0 < fixedWeight) (href : ∀ output, 0 < reference.weight output)
    (hD : 0 ≤ densityBound) (hL : 0 ≤ scoreSquare)
    (hkernel : ∀ point output, 0 ≤ kernel point output)
    (hdensity : ∀ output, (∑ point, input.weight point * kernel point output) ≤
      densityBound * (fixedWeight * reference.weight output))
    (hmarginal : (∑ output, ∑ point, input.weight point * kernel point output) ≤
      marginalBound * fixedWeight)
    (score : Input → Fiber → ℝ) (hscore : ∀ point, fiber.l2Sq (score point) ≤ scoreSquare) :
    reference.expectation (fun output => fiber.l2Sq (fun rest =>
      (∑ point, input.weight point * score point rest * kernel point output) /
        (fixedWeight * reference.weight output))) ≤
      densityBound * marginalBound * scoreSquare := by
  have hpoint (output : Free) :
      reference.weight output * fiber.l2Sq (fun rest =>
        (∑ point, input.weight point * score point rest * kernel point output) /
          (fixedWeight * reference.weight output)) ≤
        densityBound * scoreSquare / fixedWeight *
          ∑ point, input.weight point * kernel point output := by
    let mass := ∑ point, input.weight point * kernel point output
    have hm : 0 ≤ mass := Finset.sum_nonneg fun point _ =>
      mul_nonneg (input.nonneg point) (hkernel point output)
    have hh := positiveCombination_l2Sq_le fiber
      (fun point => input.weight point * kernel point output) score scoreSquare
      (fun point => mul_nonneg (input.nonneg point) (hkernel point output)) hscore
    have heq : fiber.l2Sq (fun rest =>
        (∑ point, input.weight point * score point rest * kernel point output) /
          (fixedWeight * reference.weight output)) =
        fiber.l2Sq (fun rest => ∑ point, (input.weight point * kernel point output) * score point rest) /
          (fixedWeight * reference.weight output) ^ 2 := by
      have hsum (rest) : (∑ point, input.weight point * score point rest * kernel point output) =
          ∑ point, (input.weight point * kernel point output) * score point rest := by
        apply Finset.sum_congr rfl
        intro point _
        ring
      simp only [hsum, FiniteDist.l2Sq, FiniteDist.expectation]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro rest _
      ring
    rw [heq]
    have hc : mass ^ 2 * scoreSquare ≤
        densityBound * scoreSquare * fixedWeight * reference.weight output * mass := by
      have ht := mul_le_mul_of_nonneg_right (hdensity output) (mul_nonneg hm hL)
      convert ht using 1 <;> ring
    have hden : 0 < fixedWeight ^ 2 * reference.weight output :=
      mul_pos (sq_pos_of_pos hfixed) (href output)
    have hh' : reference.weight output *
        (fiber.l2Sq (fun rest => ∑ point, (input.weight point * kernel point output) * score point rest) /
          (fixedWeight * reference.weight output) ^ 2) =
        fiber.l2Sq (fun rest => ∑ point, (input.weight point * kernel point output) * score point rest) /
          (fixedWeight ^ 2 * reference.weight output) := by field_simp
    rw [hh']
    apply (div_le_iff₀ hden).mpr
    convert hh.trans hc using 1
    field_simp
    ring
  calc
    _ ≤ ∑ output, densityBound * scoreSquare / fixedWeight *
        ∑ point, input.weight point * kernel point output := Finset.sum_le_sum fun output _ => hpoint output
    _ = densityBound * scoreSquare / fixedWeight *
        (∑ output, ∑ point, input.weight point * kernel point output) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ densityBound * scoreSquare / fixedWeight * (marginalBound * fixedWeight) :=
      mul_le_mul_of_nonneg_left hmarginal (by positivity)
    _ = _ := by field_simp

/-- Fixing all new outputs keeps the old remainder Hilbert-valued. -/
theorem signedChannel_density_hilbert_square_le {Input Fiber : Type*}
    [Fintype Input] [Fintype Fiber]
    (input : FiniteDist Input) (fiber : FiniteDist Fiber) (kernel : Input → ℝ)
    (reference densityBound squareBound : ℝ) (href : 0 < reference)
    (hD : 0 ≤ densityBound) (hL : 0 ≤ squareBound)
    (hkernel : ∀ point, 0 ≤ kernel point)
    (hdensity : (∑ point, input.weight point * kernel point) ≤ densityBound * reference)
    (score : Input → Fiber → ℝ) (hscore : ∀ point, fiber.l2Sq (score point) ≤ squareBound) :
    fiber.l2Sq (fun rest => (∑ point, input.weight point * score point rest * kernel point) / reference) ≤
      densityBound ^ 2 * squareBound := by
  let weight := fun point => input.weight point * kernel point / reference
  have hw (point) : 0 ≤ weight point := div_nonneg (mul_nonneg (input.nonneg point) (hkernel point)) href.le
  have hm : (∑ point, weight point) ≤ densityBound := by
    unfold weight
    rw [← Finset.sum_div]
    exact (div_le_iff₀ href).mpr hdensity
  have hm0 : 0 ≤ ∑ point, weight point := Finset.sum_nonneg fun point _ => hw point
  have hh := positiveCombination_l2Sq_le fiber weight score squareBound hw hscore
  have heq : (fun rest => (∑ point, input.weight point * score point rest * kernel point) / reference) =
      (fun rest => ∑ point, weight point * score point rest) := by
    funext rest
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro point _
    dsimp [weight]
    ring
  rw [heq]
  exact hh.trans (mul_le_mul_of_nonneg_right ((sq_le_sq₀ hm0 hD).mpr hm) hL)

end
end AFT
