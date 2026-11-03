import AFT.SelectionBound
import AFT.Fock

/-! # Actual tagged homogeneous responses multiplied by complete block products -/

namespace AFT
namespace TaggedFock

open MeasureTheory TensorFock NonlinearFock
open scoped BigOperators Classical

variable {Index Coordinate Slot : Type*}
variable [Fintype Index] [Fintype Coordinate] [Fintype Slot]

omit [Fintype Slot] in
set_option backward.isDefEq.respectTransparency false in
/-- A full cubic block product has an exact finite polynomial certificate. -/
theorem cubicBlockProduct_polynomial (linear : Index → Coordinate → ℝ)
    (quadratic : Index → BlockFock.Tensor (Fin 2) Coordinate)
    (cubic : Index → BlockFock.Tensor (Fin 3) Coordinate) :
    IsTensorPolynomial (cubicBlockProduct linear quadratic cubic) := by
  letI : DecidableEq (Fin 1) := Classical.decEq _
  let Slots (_ : Index) (choice : Fin 4) := Fin choice.val
  let tensor (index : Index) : (choice : Fin 4) → BlockFock.Tensor (Slots index choice) Coordinate := by
    intro choice
    refine Fin.cases (fun _ => 1) ?_ choice
    intro second
    refine Fin.cases (fun word : Fin 1 → Coordinate => linear index (word 0)) ?_ second
    intro third
    refine Fin.cases (quadratic index) ?_ third
    intro fourth
    refine Fin.cases (cubic index) ?_ fourth
    exact fun impossible => Fin.elim0 impossible
  have h := finite_block_product_polynomial (fun _ : Index => Fin 4) Slots tensor
  have heval (index : Index) (value : Coordinate → ℂ) :
      (∑ choice : Fin 4, tensorEvaluation (tensor index choice) value) =
        ((1 + ∑ coordinate, (linear index coordinate : ℂ) * value coordinate) +
          tensorEvaluation (quadratic index) value + tensorEvaluation (cubic index) value) := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    change tensorEvaluation (fun _ : Fin 0 → Coordinate => (1 : ℝ)) value +
      (tensorEvaluation (fun word : Fin 1 → Coordinate => linear index (word 0)) value +
        (tensorEvaluation (quadratic index) value + (tensorEvaluation (cubic index) value + 0))) = _
    have hzero : tensorEvaluation (fun _ : Fin 0 → Coordinate => (1 : ℝ)) value = 1 := by
      simp [tensorEvaluation, wordMonomial]
    have hone : tensorEvaluation (fun word : Fin 1 → Coordinate => linear index (word 0)) value =
        ∑ coordinate, (linear index coordinate : ℂ) * value coordinate := by
      simp only [tensorEvaluation, wordMonomial, Fin.prod_univ_one]
      exact (Equiv.funUnique (Fin 1) Coordinate).sum_comp
        (fun coordinate => (linear index coordinate : ℂ) * value coordinate)
    rw [hzero, hone]
    ring
  simpa only [heval, cubicBlockProduct] using h

omit [Fintype Slot] in
/-- Exact dilation of the actual cubic product, including every homogeneous
coefficient and all source blocks. -/
theorem cubicBlockProduct_dilate (linear : Index → Coordinate → ℝ)
    (quadratic : Index → BlockFock.Tensor (Fin 2) Coordinate)
    (cubic : Index → BlockFock.Tensor (Fin 3) Coordinate) (radius : ℝ)
    (value : Coordinate → ℂ) :
    cubicBlockProduct linear quadratic cubic (fun coordinate => (radius : ℂ) * value coordinate) =
      cubicBlockProduct (fun index coordinate => radius * linear index coordinate)
        (fun index word => radius ^ 2 * quadratic index word)
        (fun index word => radius ^ 3 * cubic index word) value := by
  unfold cubicBlockProduct
  apply Finset.prod_congr rfl
  intro index _
  rw [tensorEvaluation_dilate, tensorEvaluation_dilate]
  simp only [Fintype.card_fin]
  congr 3
  apply Finset.sum_congr rfl
  intro coordinate _
  push_cast
  ring

set_option backward.isDefEq.respectTransparency false in
/-- Any genuine joint homogeneous tagged response can multiply the complete
independent-block product. The radius is doubled only once, and the full
factorial cost depends on the actual total tagged degree. -/
theorem tagged_cubic_block_energy_le [Nonempty Coordinate]
    (tagged : BlockFock.Tensor Slot Coordinate) (linear : Index → Coordinate → ℝ)
    (quadratic : Index → BlockFock.Tensor (Fin 2) Coordinate)
    (cubic : Index → BlockFock.Tensor (Fin 3) Coordinate) (capacity : ℕ)
    (hcapacity : (SelectionBound.nonlinearSupport
      (fun index word => (Real.sqrt 2) ^ 2 * quadratic index word)
      (fun index word => (Real.sqrt 2) ^ 3 * cubic index word)).card ≤ capacity)
    (henergy : (∑ index, ∑ coordinate, (Real.sqrt 2 * linear index coordinate) ^ 2) ≤ 1 / 8)
    (hsmall : (∑ index, (128 * SelectionBound.localPairNorm
      (fun index word => (Real.sqrt 2) ^ 2 * quadratic index word) index +
        128 * Real.sqrt capacity * SelectionBound.localTripleNorm
          (fun index word => (Real.sqrt 2) ^ 3 * cubic index word) index)) ≤ 1 / 2) :
    (∫ value, Complex.normSq (tensorEvaluation tagged value *
      cubicBlockProduct linear quadratic cubic value) ∂FockGaussian.field) ≤
      ((Fintype.card Slot).factorial : ℝ) * 2 ^ Fintype.card Slot * BlockFock.tensorEnergy tagged *
        (16 * Real.exp (8 * ∑ coordinate, (∑ index, Real.sqrt 2 * linear index coordinate) ^ 2)) := by
  apply (homogeneous_times_polynomial_energy_le tagged
    (cubicBlockProduct_polynomial linear quadratic cubic)).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by positivity)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  simp_rw [cubicBlockProduct_dilate]
  exact SelectionBound.independent_cubic_block_fock_bound
    (fun index coordinate => Real.sqrt 2 * linear index coordinate)
    (fun index word => (Real.sqrt 2) ^ 2 * quadratic index word)
    (fun index word => (Real.sqrt 2) ^ 3 * cubic index word) capacity hcapacity henergy hsmall

end TaggedFock
end AFT
