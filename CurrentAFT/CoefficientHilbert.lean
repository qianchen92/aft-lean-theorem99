import CurrentAFT.LocalRaisingBounds

/-! # Finite Hilbert coordinates of the actual graded coefficient algebra -/
namespace CurrentAFT.CoefficientHilbert

open AFT ControlCoordinates ControlProduct ControlNorm GradedControlAlgebra GradedControlNorm
  GradedControlStability LocalRaisingLinear LocalRaisingBounds
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

abbrev Coordinate (Primary Body : Type*) (order : ℕ) :=
  (arity : TruncatedArity order) × ((Fin arity.val.1.val → Primary) × (Fin arity.val.2.val → Body))

def referenceWeight (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (coordinate : Coordinate Primary Body order) : ℝ :=
  (∏ index, primary.weight (coordinate.2.1 index)) * ∏ index, body.weight (coordinate.2.2 index)

theorem referenceWeight_nonneg (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (coordinate : Coordinate Primary Body order) : 0 ≤ referenceWeight primary body order coordinate := by
  exact mul_nonneg (Finset.prod_nonneg (fun _ _ => primary.nonneg _))
    (Finset.prod_nonneg (fun _ _ => body.nonneg _))

def encodeLinear (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (primaryFactor bodyFactor : ℝ) :
    KernelFamily primary body order →ₗ[ℝ] (Coordinate Primary Body order → ℝ) where
  toFun family coordinate :=
    gradeWeight primaryFactor bodyFactor coordinate.1.val.1.val coordinate.1.val.2.val *
      Real.sqrt (referenceWeight primary body order coordinate) *
        (family coordinate.1).val coordinate.2.1 coordinate.2.2
  map_add' first second := by
    funext coordinate
    simp only [Pi.add_apply, Submodule.coe_add, mul_add]
  map_smul' scalar family := by
    funext coordinate
    simp only [Pi.smul_apply, Submodule.coe_smul, smul_eq_mul, RingHom.id_apply]
    ring

theorem encode_energy (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (primaryFactor bodyFactor : ℝ) (family : KernelFamily primary body order) :
    (∑ coordinate, (encodeLinear primary body order primaryFactor bodyFactor family coordinate) ^ 2) =
      ∑ arity : TruncatedArity order,
        gradeWeight primaryFactor bodyFactor arity.val.1.val arity.val.2.val ^ 2 *
          blockEnergy primary body (family arity).val := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro arity _
  rw [Fintype.sum_prod_type, blockEnergy_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro colors _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro centers _
  simp only [encodeLinear, LinearMap.coe_mk, AddHom.coe_mk, mul_pow, referenceWeight]
  rw [Real.sq_sqrt (mul_nonneg (Finset.prod_nonneg (fun index _ => primary.nonneg (colors index)))
    (Finset.prod_nonneg (fun index _ => body.nonneg (centers index))))]
  ring

theorem encode_energy_eq_sum_sq (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (primaryFactor bodyFactor : ℝ) (family : KernelFamily primary body order) :
    (∑ coordinate, (encodeLinear primary body order primaryFactor bodyFactor family coordinate) ^ 2) =
      ∑ arity : TruncatedArity order,
        (gradeWeight primaryFactor bodyFactor arity.val.1.val arity.val.2.val *
          blockL2 primary body (family arity).val) ^ 2 := by
  rw [encode_energy]
  apply Finset.sum_congr rfl
  intro arity _
  rw [mul_pow, blockL2, Real.sq_sqrt (blockEnergy_nonneg primary body _)]

theorem encode_energy_le (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (primaryFactor bodyFactor : ℝ) (hprimary : 0 ≤ primaryFactor) (hbody : 0 ≤ bodyFactor)
    (family : KernelFamily primary body order) :
    (∑ coordinate, (encodeLinear primary body order primaryFactor bodyFactor family coordinate) ^ 2) ≤
      familyNorm primary body order primaryFactor bodyFactor family ^ 2 := by
  rw [encode_energy_eq_sum_sq]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun arity _ =>
    mul_nonneg (gradeWeight_nonneg _ _ hprimary hbody _ _) (blockL2_nonneg primary body _))

theorem familyNorm_sq_le_encoded (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (primaryFactor bodyFactor : ℝ) (family : KernelFamily primary body order) :
    familyNorm primary body order primaryFactor bodyFactor family ^ 2 ≤
      (Fintype.card (TruncatedArity order) : ℝ) *
        ∑ coordinate, (encodeLinear primary body order primaryFactor bodyFactor family coordinate) ^ 2 := by
  rw [encode_energy_eq_sum_sq]
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (TruncatedArity order))
    (fun _ => (1 : ℝ)) (fun arity => gradeWeight primaryFactor bodyFactor arity.val.1.val arity.val.2.val *
      blockL2 primary body (family arity).val)
  simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, familyNorm] using h

def centerLinear {Color : Type*} [Fintype Color] (law : FiniteDist Color) : (Color → ℝ) →ₗ[ℝ] (Color → ℝ) where
  toFun score := fun color => score color - law.expectation score
  map_add' first second := by
    funext color
    change first color + second color - law.expectation (fun point => first point + second point) = _
    rw [FiniteDist.expectation_add]
    simp only [Pi.add_apply]
    ring
  map_smul' scalar score := by
    funext color
    change scalar * score color - law.expectation (fun point => scalar * score point) = _
    rw [FiniteDist.expectation_const_mul]
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem center_mean {Color : Type*} [Fintype Color] (law : FiniteDist Color) (score : Color → ℝ) :
    law.expectation (centerLinear law score) = 0 := by
  change law.expectation (fun color => score color - law.expectation score) = 0
  rw [FiniteDist.expectation_sub, FiniteDist.expectation_const, sub_self]

theorem center_energy {Color : Type*} [Fintype Color] (law : FiniteDist Color) (score : Color → ℝ) :
    law.l2Sq (centerLinear law score) = law.l2Sq score - (law.expectation score) ^ 2 := by
  have hexpand (color : Color) : (score color - law.expectation score) ^ 2 =
      score color ^ 2 - 2 * law.expectation score * score color + (law.expectation score) ^ 2 := by ring
  unfold FiniteDist.l2Sq
  change law.expectation (fun color => (score color - law.expectation score) ^ 2) = _
  simp_rw [hexpand]
  rw [FiniteDist.expectation_add, FiniteDist.expectation_sub, FiniteDist.expectation_const_mul,
    FiniteDist.expectation_const]
  ring

theorem center_energy_le {Color : Type*} [Fintype Color] (law : FiniteDist Color) (score : Color → ℝ) :
    law.l2Sq (centerLinear law score) ≤ law.l2Sq score := by
  rw [center_energy]
  linarith [sq_nonneg (law.expectation score)]

end
end CurrentAFT.CoefficientHilbert
