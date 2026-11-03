import AFT.LocalCoefficientLinear
import AFT.V7Blocks

/-! # One common finite Fock alphabet for heterogeneous local output blocks -/
namespace AFT.LocalTensors
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]
local instance packedFockFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

abbrev PackedCoordinate (maximum : ℕ) (Color : Type*) :=
  Sigma (fun degree : Fin (maximum + 1) => Fin degree.val → Color)

/-- All local degrees are embedded into one common alphabet; unused higher
degrees are the actual zero coefficients, not an assumed truncation. -/
def packedFockChannel (reference : FiniteDist Color) (maximum population : ℕ) (radius : ℝ) :
    ((Slot → Color) → ℝ) →ₗ[ℝ] (PackedCoordinate maximum Color → ℝ) where
  toFun mass coordinate := Real.sqrt (coordinate.1.val.factorial : ℝ) *
    (Real.sqrt 2 * (radius / Real.sqrt population)) ^ coordinate.1.val *
      degreeTensor (fun _ : Slot => reference) mass coordinate.1.val coordinate.2
  map_add' first second := by
    funext coordinate
    rw [← degreeTensorLinear_apply, map_add]
    simp only [Pi.add_apply, mul_add, degreeTensorLinear_apply]
  map_smul' scalar mass := by
    funext coordinate
    rw [← degreeTensorLinear_apply, map_smul]
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, degreeTensorLinear_apply]
    ring

/-- The padded coefficient energy is exactly the local marked Fock budget
apart from its harmless number-of-degrees prefactor. -/
theorem packedFockChannel_energy (reference : FiniteDist Color) (maximum population : ℕ) (radius : ℝ)
    (hmaximum : Fintype.card Slot ≤ maximum) (mass : (Slot → Color) → ℝ) :
    (Fintype.card Slot + 1 : ℕ) *
      (∑ coordinate, packedFockChannel reference maximum population radius mass coordinate ^ 2) =
      BlockProducts.taggedCoefficientEnergy reference mass population radius := by
  rw [Fintype.sum_sigma]
  simp only [packedFockChannel, LinearMap.coe_mk, AddHom.coe_mk]
  change (Fintype.card Slot + 1 : ℕ) * (∑ degree : Fin (maximum + 1),
    ∑ word : Fin degree.val → Color, (Real.sqrt (degree.val.factorial : ℝ) *
      (Real.sqrt 2 * (radius / Real.sqrt population)) ^ degree.val *
        degreeTensor (fun _ : Slot => reference) mass degree.val word) ^ 2) = _
  rw [Fin.sum_univ_eq_sum_range (fun degree : ℕ => ∑ word : Fin degree → Color,
    (Real.sqrt (degree.factorial : ℝ) * (Real.sqrt 2 * (radius / Real.sqrt population)) ^ degree *
      degreeTensor (fun _ : Slot => reference) mass degree word) ^ 2) (maximum + 1)]
  unfold BlockProducts.taggedCoefficientEnergy TensorFock.normalizedTensor BlockFock.tensorEnergy
  congr 1
  have hterm (degree : ℕ) :
      (∑ word : Fin degree → Color,
        (Real.sqrt (degree.factorial : ℝ) * (Real.sqrt 2 * (radius / Real.sqrt population)) ^ degree *
          degreeTensor (fun _ : Slot => reference) mass degree word) ^ 2) =
      (degree.factorial : ℝ) * 2 ^ degree *
        ∑ word : Fin degree → Color, ((radius / Real.sqrt population) ^ degree *
          degreeTensor (fun _ : Slot => reference) mass degree word) ^ 2 := by
    have hpow : (Real.sqrt 2 ^ degree) ^ 2 = (2 : ℝ) ^ degree := by
      rw [← pow_mul, Nat.mul_comm degree 2, pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    simp only [mul_pow, hpow, Real.sq_sqrt (Nat.cast_nonneg degree.factorial), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro word _
    ring
  simp_rw [hterm]
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hmaximum))
  intro degree hdegree hnot
  have habove : Fintype.card Slot < degree := by simp only [Finset.mem_range, not_lt] at hnot; omega
  simp only [degreeTensor_zero_above _ _ _ habove, Pi.zero_apply, mul_zero, zero_pow (by omega : 2 ≠ 0),
    Finset.sum_const_zero, mul_zero]

/-- Common-alphabet padding preserves the same dimension-free local energy
bound, with no extra factor depending on the color palette. -/
theorem packedFockChannel_energy_le (reference : FiniteDist Color) (maximum population : ℕ) (radius : ℝ)
    (hmaximum : Fintype.card Slot ≤ maximum) (mass : (Slot → Color) → ℝ) :
    (∑ coordinate, packedFockChannel reference maximum population radius mass coordinate ^ 2) ≤
      BlockProducts.taggedCoefficientEnergy reference mass population radius := by
  rw [← packedFockChannel_energy reference maximum population radius hmaximum mass]
  exact le_mul_of_one_le_left (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _))

end
end AFT.LocalTensors
