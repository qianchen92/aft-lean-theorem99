import CurrentAFT.ActualFockBound

/-! # The complete physical Fock energy is a genuine finite Hilbert norm -/

namespace CurrentAFT.PhysicalFockHilbert

open AFT ActualFockBound
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]

def channel (reference : FiniteDist Color) (radius : ℝ) :
    ((Slot → Color) → ℝ) →ₗ[ℝ] (LocalTensors.FockCoordinate Slot Color → ℝ) where
  toFun mass coordinate := Real.sqrt (coordinate.1.val.factorial : ℝ) *
    (radius / Real.sqrt (Fintype.card Slot : ℝ)) ^ coordinate.1.val *
      LocalTensors.degreeTensor (fun _ : Slot => reference) mass coordinate.1.val coordinate.2
  map_add' first second := by
    funext coordinate
    rw [← LocalTensors.degreeTensorLinear_apply, map_add]
    simp only [Pi.add_apply, mul_add, LocalTensors.degreeTensorLinear_apply]
  map_smul' scalar mass := by
    funext coordinate
    rw [← LocalTensors.degreeTensorLinear_apply, map_smul]
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, LocalTensors.degreeTensorLinear_apply]
    ring

theorem channel_energy (reference : FiniteDist Color) (radius : ℝ) (mass : (Slot → Color) → ℝ) :
    (∑ coordinate, channel reference radius mass coordinate ^ 2) = energy reference mass radius := by
  have hnorm (degree : ℕ) : ((radius / Real.sqrt (Fintype.card Slot : ℝ)) ^ degree) ^ 2 =
      radius ^ (2 * degree) / (Fintype.card Slot : ℝ) ^ degree := by
    rw [← pow_mul, Nat.mul_comm degree 2, pow_mul, div_pow,
      Real.sq_sqrt (Nat.cast_nonneg _), div_pow, ← pow_mul]
  rw [Fintype.sum_sigma]
  simp only [channel, LinearMap.coe_mk, AddHom.coe_mk, mul_pow,
    Real.sq_sqrt (Nat.cast_nonneg _), hnorm]
  unfold energy HistogramTail.fockEnergy BlockFock.tensorEnergy
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro degree _
  rw [Finset.mul_sum]
  rw [Finset.sum_div]
  apply Finset.sum_congr (by ext; simp)
  intro word _
  ring

/-- A literal finite Euclidean vector, with the physical ordered-tensor
factorials and exact full-population normalization in every degree. -/
def vector (reference : FiniteDist Color) (radius : ℝ) :
    ((Slot → Color) → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (LocalTensors.FockCoordinate Slot Color) :=
  (ProfileHilbert.whiten (fun _ : LocalTensors.FockCoordinate Slot Color => (1 : ℝ))).comp
    (channel reference radius)

theorem vector_norm_sq (reference : FiniteDist Color) (radius : ℝ) (mass : (Slot → Color) → ℝ) :
    ‖vector reference radius mass‖ ^ 2 = energy reference mass radius := by
  rw [vector, LinearMap.comp_apply, ProfileHilbert.whiten_norm_sq _ _ (fun _ => by norm_num)]
  simpa only [profileSquareNorm, div_one] using channel_energy reference radius mass

/-- The full physical norm of any finite signed coefficient combination
is bounded by the weighted sum of the full component norms. No number of
palette atoms, frequencies, or tensor-rank terms enters the estimate. -/
theorem energy_signed_sum_le {Index : Type*} [Fintype Index]
    (reference : FiniteDist Color) (radius : ℝ) (coefficient bound : Index → ℝ)
    (mass : Index → (Slot → Color) → ℝ) (hbound : ∀ index, 0 ≤ bound index)
    (hcomponent : ∀ index, energy reference (mass index) radius ≤ bound index ^ 2) :
    energy reference (fun word => ∑ index, coefficient index * mass index word) radius ≤
      (∑ index, |coefficient index| * bound index) ^ 2 := by
  have hm : (fun word => ∑ index, coefficient index * mass index word) =
      ∑ index, coefficient index • mass index := by
    funext word
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hv (index : Index) : ‖vector reference radius (mass index)‖ ≤ bound index := by
    apply (sq_le_sq₀ (norm_nonneg _) (hbound index)).mp
    rw [vector_norm_sq]
    exact hcomponent index
  rw [← vector_norm_sq, hm, map_sum]
  simp only [map_smul]
  have hnorm : ‖∑ index, coefficient index • vector reference radius (mass index)‖ ≤
      ∑ index, |coefficient index| * bound index := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro index _
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hv index) (abs_nonneg _)
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2

end

end CurrentAFT.PhysicalFockHilbert
