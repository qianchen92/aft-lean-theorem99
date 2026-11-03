import AFT.TaggedBlockTail
import AFT.TensorChannel

/-! # The actual finite Fock coefficients form one linear Hilbert channel -/

namespace AFT.LocalTensors

open scoped BigOperators Classical
noncomputable section
local instance localCoefficientLinearFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]

/-- Actual finite tensor symmetrization is a linear operation. -/
def symmetrizeLinear : BlockFock.Tensor Slot Color →ₗ[ℝ] BlockFock.Tensor Slot Color where
  toFun := BlockFock.symmetrize
  map_add' first second := by
    funext word
    simp only [BlockFock.symmetrize, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' scalar tensor := by
    funext word
    simp only [BlockFock.symmetrize, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro permutation _
    ring

/-- Every actual selected homogeneous piece is linear in the signed mass. -/
def degreePieceLinear (reference : Slot → FiniteDist Color) (degree : ℕ) (selected : Finset Slot) :
    ((Slot → Color) → ℝ) →ₗ[ℝ] BlockFock.Tensor (Fin degree) Color where
  toFun mass := degreePiece reference mass degree selected
  map_add' first second := by
    funext word
    by_cases h : Fintype.card selected = degree
    · simp only [degreePiece, dif_pos h, localTensor_formula, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    · simp only [degreePiece, dif_neg h, Pi.add_apply, add_zero]
  map_smul' scalar mass := by
    funext word
    by_cases h : Fintype.card selected = degree
    · simp only [degreePiece, dif_pos h, localTensor_formula, Pi.smul_apply, smul_eq_mul,
        RingHom.id_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro input _
      ring
    · simp only [degreePiece, dif_neg h, Pi.smul_apply, smul_eq_mul, mul_zero]

/-- All degree coefficients are the literal linear response of the signed
physical mass. This map includes the actual finite symmetrization. -/
def degreeTensorLinear (reference : Slot → FiniteDist Color) (degree : ℕ) :
    ((Slot → Color) → ℝ) →ₗ[ℝ] BlockFock.Tensor (Fin degree) Color :=
  symmetrizeLinear.comp (∑ selected : Finset Slot, degreePieceLinear reference degree selected)

@[simp] theorem degreeTensorLinear_apply (reference : Slot → FiniteDist Color) (degree : ℕ)
    (mass : (Slot → Color) → ℝ) : degreeTensorLinear reference degree mass = degreeTensor reference mass degree := by
  simp only [degreeTensorLinear, LinearMap.comp_apply, LinearMap.sum_apply, symmetrizeLinear,
    LinearMap.coe_mk, AddHom.coe_mk, degreePieceLinear]
  unfold degreeTensor
  congr 1
  funext word
  exact Finset.sum_apply word Finset.univ (fun selected => degreePiece reference mass degree selected)

/-- Every degree and every color-word basis vector of the actual finite
marked Fock space, without choosing a basis of the centered subspace. -/
abbrev FockCoordinate (Slot Color : Type*) [Fintype Slot] :=
  Sigma (fun degree : Fin (Fintype.card Slot + 1) => Fin degree.val → Color)

/-- A single explicit linear channel whose counting norm is exactly the
marked coefficient budget. Scalar local-response estimates can therefore
be tensored directly on arbitrary joint input kernels. -/
def finiteFockChannel (reference : FiniteDist Color) (population : ℕ) (radius : ℝ) :
    ((Slot → Color) → ℝ) →ₗ[ℝ] (FockCoordinate Slot Color → ℝ) where
  toFun mass coordinate :=
    Real.sqrt ((Fintype.card Slot + 1 : ℕ) * (coordinate.1.val.factorial : ℝ) * 2 ^ coordinate.1.val) *
      (radius / Real.sqrt population) ^ coordinate.1.val *
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

/-- The whole marked Fock budget is exactly one ordinary finite Euclidean
squared norm, including all factorials and finite-population normalization. -/
theorem finiteFockChannel_energy (reference : FiniteDist Color) (population : ℕ) (radius : ℝ)
    (mass : (Slot → Color) → ℝ) :
    (∑ coordinate : FockCoordinate Slot Color, (finiteFockChannel reference population radius mass coordinate) ^ 2) =
      BlockProducts.taggedCoefficientEnergy reference mass population radius := by
  have hn (degree : ℕ) : (0 : ℝ) ≤ (Fintype.card Slot + 1 : ℕ) * (degree.factorial : ℝ) * 2 ^ degree := by positivity
  rw [Fintype.sum_sigma]
  simp only [finiteFockChannel, LinearMap.coe_mk, AddHom.coe_mk, mul_pow,
    Real.sq_sqrt (hn _)]
  unfold BlockProducts.taggedCoefficientEnergy TensorFock.normalizedTensor BlockFock.tensorEnergy
  rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro degree _
  simp only [mul_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro word _
  ring

end
end AFT.LocalTensors
