import AFT.PolynomialTaggedFock
import AFT.LocalCoefficientLinear

/-! # Multiplying finite coefficient spaces without decomposing the input kernel -/

namespace AFT.JointFock

open MeasureTheory TensorFock NonlinearFock
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance jointFockSigmaDecEq {ι : Type*} {fiber : ι → Type*} : DecidableEq (Sigma fiber) := Classical.decEq _

variable {Index Color : Type*} [Fintype Index] [Fintype Color]
variable (Choice : Index → Type*) [∀ index, Fintype (Choice index)]
variable (Slots : (index : Index) → Choice index → Type*) [∀ index choice, Fintype (Slots index choice)]

/-- Local degree/word coordinates are exactly a choice of all local degrees
and one word on their disjoint union. This reindexing does not separate the
joint coefficient array into rank-one terms. -/
def coordinateEquiv :
    ((index : Index) → Sigma (fun choice : Choice index => Slots index choice → Color)) ≃
      Sigma (fun choice : (index : Index) → Choice index => (Sigma (fun index => Slots index (choice index))) → Color) where
  toFun point := ⟨(fun index => (point index).1), fun slot => (point slot.1).2 slot.2⟩
  invFun point := fun index => ⟨point.1 index, fun slot => point.2 ⟨index, slot⟩⟩
  left_inv point := by funext index; rfl
  right_inv point := by rcases point with ⟨choice, word⟩; rfl

/-- The homogeneous tensor for one vector of local degrees is just a slice
of the original arbitrary joint array. -/
def degreeTensor
    (coefficient : ((index : Index) → Sigma (fun choice : Choice index => Slots index choice → Color)) → ℝ)
    (choice : (index : Index) → Choice index) :
    BlockFock.Tensor (Sigma (fun index => Slots index (choice index))) Color :=
  fun word => coefficient (fun index => ⟨choice index, fun slot => word ⟨index, slot⟩⟩)

/-- The sum of all homogeneous tensor energies is the original array energy
exactly; there is no palette or nuclear-norm loss. -/
theorem degree_energy_sum
    (coefficient : ((index : Index) → Sigma (fun choice : Choice index => Slots index choice → Color)) → ℝ) :
    (∑ choice, BlockFock.tensorEnergy (degreeTensor Choice Slots coefficient choice)) =
      ∑ point, coefficient point ^ 2 := by
  have hh := (coordinateEquiv (Color := Color) Choice Slots).symm.sum_comp (fun point => coefficient point ^ 2)
  simpa only [Fintype.sum_sigma, coordinateEquiv, degreeTensor, BlockFock.tensorEnergy] using hh

/-- Evaluate the actual arbitrary joint array by multiplying the local
monomials at one shared Gaussian color vector. -/
def evaluation
    (coefficient : ((index : Index) → Sigma (fun choice : Choice index => Slots index choice → Color)) → ℝ)
    (value : Color → ℂ) : ℂ :=
  ∑ point, (coefficient point : ℂ) * ∏ index, wordMonomial (point index).2 value

theorem evaluation_eq_degree_sum
    (coefficient : ((index : Index) → Sigma (fun choice : Choice index => Slots index choice → Color)) → ℝ)
    (value : Color → ℂ) :
    evaluation Choice Slots coefficient value =
      ∑ choice, tensorEvaluation (degreeTensor Choice Slots coefficient choice) value := by
  have hh := (coordinateEquiv (Color := Color) Choice Slots).symm.sum_comp
    (fun point => (coefficient point : ℂ) * ∏ index, wordMonomial (point index).2 value)
  rw [evaluation, ← hh, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro choice _
  unfold tensorEvaluation degreeTensor wordMonomial
  apply Finset.sum_congr rfl
  intro word _
  simp only [coordinateEquiv, Fintype.prod_sigma]
  rfl

/-- Diagonal evaluation of all local Gaussian coefficient spaces is a
bounded Hilbert operation in every fixed degree. The constant depends only
on the degree choices and total degree, and applies to joint arrays. -/
theorem evaluation_energy_le
    (coefficient : ((index : Index) → Sigma (fun choice : Choice index => Slots index choice → Color)) → ℝ)
    (degreeBound : ℕ)
    (hdegree : ∀ choice : (index : Index) → Choice index,
      Fintype.card (Sigma (fun index => Slots index (choice index))) ≤ degreeBound) :
    (∫ value, Complex.normSq (evaluation Choice Slots coefficient value) ∂FockGaussian.field) ≤
      (Fintype.card ((index : Index) → Choice index) : ℝ) * (degreeBound.factorial : ℝ) *
        ∑ point, coefficient point ^ 2 := by
  let tensor := degreeTensor Choice Slots coefficient
  have hmem (choice : (index : Index) → Choice index) := tensor_memLp (tensor choice)
  have hint (choice : (index : Index) → Choice index) :
      Integrable (fun value => Complex.normSq (tensorEvaluation (tensor choice) value)) FockGaussian.field := by
    simpa only [← Complex.sq_norm] using
      (memLp_two_iff_integrable_sq_norm (hmem choice).aestronglyMeasurable).mp (hmem choice)
  have hleftmem := memLp_finset_sum Finset.univ
    (fun choice (_ : choice ∈ Finset.univ) => hmem choice)
  have hleft : Integrable (fun value => Complex.normSq (∑ choice, tensorEvaluation (tensor choice) value)) FockGaussian.field := by
    simpa only [← Complex.sq_norm] using
      (memLp_two_iff_integrable_sq_norm hleftmem.aestronglyMeasurable).mp hleftmem
  have hright := (integrable_finset_sum Finset.univ (fun choice _ => hint choice)).const_mul
    (Fintype.card ((index : Index) → Choice index) : ℝ)
  simp_rw [evaluation_eq_degree_sum]
  calc
    _ ≤ ∫ value, (Fintype.card ((index : Index) → Choice index) : ℝ) *
        ∑ choice, Complex.normSq (tensorEvaluation (tensor choice) value) ∂FockGaussian.field :=
      integral_mono hleft hright (fun value => by
        simpa only [Finset.card_univ] using TaggedFock.normSq_sum_le_card_sum Finset.univ
          (fun choice => tensorEvaluation (tensor choice) value))
    _ = (Fintype.card ((index : Index) → Choice index) : ℝ) *
        ∑ choice, ∫ value, Complex.normSq (tensorEvaluation (tensor choice) value) ∂FockGaussian.field := by
      rw [integral_const_mul, integral_finset_sum _ (fun choice _ => hint choice)]
    _ ≤ (Fintype.card ((index : Index) → Choice index) : ℝ) *
        ∑ choice, (degreeBound.factorial : ℝ) * BlockFock.tensorEnergy (tensor choice) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro choice _
      apply (tensor_gaussian_energy_le (tensor choice)).trans
      apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      exact_mod_cast Nat.factorial_le (hdegree choice)
    _ = _ := by rw [← Finset.mul_sum, degree_energy_sum]; ring

end
end AFT.JointFock
