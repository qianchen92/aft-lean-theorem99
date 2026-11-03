import CurrentAFT.FinitePolynomialTensor

/-! # Exact root Fubini for joint physical polynomial channels -/
namespace CurrentAFT.RootPolynomialTensor
open AFT FinitePolynomialTensor
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
local instance classicalProdDecidableEq {First Second : Type*} : DecidableEq (First × Second) := Classical.decEq _

variable {Index : Type*} [Fintype Index] [DecidableEq Index]
  {RootData Control : Index → Type*} [∀ index, Fintype (RootData index)] [∀ index, Fintype (Control index)]
  {Value : Type*} [CommRing Value] [Algebra ℝ Value]

def sliceLinear (index : Index) (root : RootData index) :
    ((RootData index × Control index) → ℝ) →ₗ[ℝ] (Control index → ℝ) where
  toFun score control := score (root, control)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def averagedChannel (reference : ∀ index, FiniteDist (RootData index))
    (physical : ∀ index, RootData index → (Control index → ℝ) →ₗ[ℝ] Value) (index : Index) :
    ((RootData index × Control index) → ℝ) →ₗ[ℝ] Value :=
  ∑ root, (reference index).weight root • ((physical index root).comp (sliceLinear index root))

omit [Fintype Index] [DecidableEq Index] [∀ index, Fintype (Control index)] in
theorem averagedChannel_column (reference : ∀ index, FiniteDist (RootData index))
    (physical : ∀ index, RootData index → (Control index → ℝ) →ₗ[ℝ] Value)
    (index : Index) (point : RootData index × Control index) :
    averagedChannel reference physical index (Pi.single point 1) =
      (reference index).weight point.1 • physical index point.1 (Pi.single point.2 1) := by
  classical
  rcases point with ⟨pointRoot, pointControl⟩
  simp only [averagedChannel, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    sliceLinear, LinearMap.coe_mk, AddHom.coe_mk]
  change (∑ root, (reference index).weight root • physical index root
    (fun control => (Pi.single (pointRoot, pointControl) (1 : ℝ) : RootData index × Control index → ℝ) (root, control))) = _
  rw [Finset.sum_eq_single pointRoot]
  · congr 1
    congr 1
    funext control
    simp [Pi.single_apply]
  · intro root _ hne
    have hzero : (fun control => (Pi.single (pointRoot, pointControl) (1 : ℝ) : RootData index × Control index → ℝ) (root, control)) = 0 := by
      funext control
      simp [hne]
    rw [hzero, map_zero, smul_zero]
  · simp

def sourceEquiv : ((index : Index) → RootData index × Control index) ≃
    (((index : Index) → RootData index) × ((index : Index) → Control index)) where
  toFun word := (fun index => (word index).1, fun index => (word index).2)
  invFun word index := (word.1 index, word.2 index)
  left_inv _ := rfl
  right_inv _ := rfl

/-- All retained roots are integrated jointly with the original control
kernel. Neither the root density nor the control kernel must factor. -/
theorem synthesis_averaged
    (reference : ∀ index, FiniteDist (RootData index))
    (physical : ∀ index, RootData index → (Control index → ℝ) →ₗ[ℝ] Value)
    (input : ((index : Index) → RootData index × Control index) → ℝ) :
    synthesis (averagedChannel reference physical) input =
      ∑ roots : (index : Index) → RootData index, (∏ index, (reference index).weight (roots index)) •
        synthesis (fun index => physical index (roots index)) (fun controls => input (fun index => (roots index, controls index))) := by
  unfold synthesis
  simp only [averagedChannel_column, Finset.prod_smul, smul_smul, Finset.smul_sum]
  rw [← Fintype.sum_prod_type (f := fun pair : ((index : Index) → RootData index) × ((index : Index) → Control index) =>
    ((∏ index, (reference index).weight (pair.1 index)) * input (fun index => (pair.1 index, pair.2 index))) •
      ∏ index, physical index (pair.1 index) (Pi.single (pair.2 index) 1))]
  rw [← (sourceEquiv (RootData := RootData) (Control := Control)).sum_comp]
  apply Finset.sum_congr rfl
  intro source _
  simp only [sourceEquiv, Equiv.coe_fn_mk]
  rw [mul_comm]

end
end CurrentAFT.RootPolynomialTensor
