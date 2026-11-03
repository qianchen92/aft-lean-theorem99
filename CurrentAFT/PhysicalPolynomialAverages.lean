import CurrentAFT.ActualWeightedFourier
import CurrentAFT.GradedControlAlgebra
import CurrentAFT.CycleRootExpansion
import AFT.CenteredGaussianEvaluation

/-! # Exact finite averages and relabelings of the physical output PGF -/
namespace CurrentAFT.PhysicalPolynomialAverages
open AFT AFT.RepresentedPolynomial HistogramNormalization GradedControlAlgebra
  ControlCoordinates CycleRootExpansion
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem generating_renamed {Slot OtherSlot Color : Type*}
    [Fintype Slot] [Fintype OtherSlot] [Fintype Color]
    (reference : Color → ℝ) (equiv : Slot ≃ OtherSlot) (mass : (Slot → Color) → ℝ) :
    centeredGeneratingLinear reference (renamedMass equiv mass) =
      centeredGeneratingLinear reference mass := by
  unfold centeredGeneratingLinear
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [← (renameWord equiv).sum_comp]
  apply Finset.sum_congr rfl
  intro word _
  have hword : renamedMass equiv mass (renameWord equiv word) = mass word := by
    simp only [renamedMass, renameWord, Equiv.coe_fn_mk, Function.comp_def, Equiv.symm_apply_apply]
  rw [hword]
  congr 1
  exact Equiv.prod_comp equiv.symm (fun slot => centeredFactor reference (word slot))

theorem generating_average {Source Slot Color : Type*}
    [Fintype Source] [Fintype Slot] [Fintype Color]
    (reference : Color → ℝ) (law : FiniteDist Source) (mass : Source → (Slot → Color) → ℝ) :
    centeredGeneratingLinear reference (fun word => law.expectation (fun source => mass source word)) =
      ∑ source, law.weight source • centeredGeneratingLinear reference (mass source) := by
  have hmass : (fun word => law.expectation (fun source => mass source word)) =
      ∑ source, law.weight source • mass source := by
    funext word
    simp only [FiniteDist.expectation, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hmass, map_sum]
  simp only [map_smul]

theorem expectationLinear_prod {First Second Value : Type*} [Fintype First] [Fintype Second]
    [AddCommGroup Value] [Module ℝ Value] (first : FiniteDist First) (second : FiniteDist Second)
    (test : First × Second → Value) :
    expectationLinear (first.prod second) test =
      expectationLinear first (fun left => expectationLinear second (fun right => test (left, right))) := by
  simp only [expectationLinear, LinearMap.coe_mk, AddHom.coe_mk, Fintype.sum_prod_type,
    FiniteDist.prod_weight, Finset.smul_sum, smul_smul]

theorem expectationLinear_const {Source Value : Type*} [Fintype Source]
    [AddCommGroup Value] [Module ℝ Value] (law : FiniteDist Source) (value : Value) :
    expectationLinear law (fun _ => value) = value := by
  change (∑ source, law.weight source • value) = value
  rw [← Finset.sum_smul, law.sum_one, one_smul]

theorem linear_expectation {Source Value Target : Type*} [Fintype Source]
    [AddCommGroup Value] [Module ℝ Value] [AddCommGroup Target] [Module ℝ Target]
    (channel : Value →ₗ[ℝ] Target) (law : FiniteDist Source) (test : Source → Value) :
    channel (expectationLinear law test) =
      expectationLinear law (fun source => channel (test source)) := by
  change channel (∑ source, law.weight source • test source) = _
  rw [map_sum]
  simp only [map_smul, expectationLinear, LinearMap.coe_mk, AddHom.coe_mk]

theorem expectationLinear_comm {First Second Value : Type*} [Fintype First] [Fintype Second]
    [AddCommGroup Value] [Module ℝ Value] (first : FiniteDist First) (second : FiniteDist Second)
    (test : First → Second → Value) :
    expectationLinear first (fun left => expectationLinear second (test left)) =
      expectationLinear second (fun right => expectationLinear first (fun left => test left right)) := by
  simp only [expectationLinear, LinearMap.coe_mk, AddHom.coe_mk, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro right _
  apply Finset.sum_congr rfl
  intro left _
  rw [mul_comm]

def arityOptionMap (order : ℕ) : Option (PositiveArity order) → TruncatedArity order
  | none => zeroArity order
  | some arity => positiveArity order arity

theorem arityOptionMap_bijective (order : ℕ) : Function.Bijective (arityOptionMap order) := by
  constructor
  · intro left right hequal
    cases left with
    | none =>
      cases right with
      | none => rfl
      | some arity =>
        have h := congrArg (fun a : TruncatedArity order => a.val.1.val + a.val.2.val) hequal
        have hp := arity.property.1
        change 0 + 0 = arity.val.1.val + arity.val.2.val at h
        omega
    | some arity =>
      cases right with
      | none =>
        have h := congrArg (fun a : TruncatedArity order => a.val.1.val + a.val.2.val) hequal
        have hp := arity.property.1
        change arity.val.1.val + arity.val.2.val = 0 + 0 at h
        omega
      | some other =>
        apply congrArg some
        apply Subtype.ext
        exact congrArg (fun a : TruncatedArity order => a.val) hequal
  · intro arity
    by_cases hzero : arity.val.1.val + arity.val.2.val = 0
    · refine ⟨none, ?_⟩
      apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext
      · change 0 = arity.val.1.val
        omega
      · change 0 = arity.val.2.val
        omega
    · exact ⟨some ⟨arity.val, ⟨by omega, arity.property⟩⟩, rfl⟩

theorem sum_arities {Value : Type*} [AddCommMonoid Value] (order : ℕ)
    (test : TruncatedArity order → Value) :
    (∑ arity, test arity) = test (zeroArity order) +
      ∑ arity : PositiveArity order, test (positiveArity order arity) := by
  rw [← (Equiv.ofBijective (arityOptionMap order) (arityOptionMap_bijective order)).sum_comp]
  exact Fintype.sum_option _

end
end CurrentAFT.PhysicalPolynomialAverages
