import CurrentAFT.RationalLegFamilyTable
import CurrentAFT.CalibrationCoordinateError

/-! # Actual point bounds for fixed-root local numerator coefficients

The estimates use the actual positive primary atoms, finite coefficient
extraction and the actual tensor inverse. No root probability is divided
out, and the resulting bounds are polynomials in current public parameters.
-/
namespace CurrentAFT.LegCoefficientPointBounds
open AFT DiffuseProfiles ProposalPrimary ActualControls CoefficientHilbert
  ControlCoordinates GradedControlAlgebra
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSubtypeDecidableEq {Index : Type*} (selected : Finset Index) : DecidableEq selected := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw

theorem ordered_density_bound (security : ℕ) (mass : (Fin 3 → Palette security) → ℝ)
    (selected : Finset (Fin 3)) (bound : ℝ) (hb : 0 ≤ bound) (hmass : ∀ word, |mass word| ≤ bound)
    (output : Fin selected.card → Palette security) :
    |RationalLegCoefficientExtraction.orderedDensity security mass selected output| ≤
      (Parameters.modulus security : ℝ)^3 * bound * (4 * (Parameters.modulus security : ℝ))^selected.card := by
  unfold RationalLegCoefficientExtraction.orderedDensity LocalTensors.referenceRestrictedComponent
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _word : Fin 3 → Palette security, bound * (4 * (Parameters.modulus security : ℝ))^selected.card := by
      apply Finset.sum_le_sum
      intro word _
      rw [abs_mul, Finset.abs_prod]
      apply mul_le_mul (hmass word) _ (Finset.prod_nonneg fun _ _ => abs_nonneg _) hb
      calc
        _ ≤ ∏ _slot : selected, 4 * (Parameters.modulus security : ℝ) :=
          Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun slot _ => RationalLegCoefficientExtraction.actual_atom_bound security _ _)
        _ = _ := by simp
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring

theorem tensor_bound (security degree : ℕ) (profile : (Fin degree → Palette security) → ℝ)
    (bound : ℝ) (hb : 0 ≤ bound) (hprofile : ∀ word, |profile word| ≤ bound)
    (output : Fin degree → Palette security) :
    |PrimaryTensorInverse.tensorInverse security degree profile output| ≤
      (Parameters.modulus security : ℝ)^degree * (RationalTensorInverseProgram.actualBound security)^degree * bound := by
  have h := RationalTensorInverseProgram.actual_tensor_difference security degree profile 0 bound hb
    (fun word => by simpa only [Pi.zero_apply, sub_zero] using hprofile word) output
  simpa only [map_zero, Pi.zero_apply, sub_zero] using h

theorem selected_kernel_bound (security : ℕ) (mass : (Fin 3 → Palette security) → ℝ)
    (selected : Finset (Fin 3)) (bound : ℝ) (hb : 0 ≤ bound) (hmass : ∀ word, |mass word| ≤ bound)
    (output : Fin selected.card → Palette security) (centers : Fin 0 → SafePalette security) :
    |(RootLegCoefficientFamily.selectedKernel security selected.card mass selected (by simp)).val output centers| ≤
      (Parameters.modulus security : ℝ)^selected.card * (RationalTensorInverseProgram.actualBound security)^selected.card *
        ((Parameters.modulus security : ℝ)^3 * bound * (4 * (Parameters.modulus security : ℝ))^selected.card) := by
  rw [RationalLegCoefficientExtraction.actual_selectedKernel_average]
  apply CalibrationCoordinateError.expectation_abs_bound
  intro permutation
  exact tensor_bound security selected.card _ _ (by positivity) (ordered_density_bound security mass selected bound hb hmass)
    (output ∘ permutation)

def selectedBound (security : ℕ) (massBound : ℝ) : ℝ :=
  (Parameters.modulus security : ℝ)^3 * (1 + RationalTensorInverseProgram.actualBound security)^3 *
    ((Parameters.modulus security : ℝ)^3 * massBound * (4 * (Parameters.modulus security : ℝ))^3)

theorem selectedBound_nonneg (security : ℕ) (bound : ℝ) (hb : 0 ≤ bound) : 0 ≤ selectedBound security bound := by
  unfold selectedBound
  positivity [RationalTensorInverseProgram.actualBound_nonneg security]

theorem selected_kernel_uniform (security : ℕ) (mass : (Fin 3 → Palette security) → ℝ)
    (selected : Finset (Fin 3)) (bound : ℝ) (hb : 0 ≤ bound) (hmass : ∀ word, |mass word| ≤ bound)
    (output : Fin selected.card → Palette security) (centers : Fin 0 → SafePalette security) :
    |(RootLegCoefficientFamily.selectedKernel security selected.card mass selected (by simp)).val output centers| ≤
      selectedBound security bound := by
  have hcard : selected.card ≤ 3 := (Finset.card_le_card (Finset.subset_univ selected)).trans_eq (by simp)
  have hq : (1 : ℝ) ≤ Parameters.modulus security := by
    exact_mod_cast (Parameters.modulus_spec security).2.two_le.trans' (by omega)
  have hM := RationalTensorInverseProgram.actualBound_nonneg security
  have hqpow := pow_le_pow_right₀ hq hcard
  have hfour : (1 : ℝ) ≤ 4 * (Parameters.modulus security : ℝ) := by linarith
  have hfourpow := pow_le_pow_right₀ hfour hcard
  have hMpow : (RationalTensorInverseProgram.actualBound security)^selected.card ≤
      (1 + RationalTensorInverseProgram.actualBound security)^3 :=
    (pow_le_pow_left₀ hM (show RationalTensorInverseProgram.actualBound security ≤
        1 + RationalTensorInverseProgram.actualBound security by linarith) selected.card).trans
      (pow_le_pow_right₀ (by linarith) hcard)
  apply (selected_kernel_bound security mass selected bound hb hmass output centers).trans
  exact mul_le_mul (mul_le_mul hqpow hMpow (pow_nonneg hM _) (by positivity))
    (mul_le_mul_of_nonneg_left hfourpow (by positivity)) (by positivity) (by positivity)

theorem inserted_bound (security order : ℕ) (mass : (Fin 3 → Palette security) → ℝ)
    (selected : Finset (Fin 3)) (bound : ℝ) (hb : 0 ≤ bound) (hmass : ∀ word, |mass word| ≤ bound)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(RootLegCoefficientFamily.selectedFamily security order mass selected arity).val colors centers| ≤ selectedBound security bound := by
  rw [← RationalLegFamilyTable.insertSelected_actual security order mass selected arity colors centers]
  unfold RationalLegFamilyTable.insertSelected
  split_ifs with hmatch
  · exact selected_kernel_uniform security mass selected bound hb hmass (colors ∘ finCongr hmatch.1) Fin.elim0
  · simpa only [abs_zero] using selectedBound_nonneg security bound hb

theorem selected_sum_bound (security order : ℕ) (mass : (Fin 3 → Palette security) → ℝ)
    (selectedSets : Finset (Finset (Fin 3))) (bound : ℝ) (hb : 0 ≤ bound) (hmass : ∀ word, |mass word| ≤ bound)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |∑ selected ∈ selectedSets, (RootLegCoefficientFamily.selectedFamily security order mass selected arity).val colors centers| ≤
      8 * selectedBound security bound := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _selected ∈ selectedSets, selectedBound security bound :=
      Finset.sum_le_sum (fun selected _ => inserted_bound security order mass selected bound hb hmass arity colors centers)
    _ ≤ _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (selectedBound_nonneg security bound hb)
      apply Nat.cast_le.mpr
      exact (Finset.card_le_card (Finset.subset_univ selectedSets)).trans_eq (by norm_num)

theorem higher_bound (security order : ℕ) (mass : (Fin 3 → Palette security) → ℝ)
    (bound : ℝ) (hb : 0 ≤ bound) (hmass : ∀ word, |mass word| ≤ bound)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(RootLegCoefficientLinear.higherFamilyLinear security order mass arity).val colors centers| ≤
      8 * selectedBound security bound := by
  rw [RootLegCoefficientLinear.higherFamilyLinear_apply]
  simpa only [RootLegCoefficientFamily.higherFamily, Finset.sum_apply, Submodule.coe_sum] using
    selected_sum_bound security order mass _ bound hb hmass arity colors centers

theorem positive_bound (security order : ℕ) (law : FiniteDist (Fin 3 → Palette security))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(RootLegNormalized.positiveFamily security order law arity).val colors centers| ≤
      1 + 8 * selectedBound security 1 := by
  unfold RootLegNormalized.positiveFamily RootLegNormalized.completeFamily
  rw [law.sum_one, one_smul]
  simp only [Pi.add_apply, Submodule.coe_add, Finset.sum_apply, Submodule.coe_sum]
  have hu : |((1 : RootLegCoefficientFamily.Family security order) arity).val colors centers| ≤ 1 := by
    rw [← congrFun (congrFun (congrFun
      (RationalFamilyProductProgram.unit_actual (primaryLaw security) (bodyReference security) order) arity) colors) centers]
    unfold RationalFamilyProductProgram.unit
    split_ifs <;> norm_num
  exact (abs_add_le _ _).trans (add_le_add hu (selected_sum_bound security order law.weight _ 1 (by norm_num)
    (fun word => by rw [abs_of_nonneg (law.nonneg word)]; exact law.atom_le_one word) arity colors centers))

end
end CurrentAFT.LegCoefficientPointBounds
