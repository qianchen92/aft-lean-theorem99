import CurrentAFT.RationalLocalFamilyProgram

/-! # Actual point bounds for fixed-root local numerator coefficients

The estimates use the actual positive primary atoms, finite coefficient
extraction and the actual tensor inverse. No root probability is divided
out, and the resulting bounds are polynomials in current public parameters.
-/
namespace CurrentAFT.LocalCoefficientPointBounds
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

theorem ordered_density_bound (security : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (selected : Finset (Fin 4)) (bound : ℝ) (hb : 0 ≤ bound) (hmass : ∀ word, |mass word| ≤ bound)
    (output : Fin selected.card → Palette security) :
    |RationalCoefficientExtraction.orderedDensity security mass selected output| ≤
      (Parameters.modulus security : ℝ)^4 * bound * (4 * (Parameters.modulus security : ℝ))^selected.card := by
  unfold RationalCoefficientExtraction.orderedDensity LocalTensors.referenceRestrictedComponent
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _word : Fin 4 → Palette security, bound * (4 * (Parameters.modulus security : ℝ))^selected.card := by
      apply Finset.sum_le_sum
      intro word _
      rw [abs_mul, Finset.abs_prod]
      apply mul_le_mul (hmass word) _ (Finset.prod_nonneg fun _ _ => abs_nonneg _) hb
      calc
        _ ≤ ∏ _slot : selected, 4 * (Parameters.modulus security : ℝ) :=
          Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun slot _ => RationalCoefficientExtraction.actual_atom_bound security _ _)
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

theorem selected_kernel_bound (security : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (selected : Finset (Fin 4)) (bound : ℝ) (hb : 0 ≤ bound) (hmass : ∀ word, |mass word| ≤ bound)
    (output : Fin selected.card → Palette security) (centers : Fin 0 → SafePalette security) :
    |(LocalCoefficientFamily.selectedKernel security selected.card mass selected (by simp)).val output centers| ≤
      (Parameters.modulus security : ℝ)^selected.card * (RationalTensorInverseProgram.actualBound security)^selected.card *
        ((Parameters.modulus security : ℝ)^4 * bound * (4 * (Parameters.modulus security : ℝ))^selected.card) := by
  rw [RationalCoefficientExtraction.actual_selectedKernel_average]
  apply CalibrationCoordinateError.expectation_abs_bound
  intro permutation
  exact tensor_bound security selected.card _ _ (by positivity) (ordered_density_bound security mass selected bound hb hmass)
    (output ∘ permutation)

def selectedBound (security : ℕ) (massBound : ℝ) : ℝ :=
  (Parameters.modulus security : ℝ)^4 * (1 + RationalTensorInverseProgram.actualBound security)^4 *
    ((Parameters.modulus security : ℝ)^4 * massBound * (4 * (Parameters.modulus security : ℝ))^4)

theorem selectedBound_nonneg (security : ℕ) (bound : ℝ) (hb : 0 ≤ bound) : 0 ≤ selectedBound security bound := by
  unfold selectedBound
  positivity [RationalTensorInverseProgram.actualBound_nonneg security]

theorem selected_kernel_uniform (security : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (selected : Finset (Fin 4)) (bound : ℝ) (hb : 0 ≤ bound) (hmass : ∀ word, |mass word| ≤ bound)
    (output : Fin selected.card → Palette security) (centers : Fin 0 → SafePalette security) :
    |(LocalCoefficientFamily.selectedKernel security selected.card mass selected (by simp)).val output centers| ≤
      selectedBound security bound := by
  have hcard : selected.card ≤ 4 := (Finset.card_le_card (Finset.subset_univ selected)).trans_eq (by simp)
  have hq : (1 : ℝ) ≤ Parameters.modulus security := by
    exact_mod_cast (Parameters.modulus_spec security).2.two_le.trans' (by omega)
  have hM := RationalTensorInverseProgram.actualBound_nonneg security
  have hqpow := pow_le_pow_right₀ hq hcard
  have hfour : (1 : ℝ) ≤ 4 * (Parameters.modulus security : ℝ) := by linarith
  have hfourpow := pow_le_pow_right₀ hfour hcard
  have hMpow : (RationalTensorInverseProgram.actualBound security)^selected.card ≤
      (1 + RationalTensorInverseProgram.actualBound security)^4 :=
    (pow_le_pow_left₀ hM (show RationalTensorInverseProgram.actualBound security ≤
        1 + RationalTensorInverseProgram.actualBound security by linarith) selected.card).trans
      (pow_le_pow_right₀ (by linarith) hcard)
  apply (selected_kernel_bound security mass selected bound hb hmass output centers).trans
  exact mul_le_mul (mul_le_mul hqpow hMpow (pow_nonneg hM _) (by positivity))
    (mul_le_mul_of_nonneg_left hfourpow (by positivity)) (by positivity) (by positivity)

def numeratorBound (security : ℕ) : ℝ := 16 * selectedBound security (2 * (Parameters.modulus security : ℝ)^2)

theorem numeratorBound_nonneg (security : ℕ) : 0 ≤ numeratorBound security :=
  mul_nonneg (by norm_num) (selectedBound_nonneg security _ (by positivity))

theorem numerator_bound (security order : ℕ) (roots : RootTaggedSelected.RootPair security)
    (primaryColor : Palette security) (arity : TruncatedArity order)
    (colors : Fin arity.val.1.val → Palette security) (centers : Fin arity.val.2.val → SafePalette security) :
    |(LocalRaisingLinear.completeFamilyLinear security order
        (RootMassColumns.primaryMassAt security roots (centerLinear (primaryLaw security) (Pi.single primaryColor 1)))
          arity).val colors centers| ≤ numeratorBound security := by
  rw [RationalLocalFamilyProgram.completeFamily_zero_mass security order _
    (RationalLocalFamilyProgram.primaryMassAt_zero security roots primaryColor)]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _selected ∈ (Finset.univ : Finset (Finset (Fin 4))).erase ∅,
        selectedBound security (2 * (Parameters.modulus security : ℝ)^2) := by
      apply Finset.sum_le_sum
      intro selected _
      unfold RationalLocalFamilyProgram.insertSelected
      split_ifs with hmatch
      · exact selected_kernel_uniform security _ selected _ (by positivity)
          (fun word => by
            simpa only [mul_one] using RationalRootMassProgram.primaryMassAt_bound security roots
              (centerLinear (primaryLaw security) (Pi.single primaryColor 1)) 1 (by norm_num)
              (RationalPrimaryColumnProgram.actual_centerDelta_bound security primaryColor) word)
          (colors ∘ finCongr hmatch.1) Fin.elim0
      · simpa only [abs_zero] using selectedBound_nonneg security (2 * (Parameters.modulus security : ℝ)^2) (by positivity)
    _ ≤ _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (selectedBound_nonneg security _ (by positivity))
      apply Nat.cast_le.mpr
      calc
        _ ≤ (Finset.univ : Finset (Finset (Fin 4))).card := Finset.card_le_card (Finset.erase_subset ..)
        _ = 16 := by norm_num

end
end CurrentAFT.LocalCoefficientPointBounds
