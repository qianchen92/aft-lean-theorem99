import AFT.Hoeffding
import CurrentAFT.CenteredCycleDensity

/-!
# Exact centering contraction with zero reference atoms

Full positivity of the reference palette is unnecessary. It suffices that
every input with nonzero signed mass lies on product-reference support.
The actual selected-root law has that property by its exact marginals.
-/

namespace CurrentAFT.SupportedHoeffding

open AFT
open scoped BigOperators Classical

noncomputable section

variable {Color Index : Type*} [Fintype Color] [Fintype Index]

/-- Only the source atom must be positive for its centered atom to average
zero. Other reference atoms may vanish. -/
theorem centeredAtom_mean_of_source_positive (reference : FiniteDist Color)
    (source : Color) (hsource : 0 < reference.weight source) :
    (∑ output, reference.weight output * Hoeffding.centeredAtom reference source output) = 0 := by
  simp only [Hoeffding.centeredAtom, mul_sub, mul_one, Finset.sum_sub_distrib, reference.sum_one]
  have hpoint (output : Color) :
      reference.weight output * (if source = output then (reference.weight output)⁻¹ else 0) =
        if source = output then (1 : ℝ) else 0 := by
    by_cases hequal : source = output
    · subst output
      simp [hsource.ne']
    · simp [hequal]
  simp_rw [hpoint]
  simp

/-- Canonicality of the actual component under support-only positivity. -/
theorem densityComponent_canonical_of_support (reference : Index → FiniteDist Color)
    (mass : (Index → Color) → ℝ)
    (hsupport : ∀ input, mass input ≠ 0 → ∀ index, 0 < (reference index).weight (input index))
    (selected : Finset Index) :
    Hoeffding.Canonical reference selected (Hoeffding.densityComponent reference mass selected) := by
  constructor
  · intro first second hagree
    unfold Hoeffding.densityComponent
    apply Finset.sum_congr rfl
    intro input _
    congr 1
    apply Finset.prod_congr rfl
    intro index hindex
    rw [hagree index hindex]
  · intro index hindex output
    simp only [Hoeffding.densityComponent, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro input _
    by_cases hzero : mass input = 0
    · simp [hzero]
    · have hproduct (color : Color) :
          (∏ other ∈ selected, Hoeffding.centeredAtom (reference other)
            (input other) (Function.update output index color other)) =
          Hoeffding.centeredAtom (reference index) (input index) color *
            ∏ other ∈ selected.erase index,
              Hoeffding.centeredAtom (reference other) (input other) (output other) := by
        rw [← Finset.mul_prod_erase _ _ hindex]
        simp only [Function.update_self]
        congr 1
        apply Finset.prod_congr rfl
        intro other hother
        rw [Function.update_of_ne (Finset.mem_erase.mp hother).1]
      simp_rw [hproduct]
      have hterm (color : Color) :
          (reference index).weight color * (mass input *
            (Hoeffding.centeredAtom (reference index) (input index) color *
              ∏ other ∈ selected.erase index,
                Hoeffding.centeredAtom (reference other) (input other) (output other))) =
          (mass input * ∏ other ∈ selected.erase index,
            Hoeffding.centeredAtom (reference other) (input other) (output other)) *
              ((reference index).weight color * Hoeffding.centeredAtom (reference index) (input index) color) := by ring
      simp_rw [hterm]
      rw [← Finset.mul_sum,
        centeredAtom_mean_of_source_positive (reference index) (input index) (hsupport input hzero index), mul_zero]

/-- Full finite Parseval now permits zero atoms, provided the signed input
is supported by the product reference. -/
theorem densityComponent_parseval_of_support (reference : Index → FiniteDist Color)
    (mass : (Index → Color) → ℝ)
    (hsupport : ∀ input, mass input ≠ 0 → ∀ index, 0 < (reference index).weight (input index)) :
    (FiniteDist.independent reference).l2Sq
      (fun output => mass output / (FiniteDist.independent reference).weight output) =
        ∑ selected : Finset Index, (FiniteDist.independent reference).l2Sq
          (Hoeffding.densityComponent reference mass selected) := by
  have h := Hoeffding.canonical_sum_l2Sq reference Finset.univ
    (Hoeffding.densityComponent reference mass)
    (fun selected _ => densityComponent_canonical_of_support reference mass hsupport selected)
  simpa only [Hoeffding.densityComponent_sum] using h

/-- The exact orthogonal-projection contraction used for full root centering. -/
theorem canonical_component_energy_le (reference : Index → FiniteDist Color)
    (mass : (Index → Color) → ℝ)
    (hsupport : ∀ input, mass input ≠ 0 → ∀ index, 0 < (reference index).weight (input index))
    (selected : Finset Index) :
    (FiniteDist.independent reference).l2Sq (Hoeffding.densityComponent reference mass selected) ≤
      (FiniteDist.independent reference).l2Sq
        (fun output => mass output / (FiniteDist.independent reference).weight output) := by
  rw [densityComponent_parseval_of_support reference mass hsupport]
  exact Finset.single_le_sum (fun _ _ => FiniteDist.l2Sq_nonneg _ _) (Finset.mem_univ selected)

/-- The current coefficient's atom formula agrees with the established
Hoeffding projection, including its convention at zero reference atoms. -/
theorem centeredRootAtom_eq (reference : FiniteDist Color) (input output : Color) :
    CycleSelections.centeredRootAtom reference input output = Hoeffding.centeredAtom reference input output := by
  unfold CycleSelections.centeredRootAtom Hoeffding.centeredAtom
  by_cases hequal : input = output <;> simp [hequal, div_eq_mul_inv]

/-- Pointwise identity of the actual current centered coefficient and the
full Hoeffding component of its genuine joint law. -/
theorem centeredRootDensity_eq_component [DecidableEq Index]
    (joint : FiniteDist (Index → Color)) (reference : Index → FiniteDist Color) (output : Index → Color) :
    CycleSelections.centeredRootDensity joint reference output =
      Hoeffding.densityComponent reference joint.weight Finset.univ output := by
  unfold CycleSelections.centeredRootDensity FiniteDist.expectation Hoeffding.densityComponent
  simp only [centeredRootAtom_eq]
  apply Finset.sum_congr (by ext; simp)
  intro input _
  congr 1

/-- Full centered-density contraction for the actual joint probability law,
with no pointwise positivity requirement outside its genuine support. -/
theorem centeredRootDensity_energy_le [DecidableEq Index]
    (joint : FiniteDist (Index → Color)) (reference : Index → FiniteDist Color)
    (hsupport : ∀ input, joint.weight input ≠ 0 → ∀ index, 0 < (reference index).weight (input index)) :
    (FiniteDist.independent reference).l2Sq (CycleSelections.centeredRootDensity joint reference) ≤
      (FiniteDist.independent reference).l2Sq
        (fun output => joint.weight output / (FiniteDist.independent reference).weight output) := by
  have hfunction : CycleSelections.centeredRootDensity joint reference =
      Hoeffding.densityComponent reference joint.weight Finset.univ :=
    funext (centeredRootDensity_eq_component joint reference)
  rw [hfunction]
  have h := canonical_component_energy_le reference joint.weight hsupport Finset.univ
  convert h using 1 <;>
    unfold FiniteDist.l2Sq FiniteDist.expectation FiniteDist.independent <;>
    apply Finset.sum_congr (by ext; simp) <;> intro output _ <;> rfl

end

end CurrentAFT.SupportedHoeffding
