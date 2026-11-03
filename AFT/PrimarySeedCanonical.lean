import AFT.PrimarySeedInverse
import AFT.ActualResponseFormula

/-! # Canonicality of the real coordinate inverse seeds -/

namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

/-- Mass preservation in the acted coordinate, and linearity in every
other coordinate, preserve the complete canonical kernel. -/
theorem partialInputOperator_canonical (reference : Slot → FiniteDist Color) (slot : Slot)
    (operator : Module.End ℝ (Color → ℝ))
    (hpositive : ∀ color, (reference slot).weight color ≠ 0)
    (hmass : ∀ profile, (∑ color, operator profile color) = ∑ color, profile color)
    (kernel : (Slot → Color) → ℝ) (hcanonical : Hoeffding.Canonical reference Finset.univ kernel) :
    Hoeffding.Canonical reference Finset.univ
      (partialInputOperator slot operator (reference slot).weight kernel) := by
  cases Subsingleton.elim (inferInstance : DecidableEq Slot) (Classical.decEq Slot)
  constructor
  · intro first second h
    have heq : first = second := funext fun i => h i (Finset.mem_univ i)
    rw [heq]
  · intro other _ word
    by_cases heq : other = slot
    · subst other
      calc
        _ = ∑ color, operator (fun input => (reference slot).weight input*kernel (Function.update word slot input)) color := by
          apply Finset.sum_congr rfl
          intro color _
          simp only [partialInputOperator,Function.update_self,Function.update_idem]
          exact mul_div_cancel₀ _ (hpositive color)
        _ = ∑ color, (reference slot).weight color*kernel (Function.update word slot color) := hmass _
        _ = 0 := hcanonical.2 slot (Finset.mem_univ slot) word
    · let profiles : Color → Color → ℝ := fun value input =>
        (reference slot).weight input*kernel (Function.update (Function.update word other value) slot input)
      have hzero : (∑ value, (reference other).weight value • profiles value) = 0 := by
        funext input
        simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply,profiles,
          Function.update_comm heq]
        calc
          _ = (reference slot).weight input *
              ∑ value, (reference other).weight value*kernel (Function.update (Function.update word slot input) other value) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro value _
            ring
          _ = 0 := by rw [hcanonical.2 other (Finset.mem_univ other) (Function.update word slot input),mul_zero]
      have hoperator := congrArg (fun f : Color → ℝ => operator f (word slot)) hzero
      simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,map_zero,Pi.zero_apply] at hoperator
      calc
        _ = (∑ value, (reference other).weight value*operator (profiles value) (word slot)) / (reference slot).weight (word slot) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro value _
          simp only [partialInputOperator,Function.update_of_ne (Ne.symm heq)]
          dsimp only [profiles]
          ring
        _ = 0 := by rw [hoperator,zero_div]

theorem inputIteration_canonical (coordinates : List Slot) (operator : Slot → Module.End ℝ (Color → ℝ))
    (reference : Slot → FiniteDist Color)
    (hpositive : ∀ slot ∈ coordinates, ∀ color, (reference slot).weight color ≠ 0)
    (hmass : ∀ slot ∈ coordinates, ∀ profile, (∑ color, operator slot profile color) = ∑ color, profile color)
    (kernel : (Slot → Color) → ℝ) (hcanonical : Hoeffding.Canonical reference Finset.univ kernel) :
    Hoeffding.Canonical reference Finset.univ (inputIteration coordinates operator reference kernel) := by
  induction coordinates with
  | nil => exact hcanonical
  | cons slot tail ih =>
    rw [inputIteration_cons]
    exact partialInputOperator_canonical reference slot (operator slot)
      (hpositive slot (List.mem_cons_self ..)) (hmass slot (List.mem_cons_self ..)) _
      (ih (fun other h => hpositive other (List.mem_cons_of_mem _ h))
        (fun other h => hmass other (List.mem_cons_of_mem _ h)))

omit [DecidableEq Slot] in
theorem canonical_smul (reference : Slot → FiniteDist Color) (kernel : (Slot → Color) → ℝ)
    (scalar : ℝ) (hcanonical : Hoeffding.Canonical reference Finset.univ kernel) :
    Hoeffding.Canonical reference Finset.univ (scalar • kernel) := by
  constructor
  · intro first second h
    have heq : first = second := funext fun i => h i (Finset.mem_univ i)
    rw [heq]
  · intro slot _ word
    calc
      _ = scalar*(∑ color, (reference slot).weight color*kernel (Function.update word slot color)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro color _
        simp only [Pi.smul_apply,smul_eq_mul]
        ring
      _ = 0 := by rw [hcanonical.2 slot (Finset.mem_univ slot) word,mul_zero]

end
end AFT.MixedKernel

namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
variable {Color : Type*} [Fintype Color]

theorem inversePrimarySeed_canonical (primary body : FiniteDist Color) (rho : ℝ)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (seed : InputSeed Color)
    (hpositive : ∀ color, primary.weight color ≠ 0)
    (hmass : ∀ profile, (∑ color, operator.symm profile color) = ∑ color, profile color)
    (hcanonical : Hoeffding.Canonical (inputReference primary body seed) Finset.univ seed.kernel) :
    Hoeffding.Canonical (inputReference primary body (inversePrimarySeed primary body rho operator seed)) Finset.univ
      (inversePrimarySeed primary body rho operator seed).kernel := by
  apply MixedKernel.canonical_smul
  apply MixedKernel.inputIteration_canonical _ _ _ _ _ _ hcanonical
  · intro slot hs color
    rw [primaryCoordinates_reference primary body seed slot hs]
    exact hpositive color
  · intro slot _ profile
    exact hmass profile

end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open GaussianSource Filter RepresentedPolynomial
open scoped BigOperators Classical Topology
noncomputable section

theorem actual_primary_seed_canonical_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ)/(2*Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2*(Parameters.legs parameter : ℝ)/Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      ∀ operator : (Fin (Parameters.modulus parameter) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus parameter) → ℝ),
      operator.toLinearMap = actualResponse cutoffScale parameter →
      ∀ body : FiniteDist (Fin (Parameters.modulus parameter)), ∀ seed : InputSeed (Fin (Parameters.modulus parameter)),
      Hoeffding.Canonical (inputReference (actualPrimaryLaw cutoffScale parameter (beta parameter)) body seed) Finset.univ seed.kernel →
      Hoeffding.Canonical (inputReference (actualPrimaryLaw cutoffScale parameter (beta parameter)) body
          (inversePrimarySeed (actualPrimaryLaw cutoffScale parameter (beta parameter)) body (v7Activation cutoffScale parameter) operator seed))
        Finset.univ (inversePrimarySeed (actualPrimaryLaw cutoffScale parameter (beta parameter)) body
          (v7Activation cutoffScale parameter) operator seed).kernel := by
  filter_upwards [actualResponse_inverse_mass_eventually cutoffScale hscale,
    actual_primary_probability_eventually cutoffScale hscale beta hbeta,
    actual_reference_laws_eventually cutoffScale hscale beta hbeta] with parameter hm hp hl operator hop body seed hc
  apply inversePrimarySeed_canonical _ _ _ operator seed _ (hm operator hop) hc
  intro color
  rw [hl.1]
  exact (hp.1 color).ne'

end
end AFT.V7Calibration
