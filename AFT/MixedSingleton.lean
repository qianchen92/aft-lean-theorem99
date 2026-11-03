import AFT.MixedPair
import AFT.RepresentedPolynomial

/-! # Exact integrated and fixed fibers of a one-coordinate input -/

namespace AFT.MixedKernel

open scoped BigOperators Classical

noncomputable section

variable {Color : Type*} [Fintype Color]

def singletonKernel (kernel : Color → ℝ) (word : Fin 1 → Color) : ℝ := kernel (word 0)

theorem singleton_expectation (reference : FiniteDist Color) (kernel : Color → ℝ) :
    (FiniteDist.independent (fun _ : Fin 1 => reference)).expectation (singletonKernel kernel) =
      ∑ color, reference.weight color * kernel color := by
  unfold FiniteDist.expectation FiniteDist.independent
  rw [← Equiv.sum_comp (Equiv.funUnique (Fin 1) Color).symm]
  apply Finset.sum_congr rfl
  intro color _
  simp [singletonKernel]

theorem singleton_fiberSq_empty (reference : FiniteDist Color) (kernel : Color → ℝ) (values : Fin 1 → Color) :
    fiberSq (fun _ : Fin 1 => reference) (singletonKernel kernel) ∅ values = ∑ color, reference.weight color * kernel color ^ 2 := by
  unfold fiberSq FiniteDist.l2Sq
  convert singleton_expectation reference (fun color => kernel color ^ 2) using 1

theorem singleton_fiberSq_fixed (reference : FiniteDist Color) (kernel : Color → ℝ) (values : Fin 1 → Color) :
    fiberSq (fun _ : Fin 1 => reference) (singletonKernel kernel) {0} values = kernel (values 0)^2 := by
  unfold fiberSq FiniteDist.l2Sq
  have heq : (fun word : Fin 1 → Color => singletonKernel kernel (freeze {0} values word)^2) =
      fun _ => kernel (values 0)^2 := by
    funext word
    simp only [singletonKernel, freeze, Finset.mem_singleton, if_true]
  rw [heq]
  unfold FiniteDist.expectation
  rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

theorem singleton_activity_le (reference : FiniteDist Color) (kernel : Color → ℝ)
    (rate full fixed : ℝ) (hrate : 0 ≤ rate) (hfull : 0 ≤ full) (hfixed : 0 ≤ fixed)
    (hfullSq : (∑ color, reference.weight color * kernel color^2) ≤ full^2)
    (hpoint : ∀ color, |kernel color| ≤ fixed) :
    activity (fun _ : Fin 1 => rate) (fun _ => reference) (singletonKernel kernel) ≤ rate * (full + rate * fixed) := by
  have hnorm0 : fiberNorm (fun _ : Fin 1 => reference) (singletonKernel kernel) ∅ ≤ full := by
    apply (pi_norm_le_iff_of_nonneg hfull).mpr
    intro values
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), singleton_fiberSq_empty]
    exact (Real.sqrt_le_left hfull).mpr hfullSq
  have hnorm1 : fiberNorm (fun _ : Fin 1 => reference) (singletonKernel kernel) {0} ≤ fixed := by
    apply (pi_norm_le_iff_of_nonneg hfixed).mpr
    intro values
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), singleton_fiberSq_fixed, Real.sqrt_sq_eq_abs]
    exact hpoint _
  have hu : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide
  unfold activity
  rw [hu]
  simp only [Fin.prod_univ_one, Finset.sum_pair (by decide : (∅ : Finset (Fin 1)) ≠ {0}),
    Finset.prod_empty, Finset.prod_singleton, one_mul]
  exact mul_le_mul_of_nonneg_left (add_le_add hnorm0 (mul_le_mul_of_nonneg_left hnorm1 hrate)) hrate

end
end AFT.MixedKernel

namespace AFT.RepresentedPolynomial

open scoped BigOperators Classical

noncomputable section

variable {Color : Type*} [Fintype Color]

def primarySingletonInput (kernel : Color → ℝ) : InputSeed Color where
  primaryOrder := 1
  bodyOrder := 0
  kernel := MixedKernel.singletonKernel kernel

def bodySingletonInput (kernel : Color → ℝ) : InputSeed Color where
  primaryOrder := 0
  bodyOrder := 1
  kernel := MixedKernel.singletonKernel kernel

theorem primarySingletonInput_weight (kernel : Color → ℝ) (primary body : FiniteDist Color)
    (primaryPool bodyPool radius : ℝ) :
    inputWeight primary body primaryPool bodyPool radius (primarySingletonInput kernel) =
      MixedKernel.activity (fun _ : Fin 1 => (Real.sqrt primaryPool)⁻¹) (fun _ => primary) (MixedKernel.singletonKernel kernel) := by
  have hrate : inputRate primaryPool bodyPool (primarySingletonInput kernel) = fun _ : Fin 1 => (Real.sqrt primaryPool)⁻¹ := by
    funext i
    fin_cases i
    rfl
  have href : inputReference primary body (primarySingletonInput kernel) = fun _ : Fin 1 => primary := by
    funext i
    fin_cases i
    rfl
  unfold inputWeight MixedKernel.analyticActivity
  rw [hrate, href]
  simp only [primarySingletonInput, pow_zero, one_mul]
  rfl

theorem bodySingletonInput_weight (kernel : Color → ℝ) (primary body : FiniteDist Color)
    (primaryPool bodyPool radius : ℝ) :
    inputWeight primary body primaryPool bodyPool radius (bodySingletonInput kernel) =
      radius * MixedKernel.activity (fun _ : Fin 1 => (Real.sqrt bodyPool)⁻¹) (fun _ => body) (MixedKernel.singletonKernel kernel) := by
  have hrate : inputRate primaryPool bodyPool (bodySingletonInput kernel) = fun _ : Fin 1 => (Real.sqrt bodyPool)⁻¹ := by
    funext i
    fin_cases i
    rfl
  have href : inputReference primary body (bodySingletonInput kernel) = fun _ : Fin 1 => body := by
    funext i
    fin_cases i
    rfl
  unfold inputWeight MixedKernel.analyticActivity
  rw [hrate, href]
  simp only [bodySingletonInput, pow_one]
  rfl

end
end AFT.RepresentedPolynomial
