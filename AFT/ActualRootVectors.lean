import AFT.V7Blocks
import AFT.ActualTripleMarginals
import AFT.ProfileHilbert

/-! # The true root-dependent part of each physical block's first coefficient -/

namespace AFT.V7Calibration

open Filter GaussianSource ProfileHilbert FiniteConcentration
open scoped BigOperators Classical Topology

noncomputable section

local instance actualRootVectorsFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance actualRootVectorsSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _

/-- The actual body's marginal at a fixed root and realized common-queue
shift. Attached bodies average the very same second source as their endpoints. -/
def actualBlockBodyLaw (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (index : blockIndex parameter) (root queue : ℤ) : FiniteDist (Fin (Parameters.modulus parameter)) :=
  match index with
  | .inl _ => (windowGaussian (10 * parameter) (legCutoff cutoffScale parameter - 1)).mix
      (fun source => actualShiftedBodyLaw cutoffScale parameter beta (root + source + queue))
  | .inr _ => actualShiftedBodyLaw cutoffScale parameter beta (root + queue)

/-- The finite Hilbert vector used in the conditional root sum. -/
def actualBlockBodyVector (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (index : blockIndex parameter) (root queue : ℤ) : EuclideanSpace ℝ (Fin (Parameters.modulus parameter)) :=
  whiten (actualReferenceLaw cutoffScale parameter beta).weight
    (fun color => (actualBlockBodyLaw cutoffScale parameter beta index root queue).weight color -
      (actualReferenceLaw cutoffScale parameter beta).weight color)

/-- This is exactly the attached marginal of the genuine triple. -/
theorem actualBlockBodyLaw_attached (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (leg : Fin (Parameters.legs parameter)) (root queue : ℤ) :
    (actualFixedRootTripleLaw cutoffScale parameter beta root queue).map (fun word => word 2) =
      actualBlockBodyLaw cutoffScale parameter beta (.inl leg) root queue := by
  ext color
  exact actual_fixed_root_triple_body_marginal cutoffScale parameter beta root queue color

/-- The exact source mixture preserves the small physical singleton norm;
all legal roots and all legal queue shifts are covered uniformly. -/
theorem actual_body_vector_bound_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ index : blockIndex parameter, ∀ root queue : ℤ,
      |root| ≤ (v7RootCutoff parameter : ℤ) → |queue| ≤ (queueCutoff parameter : ℤ) →
      ‖actualBlockBodyVector cutoffScale parameter (beta parameter) index root queue‖ ≤
        74 / (parameter : ℝ) ^ 19 := by
  filter_upwards [actual_shifted_body_reference_energy_eventually cutoffScale hscale beta hbeta,
    actual_shifted_body_law_eventually cutoffScale hscale beta hbeta,
    actual_reference_laws_eventually cutoffScale hscale beta hbeta, eventually_ge_atTop 1]
    with parameter he hl hr hp index root queue hroot hqueue
  have hpositive : (0 : ℝ) < parameter := by exact_mod_cast hp
  have hsingle (shift : ℤ) (hs : |shift| ≤ (maxBodyShift cutoffScale parameter : ℤ)) :
      ‖whiten (actualReferenceLaw cutoffScale parameter (beta parameter)).weight
        (fun color => (actualShiftedBodyLaw cutoffScale parameter (beta parameter) shift).weight color -
          (actualReferenceLaw cutoffScale parameter (beta parameter)).weight color)‖ ≤
        74 / (parameter : ℝ) ^ 19 := by
    have hsquare : ‖whiten (actualReferenceLaw cutoffScale parameter (beta parameter)).weight
        (fun color => (actualShiftedBodyLaw cutoffScale parameter (beta parameter) shift).weight color -
          (actualReferenceLaw cutoffScale parameter (beta parameter)).weight color)‖ ^ 2 ≤
        5472 / (parameter : ℝ) ^ 38 := by
      rw [whiten_norm_sq _ _ (actualReferenceLaw cutoffScale parameter (beta parameter)).nonneg,
        (hl shift hs).1, hr.2.2]
      exact he shift hs
    have heq : (74 / (parameter : ℝ) ^ 19) ^ 2 = 5476 / (parameter : ℝ) ^ 38 := by
      field_simp
      ring
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [heq]
    exact hsquare.trans (div_le_div_of_nonneg_right (by norm_num) (by positivity))
  cases index with
  | inl leg =>
    unfold actualBlockBodyVector actualBlockBodyLaw
    rw [whiten_mixture_centered]
    apply vectorMean_norm_le
    intro source
    exact hsingle _ (actualBodyBranch_shift_bound cutoffScale parameter root queue hroot hqueue (.inr source))
  | inr body =>
    exact hsingle _ (by simpa only [actualSourceShift, add_zero] using
      actualBodyBranch_shift_bound cutoffScale parameter root queue hroot hqueue (.inl ()))

end

end AFT.V7Calibration
