import CurrentAFT.CycleMeanMGF

/-! # The complete normalized cycle mean, retaining a fixed endpoint offset -/

namespace CurrentAFT.WholeCycleMGF

open AFT FiniteConcentration
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] CycleMeanMGF.classicalFinDecidableEq

variable {Scalar Hilbert : Type*} [Fintype Scalar]
  [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]

/-- The literal full finite expectation, with every cyclic difference and
the deterministic off-body endpoint contribution. -/
def normalizedTotalMoment (body population : ℕ) (source : FiniteDist Scalar)
    (response : Fin body → Scalar × Scalar → Hilbert) (offset : Hilbert) (parameter : ℝ) : ℝ :=
  (FiniteDist.independent (fun _ : Fin body => source)).expectation (fun latent =>
    Real.exp (parameter * ‖(Real.sqrt (population : ℝ))⁻¹ •
      ((∑ vertex : Fin body, response vertex
        (latent ((finRotate body).symm vertex), latent vertex)) + offset)‖ ^ 2))

/-- This vector is computed from actual pair-law means, not an assumed
conditional-moment bound. -/
def normalizedMean (body population : ℕ) (source : FiniteDist Scalar)
    (response : Fin body → Scalar × Scalar → Hilbert) (offset : Hilbert) : Hilbert :=
  (Real.sqrt (population : ℝ))⁻¹ •
    ((∑ vertex : Fin body, vectorMean (source.prod source) (response vertex)) + offset)

theorem total_moment_le (body population : ℕ) (source : FiniteDist Scalar)
    (response : Fin body → Scalar × Scalar → Hilbert) (offset : Hilbert)
    (parameter : ℝ) (hparameter : 0 ≤ parameter) :
    normalizedTotalMoment body population source response offset parameter ≤
      Real.exp (2 * parameter * ‖normalizedMean body population source response offset‖ ^ 2) *
        CycleMeanMGF.normalizedCycleMoment body population source response (2 * parameter) := by
  have hdecomposition (latent : Fin body → Scalar) :
      (Real.sqrt (population : ℝ))⁻¹ •
        ((∑ vertex : Fin body, response vertex
          (latent ((finRotate body).symm vertex), latent vertex)) + offset) =
      ((Real.sqrt (population : ℝ))⁻¹ • ∑ vertex : Fin body,
        (response vertex (latent ((finRotate body).symm vertex), latent vertex) -
          vectorMean (source.prod source) (response vertex))) +
        normalizedMean body population source response offset := by
    unfold normalizedMean
    rw [Finset.sum_sub_distrib, ← smul_add]
    congr 1
    abel
  have hpoint (latent : Fin body → Scalar) :
      Real.exp (parameter * ‖(Real.sqrt (population : ℝ))⁻¹ •
        ((∑ vertex : Fin body, response vertex
          (latent ((finRotate body).symm vertex), latent vertex)) + offset)‖ ^ 2) ≤
      Real.exp (2 * parameter * ‖normalizedMean body population source response offset‖ ^ 2) *
        Real.exp ((2 * parameter) * ‖(Real.sqrt (population : ℝ))⁻¹ • ∑ vertex : Fin body,
          (response vertex (latent ((finRotate body).symm vertex), latent vertex) -
            vectorMean (source.prod source) (response vertex))‖ ^ 2) := by
    rw [hdecomposition, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hnorm := norm_add_le
      ((Real.sqrt (population : ℝ))⁻¹ • ∑ vertex : Fin body,
        (response vertex (latent ((finRotate body).symm vertex), latent vertex) -
          vectorMean (source.prod source) (response vertex)))
      (normalizedMean body population source response offset)
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have htwo := sq_nonneg (‖(Real.sqrt (population : ℝ))⁻¹ • ∑ vertex : Fin body,
        (response vertex (latent ((finRotate body).symm vertex), latent vertex) -
          vectorMean (source.prod source) (response vertex))‖ -
        ‖normalizedMean body population source response offset‖)
    nlinarith [mul_le_mul_of_nonneg_left hsquare hparameter,
      mul_nonneg hparameter htwo]
  unfold normalizedTotalMoment CycleMeanMGF.normalizedCycleMoment FiniteDist.expectation
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun latent _ => (mul_le_mul_of_nonneg_left (hpoint latent)
    ((FiniteDist.independent (fun _ : Fin body => source)).nonneg latent)).trans_eq (by ring))

end

end CurrentAFT.WholeCycleMGF
