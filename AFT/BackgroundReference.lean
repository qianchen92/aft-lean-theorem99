import AFT.BackgroundMeans

/-! # The actual beta-dependent reference mean and its fringe mass -/

namespace AFT

open scoped BigOperators Classical

noncomputable section

theorem uniformFiniteProfile_nonneg {ι : Type*} [DecidableEq ι] (support : Finset ι) (color : ι) :
    0 ≤ uniformFiniteProfile support color := by unfold uniformFiniteProfile; split <;> positivity

theorem uniformFiniteProfile_mass_le_one {ι : Type*} [Fintype ι] [DecidableEq ι] (support : Finset ι) :
    (∑ color, uniformFiniteProfile support color) ≤ 1 := by
  by_cases hs : support.Nonempty
  · exact le_of_eq (uniformFiniteProfile_mass support hs)
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs, uniformFiniteProfile]

theorem uniformFiniteProfile_difference_l1_le_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    (first second : Finset ι) :
    (∑ color, |uniformFiniteProfile first color - uniformFiniteProfile second color|) ≤ 2 := by
  calc
    _ ≤ ∑ color, (uniformFiniteProfile first color + uniformFiniteProfile second color) := by
      apply Finset.sum_le_sum
      intro color _
      have h1 := uniformFiniteProfile_nonneg first color
      have h2 := uniformFiniteProfile_nonneg second color
      exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg h1, abs_of_nonneg h2])
    _ ≤ _ := by rw [Finset.sum_add_distrib]; linarith [uniformFiniteProfile_mass_le_one first,
      uniformFiniteProfile_mass_le_one second]

namespace V7Calibration

/-- The reference probability profile in the exact V7 calibration identity. -/
def referenceMean (parameter : ℕ) (cutoffScale beta : ℝ) (boundary : ℤ) :
    Fin (Parameters.modulus parameter) → ℝ :=
  calibratedReferenceMean (Parameters.dimension parameter) (Parameters.legs parameter)
    (GaussianSource.v7Activation cutoffScale parameter)
    (repairedBoundaryMass parameter cutoffScale beta boundary - v7BaseBoundaryMass cutoffScale parameter boundary)
    (fun _ => 1 / (Parameters.modulus parameter : ℝ))
    (uniformFiniteProfile (boundaryPalette (Parameters.modulus parameter) boundary))
    (uniformFiniteProfile (boundaryPalette (Parameters.modulus parameter) boundary)ᶜ)

/-- The same beta repair appears in the primary and reference means. -/
theorem referenceMean_primary_difference {σ τ : Type*} [Fintype σ] [Fintype τ]
    (parameter : ℕ) (cutoffScale beta : ℝ) (boundary : ℤ)
    (bodyShifts : σ → ℤ) (bodyLaw : FiniteDist σ)
    (startsPlus startsMinus sources : τ → ℤ) (sourceLaw : FiniteDist τ)
    (color : Fin (Parameters.modulus parameter)) :
    referenceMean parameter cutoffScale beta boundary color =
      1 / (Parameters.modulus parameter : ℝ) +
      ((Parameters.legs parameter : ℝ) * GaussianSource.v7Activation cutoffScale parameter /
        Parameters.dimension parameter) *
      (primary parameter cutoffScale beta boundary bodyShifts bodyLaw startsPlus startsMinus sources sourceLaw color -
        basePrimary parameter cutoffScale boundary bodyShifts bodyLaw startsPlus startsMinus sources sourceLaw color) := by
  simp only [referenceMean, calibratedReferenceMean, primary, calibratedPrimaryProfile,
    Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- The beta-dependent reference mean changes only a boundary-sized amount
of total probability. This estimate uses its exact calibrated formula. -/
theorem referenceMean_l1_le (parameter : ℕ) (cutoffScale beta : ℝ) (boundary : ℤ)
    (hscale : 1 ≤ cutoffScale) (hp : 1 ≤ parameter)
    (hbetaLower : (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta)
    (hbetaUpper : beta ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    (∑ color, |referenceMean parameter cutoffScale beta boundary color -
      1 / (Parameters.modulus parameter : ℝ)|) ≤
      2 * ((boundaryPalette (Parameters.modulus parameter) boundary).card : ℝ) / Parameters.modulus parameter := by
  have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hx : 0 < Parameters.security parameter := lt_of_lt_of_le (by decide : 0 < 2) (Parameters.security_ge_two parameter)
  have hm : (0 : ℝ) < Parameters.legs parameter := by unfold Parameters.legs; positivity
  have hn : (0 : ℝ) < Parameters.dimension parameter := by
    exact_mod_cast Nat.mul_pos (Parameters.modulus_prime parameter).pos (pow_pos hx 20)
  have ha : 0 < GaussianSource.v7Activation cutoffScale parameter :=
    GaussianSource.activation_positive _ _ _ _ (GaussianSource.legFeatureCount_positive cutoffScale parameter hscale hp)
  have hmass := beta_boundary_mass_bounds (Parameters.dimension parameter) (Parameters.legs parameter)
    (GaussianSource.v7Activation cutoffScale parameter)
    ((boundaryPalette (Parameters.modulus parameter) boundary).card / (Parameters.modulus parameter : ℝ))
    beta hn hm ha (by positivity) hbetaLower hbetaUpper
  have hbase : (Parameters.dimension parameter : ℝ) *
      ((boundaryPalette (Parameters.modulus parameter) boundary).card / (Parameters.modulus parameter : ℝ)) /
      (Parameters.legs parameter * GaussianSource.v7Activation cutoffScale parameter) =
      v7BaseBoundaryMass cutoffScale parameter boundary := by unfold v7BaseBoundaryMass; ring
  rw [hbase] at hmass
  change v7BaseBoundaryMass cutoffScale parameter boundary / 2 ≤ repairedBoundaryMass parameter cutoffScale beta boundary ∧
    repairedBoundaryMass parameter cutoffScale beta boundary ≤ 2 * v7BaseBoundaryMass cutoffScale parameter boundary at hmass
  have hchange : |repairedBoundaryMass parameter cutoffScale beta boundary - v7BaseBoundaryMass cutoffScale parameter boundary| ≤
      v7BaseBoundaryMass cutoffScale parameter boundary := abs_le.mpr (by constructor <;> linarith [show 0 ≤ v7BaseBoundaryMass cutoffScale parameter boundary by unfold v7BaseBoundaryMass; positivity])
  have hcoeff0 : 0 ≤ (Parameters.legs parameter : ℝ) * GaussianSource.v7Activation cutoffScale parameter /
      Parameters.dimension parameter := by positivity
  have hformula (color : Fin (Parameters.modulus parameter)) :
      |referenceMean parameter cutoffScale beta boundary color - 1 / (Parameters.modulus parameter : ℝ)| =
      ((Parameters.legs parameter : ℝ) * GaussianSource.v7Activation cutoffScale parameter / Parameters.dimension parameter) *
        |repairedBoundaryMass parameter cutoffScale beta boundary - v7BaseBoundaryMass cutoffScale parameter boundary| *
        |uniformFiniteProfile (boundaryPalette (Parameters.modulus parameter) boundary) color -
          uniformFiniteProfile (boundaryPalette (Parameters.modulus parameter) boundary)ᶜ color| := by
    unfold referenceMean calibratedReferenceMean
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, add_sub_cancel_left]
    rw [mul_div_assoc, div_mul_eq_mul_div, abs_mul, abs_mul]
    simp only [abs_mul, abs_div, abs_of_pos hm, abs_of_pos ha, abs_of_pos hn]
    ring
  simp_rw [hformula]
  rw [← Finset.mul_sum]
  calc
    _ ≤ (((Parameters.legs parameter : ℝ) * GaussianSource.v7Activation cutoffScale parameter /
        Parameters.dimension parameter) * v7BaseBoundaryMass cutoffScale parameter boundary) * 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hchange hcoeff0)
        (uniformFiniteProfile_difference_l1_le_two _ _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (by unfold v7BaseBoundaryMass; positivity)
    _ = _ := by unfold v7BaseBoundaryMass; field_simp

end V7Calibration

end

end AFT
