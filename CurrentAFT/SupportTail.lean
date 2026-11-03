import Mathlib

/-!
# Complete finite-frequency support tails

This module formalizes the tail extraction in the proof of
`prop:df-corrected-weight-bounds` in the current manuscript. It sums every
remaining frequency, including those of full support. The input weighted
energy bound and low-support cancellation must still be established for the
actual protected endpoint law; this module does not assert either physical
estimate or the constructive AFT theorem.
-/

namespace CurrentAFT

open scoped BigOperators

noncomputable section

/-- The complete weighted energy on a specified finite frequency set. -/
def weightedSupportEnergy {Frequency : Type*} (frequencies : Finset Frequency)
    (supportDegree : Frequency → ℕ) (energy : Frequency → ℝ) (radius : ℝ) : ℝ :=
  ∑ frequency ∈ frequencies, radius ^ (2 * supportDegree frequency) * energy frequency

/-- Exact cancellation through `order` and a radius at least one convert a
complete weighted-energy estimate into an unweighted estimate. No truncation
of the frequency sum is made. -/
theorem complete_support_tail {Frequency : Type*} (frequencies : Finset Frequency)
    (supportDegree : Frequency → ℕ) (energy : Frequency → ℝ)
    (order : ℕ) (radius : ℝ) (hradius : 1 ≤ radius)
    (hnonneg : ∀ frequency ∈ frequencies, 0 ≤ energy frequency)
    (hcancel : ∀ frequency ∈ frequencies,
      supportDegree frequency ≤ order → energy frequency = 0) :
    (∑ frequency ∈ frequencies, energy frequency) ≤
      weightedSupportEnergy frequencies supportDegree energy radius /
        radius ^ (2 * (order + 1)) := by
  have hpositive : 0 < radius := lt_of_lt_of_le zero_lt_one hradius
  apply (le_div_iff₀ (pow_pos hpositive _)).2
  rw [Finset.sum_mul]
  unfold weightedSupportEnergy
  apply Finset.sum_le_sum
  intro frequency hfrequency
  by_cases hsmall : supportDegree frequency ≤ order
  · simp [hcancel frequency hfrequency hsmall]
  · have hdegree : 2 * (order + 1) ≤ 2 * supportDegree frequency := by omega
    have hpowers := pow_le_pow_right₀ hradius hdegree
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_right hpowers (hnonneg frequency hfrequency)

/-- A bound on the whole weighted sum transfers without a factor counting
frequencies. This is stronger than separately bounding each coefficient. -/
theorem complete_support_tail_of_weighted_bound {Frequency : Type*}
    (frequencies : Finset Frequency) (supportDegree : Frequency → ℕ)
    (energy : Frequency → ℝ) (order : ℕ) (radius bound : ℝ)
    (hradius : 1 ≤ radius)
    (hnonneg : ∀ frequency ∈ frequencies, 0 ≤ energy frequency)
    (hcancel : ∀ frequency ∈ frequencies,
      supportDegree frequency ≤ order → energy frequency = 0)
    (hweighted : weightedSupportEnergy frequencies supportDegree energy radius ≤ bound) :
    (∑ frequency ∈ frequencies, energy frequency) ≤
      bound / radius ^ (2 * (order + 1)) := by
  apply (complete_support_tail frequencies supportDegree energy order radius
    hradius hnonneg hcancel).trans
  exact div_le_div_of_nonneg_right hweighted (pow_nonneg (by linarith) _)

/-- The spectral version uses squared complex coefficient norms and includes
all nonzero frequencies. `coefficient` may be the Fourier transform of a real
signed law; nonnegativity of the underlying law is not required here. -/
theorem complete_fourier_tail {Frequency : Type*} [Fintype Frequency]
    [DecidableEq Frequency] [Zero Frequency]
    (supportDegree : Frequency → ℕ) (coefficient : Frequency → ℂ)
    (order : ℕ) (radius : ℝ) (hradius : 1 ≤ radius)
    (hcancel : ∀ frequency, frequency ≠ 0 → supportDegree frequency ≤ order →
      coefficient frequency = 0) :
    (∑ frequency ∈ Finset.univ.erase (0 : Frequency), ‖coefficient frequency‖ ^ 2) ≤
      weightedSupportEnergy (Finset.univ.erase (0 : Frequency)) supportDegree
        (fun frequency => ‖coefficient frequency‖ ^ 2) radius /
          radius ^ (2 * (order + 1)) := by
  apply complete_support_tail _ _ _ _ _ hradius
  · intro frequency _
    positivity
  · intro frequency hfrequency hdegree
    have hzero := hcancel frequency (Finset.ne_of_mem_erase hfrequency) hdegree
    simp [hzero]

/-- The constant coefficient of a mass-one Fourier transform contributes
exactly one to the full weighted energy. Removing it yields the bound used
in the current manuscript. Mass one is represented here only by the
explicit zero-frequency coefficient identity; no Parseval claim is assumed. -/
theorem complete_fourier_tail_of_full_weighted_bound
    {Frequency : Type*} [Fintype Frequency] [DecidableEq Frequency] [Zero Frequency]
    (supportDegree : Frequency → ℕ) (coefficient : Frequency → ℂ)
    (order : ℕ) (radius bound : ℝ) (hradius : 1 ≤ radius)
    (hsupportZero : supportDegree 0 = 0) (hcoefficientZero : coefficient 0 = 1)
    (hcancel : ∀ frequency, frequency ≠ 0 → supportDegree frequency ≤ order →
      coefficient frequency = 0)
    (hweighted : weightedSupportEnergy Finset.univ supportDegree
      (fun frequency => ‖coefficient frequency‖ ^ 2) radius ≤ bound) :
    (∑ frequency ∈ Finset.univ.erase (0 : Frequency), ‖coefficient frequency‖ ^ 2) ≤
      (bound - 1) / radius ^ (2 * (order + 1)) := by
  have hremove : weightedSupportEnergy (Finset.univ.erase (0 : Frequency))
      supportDegree (fun frequency => ‖coefficient frequency‖ ^ 2) radius =
      weightedSupportEnergy Finset.univ supportDegree
        (fun frequency => ‖coefficient frequency‖ ^ 2) radius - 1 := by
    unfold weightedSupportEnergy
    have hsum := Finset.sum_erase_add (s := Finset.univ)
      (f := fun frequency => radius ^ (2 * supportDegree frequency) *
        ‖coefficient frequency‖ ^ 2) (Finset.mem_univ (0 : Frequency))
    simp only [hsupportZero, hcoefficientZero, mul_zero, pow_zero,
      norm_one, one_pow, mul_one] at hsum
    linarith
  apply complete_support_tail_of_weighted_bound _ _ _ _ _ _ hradius
  · intro frequency _
    positivity
  · intro frequency hfrequency hdegree
    simp [hcancel frequency (Finset.ne_of_mem_erase hfrequency) hdegree]
  · rw [hremove]
    linarith

end

end CurrentAFT
