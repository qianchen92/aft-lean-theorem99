import AFT.ReferenceProbability

/-! # Actual V7 reference probabilities with legal small-parameter fallbacks -/

namespace AFT.V7Calibration

open Filter GaussianSource
open scoped BigOperators Classical Topology

noncomputable section

/-- A finite probability with specified weights whenever those weights are
nonnegative and normalized. The fallback is used only outside that domain. -/
def probabilityOr {Color : Type*} [Fintype Color] (profile : Color → ℝ)
    (fallback : FiniteDist Color) : FiniteDist Color :=
  if h : (∀ color, 0 ≤ profile color) ∧ (∑ color, profile color) = 1 then
    ⟨profile, h.1, h.2⟩ else fallback

theorem probabilityOr_weight {Color : Type*} [Fintype Color] (profile : Color → ℝ)
    (fallback : FiniteDist Color)
    (h : (∀ color, 0 ≤ profile color) ∧ (∑ color, profile color) = 1) :
    (probabilityOr profile fallback).weight = profile := by simp [probabilityOr, h]

def actualPrimaryLaw (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) :
    FiniteDist (Fin (Parameters.modulus parameter)) :=
  probabilityOr (actualPrimary cutoffScale parameter beta) (actualCoreLaw parameter)

def actualBodyLaw (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) :
    FiniteDist (Fin (Parameters.modulus parameter)) :=
  probabilityOr (actualBodyCenter cutoffScale parameter beta) (actualCoreLaw parameter)

def actualReferenceLaw (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) :
    FiniteDist (Fin (Parameters.modulus parameter)) :=
  probabilityOr (actualReferenceMean cutoffScale parameter beta) (actualCoreLaw parameter)

theorem actual_reference_laws_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight = actualPrimary cutoffScale parameter (beta parameter) ∧
      (actualBodyLaw cutoffScale parameter (beta parameter)).weight = actualBodyCenter cutoffScale parameter (beta parameter) ∧
      (actualReferenceLaw cutoffScale parameter (beta parameter)).weight = actualReferenceMean cutoffScale parameter (beta parameter) := by
  filter_upwards [actual_primary_probability_eventually cutoffScale hscale beta hbeta,
    actual_body_center_probability_eventually cutoffScale hscale beta hbeta,
    actual_reference_probability_eventually cutoffScale hscale beta hbeta] with parameter hp hb hr
  exact ⟨probabilityOr_weight _ _ ⟨fun color => (hp.1 color).le, hp.2⟩,
    probabilityOr_weight _ _ ⟨fun color => (div_nonneg ((actualCoreLaw parameter).nonneg color)
      (by norm_num)).trans (hb.2.1 color).1, hb.1⟩,
    probabilityOr_weight _ _ ⟨fun color => (hr.1 color).1, hr.2⟩⟩

end

end AFT.V7Calibration
