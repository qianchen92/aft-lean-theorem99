import CurrentAFT.PrimaryMassFamilies
import CurrentAFT.BackgroundRates

/-! Concrete first-primary certificate for the actual primary-minus-uniform mass. -/

namespace CurrentAFT.PrimaryDeviationCertificate

open AFT ControlCoordinates GradedControlNorm DiffuseProfiles ProposalPrimary ActualControls FirstResponse
  FringeCertificate BackgroundRates PrimaryTensorInverse PrimaryMassFamilies BackgroundFamilies
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference BackgroundRates.primaryFactor

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def deviation (security : ℕ) : ActualControls.Palette security → ℝ :=
  (primaryLaw security).weight - uniformProfile security

theorem deviation_mass (security : ℕ) : ∑ color, deviation security color = 0 := by
  have hq := (FirstResponse.modulus_pos security).ne'
  simp only [deviation, Pi.sub_apply, uniformProfile, Finset.sum_sub_distrib, FiniteDist.sum_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  norm_num

theorem deviation_energy (security : ℕ) : profileSquareNorm (primaryLaw security).weight (deviation security) ≤ 6 := by
  have hself : profileSquareNorm (primaryLaw security).weight (primaryLaw security).weight = 1 := by
    unfold profileSquareNorm
    have hpoint (color : ActualControls.Palette security) :
        (primaryLaw security).weight color ^ 2 / (primaryLaw security).weight color = (primaryLaw security).weight color := by
      field_simp [(primaryReference_positive security color).ne']
    simp only [hpoint, FiniteDist.sum_one]
  have h := profileSquareNorm_sub_le_two security (primaryLaw security).weight (uniformProfile security)
  rw [hself] at h
  exact h.trans (by linarith [uniformProfile_square_le_two security])

def certificate (security order : ℕ) (horder : 1 ≤ order) : ActualFamily security order :=
  massCertificateFamily security order 1 horder (oneWordProfile (deviation security))
    (oneWordProfile_centered _ (deviation_mass security)) (oneWordProfile_symmetric _)

theorem certificate_leading (security order : ℕ) (horder : 1 ≤ order) :
    massLeading security 1 (fun colors => ((certificate security order horder)
      (PrimaryMassFamilies.primaryArity order 1 horder)).val colors Fin.elim0) = oneWordProfile (deviation security) :=
  massCertificateFamily_leading security order 1 horder (oneWordProfile (deviation security))
    (oneWordProfile_centered _ (deviation_mass security)) (oneWordProfile_symmetric _)

theorem certificate_norm (security order : ℕ) (horder : 1 ≤ order) :
    familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
      (certificate security order horder) ≤ 24 / (Parameters.base security : ℝ) ^ 63 := by
  have hb := FirstResponse.base_pos security
  have ha := activation_pos security
  have hp : 0 ≤ primaryFactor security := by unfold primaryFactor; positivity
  have hinv : 2 / activation security ≤ 8 * (Parameters.base security : ℝ) := by
    have h := mul_le_mul_of_nonneg_left (activation_inverse_le security) (show (0 : ℝ) ≤ 2 by norm_num)
    convert h using 1 <;> ring
  have henergyEq : massEnergy security 1 (oneWordProfile (deviation security)) =
      profileSquareNorm (primaryLaw security).weight (deviation security) :=
    oneWordProfile_energy (primaryLaw security).weight (deviation security)
  have henergy : massEnergy security 1 (oneWordProfile (deviation security)) ≤ 6 :=
    henergyEq.le.trans (deviation_energy security)
  have hsqrt : Real.sqrt (massEnergy security 1 (oneWordProfile (deviation security))) ≤ 3 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, henergy.trans (by norm_num)⟩
  have h := massCertificateFamily_norm security order 1 horder (primaryFactor security) (bodyFactor security) hp
    (oneWordProfile (deviation security)) (oneWordProfile_centered _ (deviation_mass security)) (oneWordProfile_symmetric _)
  simp only [pow_one] at h
  calc
    _ ≤ primaryFactor security * (2 / activation security) * Real.sqrt (massEnergy security 1 (oneWordProfile (deviation security))) := h
    _ ≤ (1 / (Parameters.base security : ℝ) ^ 64) * (8 * (Parameters.base security : ℝ)) * 3 :=
      mul_le_mul (mul_le_mul (le_of_eq (primaryFactor_eq security)) hinv (by positivity) (by positivity))
        hsqrt (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by field_simp; norm_num

end

end CurrentAFT.PrimaryDeviationCertificate
