import CurrentAFT.RationalBackgroundDensities
import CurrentAFT.RationalBackgroundTable

/-! # The exact mixed free and queue certificate tables with rational leaves

These are the original primary/body coefficient data, before leading
endpoint evaluation.  The rational approximation is made in those data.
-/
namespace CurrentAFT.RationalBackgroundProgram
open AFT ControlCoordinates GradedControlAlgebra BackgroundFamilies ActualControls
  RationalBackgroundTable RationalBackgroundDensities
open scoped BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def free (security bits order : ℕ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  firstTable order (RationalBackgroundDensities.primary security bits) (RationalBackgroundDensities.body security bits)

def translation (security bits order : ℕ) (shift : ℤ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  firstTable order (fun color => RationalBackgroundDensities.primary security bits color+
    RationalBackgroundDensities.residual security bits shift color) (RationalBackgroundDensities.seed security bits shift)

noncomputable section
open scoped Classical
local instance programFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

theorem free_data (security order : ℕ) (horder : 1 ≤ order) :
    firstTable order (FringeCertificate.primaryCertificateDensity security)
      (fun color : SafePalette security => BackgroundCertificates.bodyCertificateDensity security color.val) =
      fun arity => (BackgroundFamilies.freeCertificate security order horder arity).val := by
  exact firstTable_actual (ProposalPrimary.primaryLaw security) (bodyReference security) order horder
    _ _ (FringeCertificate.primaryCertificateDensity_centered security)
    (BackgroundFamilies.safe_centered security _ (BackgroundCertificates.bodyCertificateDensity_centered security))

theorem translation_data (security order : ℕ) (horder : 1 ≤ order) (shift : ℤ) :
    firstTable order (fun color => FringeCertificate.primaryCertificateDensity security color+
      BackgroundTranslations.residualCertificateDensity security shift color)
      (fun color : SafePalette security => BackgroundTranslations.safeSeedDensity security shift color.val) =
      fun arity => (BackgroundFamilies.translationCertificate security order horder shift arity).val := by
  have hcenter : ∑ color, (ProposalPrimary.primaryLaw security).weight color*
      (FringeCertificate.primaryCertificateDensity security color+BackgroundTranslations.residualCertificateDensity security shift color)=0 := by
    simp only [mul_add, Finset.sum_add_distrib, FringeCertificate.primaryCertificateDensity_centered,
      BackgroundTranslations.residualCertificateDensity_centered, add_zero]
  rw [firstTable_actual (ProposalPrimary.primaryLaw security) (bodyReference security) order horder _ _ hcenter
    (BackgroundFamilies.safe_centered security _ (BackgroundTranslations.safeSeedDensity_centered security shift))]
  rw [primaryFamily_add _ _ _ _ _ _ (FringeCertificate.primaryCertificateDensity_centered security)
    (BackgroundTranslations.residualCertificateDensity_centered security shift) hcenter]
  rfl

def freeErrorConstant (security : ℕ) : ℝ := primaryErrorConstant security+bodyErrorConstant security

def translationErrorConstant (security : ℕ) : ℝ := primaryErrorConstant security+residualErrorConstant security+2*bodyErrorConstant security

theorem density_constants_nonneg (security : ℕ) : 0 ≤ primaryErrorConstant security ∧
    0 ≤ residualErrorConstant security ∧ 0 ≤ bodyErrorConstant security := by
  simp only [primaryErrorConstant, residualErrorConstant, bodyErrorConstant, centerErrorConstant,
    RationalMassLiftProgram.errorConstant, RationalTensorInverseProgram.actualBound,
    RationalDensityInverseProgram.inverseBound, RationalFirstResponseProgram.inverseErrorConstant]
  exact ⟨by positivity, by positivity, by positivity⟩

theorem free_error (security bits order : ℕ) (horder : 1 ≤ order)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(free security bits order arity (fun index => (colors index).val) (fun index => (centers index).val.val):ℝ)-
      (BackgroundFamilies.freeCertificate security order horder arity).val colors centers| ≤
      freeErrorConstant security*(1/(2:ℝ)^bits) := by
  rcases density_constants_nonneg security with ⟨hprimaryNonneg, hresidualNonneg, hbodyNonneg⟩
  have hx := firstTable_error order (RationalBackgroundDensities.primary security bits) (RationalBackgroundDensities.body security bits)
    (FringeCertificate.primaryCertificateDensity security)
    (fun color : SafePalette security => BackgroundCertificates.bodyCertificateDensity security color.val)
    Fin.val (fun color => color.val.val) (primaryErrorConstant security*(1/(2:ℝ)^bits)) (bodyErrorConstant security*(1/(2:ℝ)^bits))
    (by positivity) (by positivity)
    (fun color => RationalBackgroundDensities.primary_error security bits color hfirst hprecision hbudget)
    (fun color => RationalBackgroundDensities.body_error security bits color hprecision hbudget) arity colors centers
  rw [free_data security order horder] at hx
  exact hx.trans_eq (by unfold freeErrorConstant; ring)

theorem translation_error (security bits order : ℕ) (horder : 1 ≤ order) (shift : ℤ)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(translation security bits order shift arity (fun index => (colors index).val) (fun index => (centers index).val.val):ℝ)-
      (BackgroundFamilies.translationCertificate security order horder shift arity).val colors centers| ≤
      translationErrorConstant security*(1/(2:ℝ)^bits) := by
  rcases density_constants_nonneg security with ⟨hprimaryNonneg, hresidualNonneg, hbodyNonneg⟩
  have hp (color : FirstHistogram.Palette security) :
      |((RationalBackgroundDensities.primary security bits color.val+RationalBackgroundDensities.residual security bits shift color.val:ℚ):ℝ)-
        (FringeCertificate.primaryCertificateDensity security color+BackgroundTranslations.residualCertificateDensity security shift color)| ≤
      (primaryErrorConstant security+residualErrorConstant security)*(1/(2:ℝ)^bits) := by
    rw [Rat.cast_add]
    have he : (RationalBackgroundDensities.primary security bits color.val:ℝ)+(RationalBackgroundDensities.residual security bits shift color.val:ℝ)-
        (FringeCertificate.primaryCertificateDensity security color+BackgroundTranslations.residualCertificateDensity security shift color) =
        ((RationalBackgroundDensities.primary security bits color.val:ℝ)-FringeCertificate.primaryCertificateDensity security color)+
        ((RationalBackgroundDensities.residual security bits shift color.val:ℝ)-BackgroundTranslations.residualCertificateDensity security shift color) := by ring
    rw [he]
    exact (abs_add_le _ _).trans ((add_le_add
      (RationalBackgroundDensities.primary_error security bits color hfirst hprecision hbudget)
      (RationalBackgroundDensities.residual_error security bits shift color hfirst hprecision hbudget)).trans_eq (by ring))
  have hx := firstTable_error order
    (fun color => RationalBackgroundDensities.primary security bits color+RationalBackgroundDensities.residual security bits shift color)
    (RationalBackgroundDensities.seed security bits shift)
    (fun color => FringeCertificate.primaryCertificateDensity security color+BackgroundTranslations.residualCertificateDensity security shift color)
    (fun color : SafePalette security => BackgroundTranslations.safeSeedDensity security shift color.val)
    Fin.val (fun color => color.val.val)
    ((primaryErrorConstant security+residualErrorConstant security)*(1/(2:ℝ)^bits)) (2*bodyErrorConstant security*(1/(2:ℝ)^bits))
    (by positivity) (by positivity) hp
    (fun color => RationalBackgroundDensities.seed_error security bits shift color hprecision hbudget) arity colors centers
  rw [translation_data security order horder shift] at hx
  exact hx.trans_eq (by unfold translationErrorConstant; ring)

end
end CurrentAFT.RationalBackgroundProgram
