import CurrentAFT.RationalBackgroundDensities
import CurrentAFT.MarkedPairLeading

/-! # The original marked mixed seed, evaluated in the rational references -/
namespace CurrentAFT.RationalMarkedSeedProgram
open AFT RationalNumerics DiffuseProfiles ProposalPrimary ActualControls MarkedPairSeed MarkedPairLeading
open scoped BigOperators
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base PublicParameterProgram.modulus primaryLaw centerLaw

abbrev colors (security : ℕ) := (PublicParameterProgram.modulus security).count

def fixedAnchor (security primary : ℕ) (scalar : ℤ) (output : ℕ) : ℚ :=
  RationalProposalProgram.anchorKernel (colors security) ((security+2)^48) primary (-scalar) output

def rawDensity (security bits primary : ℕ) (scalar : ℤ) (output : ℕ) : ℚ :=
  fixedAnchor security primary scalar output/RationalProposalProgram.center security bits output

def secondCentered (security bits primary : ℕ) (scalar : ℤ) (output : ℕ) : ℚ :=
  rawDensity security bits primary scalar output-1

def secondMean (security bits : ℕ) (scalar : ℤ) (output : ℕ) : ℚ :=
  ∑ primary : Fin (colors security), RationalProposalProgram.primary security bits primary.val*
    secondCentered security bits primary.val scalar output

def uniformRelative (security bits primary : ℕ) : ℚ :=
  (1/(colors security:ℚ))/RationalProposalProgram.primary security bits primary

def seedDensity (security bits primary : ℕ) (scalar : ℤ) (output : ℕ) : ℚ :=
  secondCentered security bits primary scalar output-uniformRelative security bits primary*secondMean security bits scalar output

def inverseDensity (security bits : ℕ) (scalar : ℤ) (primary center : ℕ) : ℚ :=
  RationalDensityInverseProgram.current security bits (fun color => seedDensity security bits color scalar center) primary

noncomputable section
open scoped Classical

theorem fixedAnchor_cast (security : ℕ) (scalar : MarkedPairSeed.Scalar security)
    (primary output : FirstHistogram.Palette security) :
    (fixedAnchor security primary.val scalar.val output.val:ℝ) = (MarkedPairLeading.paletteAnchor security scalar primary).weight output := by
  unfold fixedAnchor
  rw [colors, PublicParameterProgram.modulus_value]
  have hA : (security+2)^48 = Parameters.anchorWidth security := by simp only [anchorWidth_eq, Parameters.base]
  rw [hA]
  exact RationalProposalProgram.anchorKernel_cast security primary output (-scalar.val)
    (by simpa only [abs_neg] using InwardAnchor.scalar_bound security scalar)

theorem rawDensity_error (security bits : ℕ) (scalar : MarkedPairSeed.Scalar security)
    (primary : FirstHistogram.Palette security) (output : SafePalette security)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ))) :
    |(rawDensity security bits primary.val scalar.val output.val.val:ℝ)-MarkedPairSeed.rawDensity security scalar primary output| ≤
      RationalBackgroundDensities.bodyErrorConstant security*(1/(2:ℝ)^bits) := by
  have hx := RationalBackgroundDensities.safe_quotient_error security bits (fixedAnchor security primary.val scalar.val)
    (MarkedPairLeading.paletteAnchor security scalar primary).weight 1 (by norm_num)
    (fixedAnchor_cast security scalar primary)
    (fun color => by
      rw [abs_of_nonneg ((MarkedPairLeading.paletteAnchor security scalar primary).nonneg color)]
      exact (MarkedPairLeading.paletteAnchor security scalar primary).atom_le_one color)
    output hprecision hbudget
  simpa only [rawDensity, MarkedPairSeed.rawDensity, one_mul] using hx

theorem rawDensity_bound (security bits : ℕ) (scalar : MarkedPairSeed.Scalar security)
    (primary : FirstHistogram.Palette security) (output : SafePalette security) :
    |(rawDensity security bits primary.val scalar.val output.val.val:ℝ)| ≤ 2*(Parameters.modulus security:ℝ) := by
  have hq := FirstResponse.modulus_pos security
  have hl := RationalProposalProgram.center_lower_safe security bits output
  have hp : 0 < (RationalProposalProgram.center security bits output.val.val:ℝ) := (by positivity : (0:ℝ)<1/(2*(Parameters.modulus security:ℝ))).trans_le hl
  rw [rawDensity, Rat.cast_div, fixedAnchor_cast, abs_div,
    abs_of_nonneg ((MarkedPairLeading.paletteAnchor security scalar primary).nonneg output.val), abs_of_pos hp]
  calc
    _ ≤ 1/(RationalProposalProgram.center security bits output.val.val:ℝ) :=
      div_le_div_of_nonneg_right ((MarkedPairLeading.paletteAnchor security scalar primary).atom_le_one output.val) hp.le
    _ ≤ 1/(1/(2*(Parameters.modulus security:ℝ))) := one_div_le_one_div_of_le (by positivity) hl
    _ = _ := by field_simp

theorem secondCentered_bound (security bits : ℕ) (scalar : MarkedPairSeed.Scalar security)
    (primary : FirstHistogram.Palette security) (output : SafePalette security) :
    |(secondCentered security bits primary.val scalar.val output.val.val:ℝ)| ≤ 2*(Parameters.modulus security:ℝ)+1 := by
  rw [secondCentered, Rat.cast_sub, Rat.cast_one]
  exact (abs_sub _ _).trans (add_le_add (rawDensity_bound security bits scalar primary output) (by norm_num))

theorem secondCentered_error (security bits : ℕ) (scalar : MarkedPairSeed.Scalar security)
    (primary : FirstHistogram.Palette security) (output : SafePalette security)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ))) :
    |(secondCentered security bits primary.val scalar.val output.val.val:ℝ)-MarkedPairSeed.secondCentered security scalar primary output| ≤
      RationalBackgroundDensities.bodyErrorConstant security*(1/(2:ℝ)^bits) := by
  simp only [secondCentered, Rat.cast_sub, Rat.cast_one, MarkedPairSeed.secondCentered]
  convert rawDensity_error security bits scalar primary output hprecision hbudget using 1
  congr 1
  ring

theorem secondMean_cast (security bits : ℕ) (scalar : MarkedPairSeed.Scalar security) (output : SafePalette security) :
    (secondMean security bits scalar.val output.val.val:ℝ) =
      (RationalProposalProgram.approximatePrimaryLaw security bits).expectation
        (fun primary => (secondCentered security bits primary.val scalar.val output.val.val:ℝ)) := by
  unfold secondMean
  rw [Rat.cast_sum]
  have hq : colors security = Parameters.modulus security := PublicParameterProgram.modulus_value security
  rw [hq]
  simp only [FiniteDist.expectation, RationalProposalProgram.approximatePrimaryLaw, Rat.cast_mul]

end
end CurrentAFT.RationalMarkedSeedProgram
