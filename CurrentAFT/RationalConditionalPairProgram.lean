import CurrentAFT.LocalPairProgram
import CurrentAFT.ConditionalPairLinear
import CurrentAFT.RationalFiniteMean
import CurrentAFT.RationalMassCertificateTable

/-! # Fixed-scalar pair means and their original one-primary certificate -/
namespace CurrentAFT.RationalConditionalPairProgram
open AFT RationalNumerics DiffuseProfiles ProposalPrimary ActualControls GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base PublicParameterProgram.modulus primaryLaw

abbrev colors (security : ℕ) := (PublicParameterProgram.modulus security).count

def pairProfile (security bits primary : ℕ) (scalar : ℤ) (output : ℕ) : ℚ :=
  (∑ other : Fin (colors security), LocalPairProgram.current security bits primary scalar output other.val)+
    ∑ other : Fin (colors security), LocalPairProgram.current security bits primary scalar other.val output

def pairMean (security bits : ℕ) (scalar : ℤ) (output : ℕ) : ℚ :=
  ∑ primary : Fin (colors security), RationalProposalProgram.primary security bits primary.val*pairProfile security bits primary.val scalar output

def centeredMean (security bits : ℕ) (scalar : ℤ) (output : ℕ) : ℚ :=
  pairMean security bits scalar output-2/(colors security:ℚ)

def current (security bits order : ℕ) (scalar : ℤ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  RationalBackgroundTable.firstTable order
    (RationalMassLiftProgram.current security bits (centeredMean security bits scalar)) (fun _ => 0)

noncomputable section
open scoped Classical
local instance conditionalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def actualPairProfile (security : ℕ) (scalar : FirstHistogram.Scalar security) (primary output : FirstHistogram.Palette security) : ℝ :=
  (∑ other, (LocalReferenceEnergy.pairAt security primary scalar).weight (output, other))+
    ∑ other, (LocalReferenceEnergy.pairAt security primary scalar).weight (other, output)

def profileErrorConstant (security : ℕ) : ℝ := 6*(Parameters.modulus security:ℝ)+
  2*(Parameters.modulus security:ℝ)*(64*(Parameters.base security:ℝ)*Parameters.dimension security)

def computedBound (security : ℕ) : ℝ := 4+6*(Parameters.modulus security:ℝ)

def errorConstant (security : ℕ) : ℝ := RationalMassLiftProgram.errorConstant security*computedBound security+
  RationalTensorInverseProgram.actualBound security*profileErrorConstant security

theorem actualPairProfile_bound (security : ℕ) (scalar : FirstHistogram.Scalar security) (primary output : FirstHistogram.Palette security) :
    |actualPairProfile security scalar primary output| ≤ 2 := by
  have hfirst := (ConditionalPairMean.firstMarginal (LocalReferenceEnergy.pairAt security primary scalar)).atom_le_one output
  have hsecond := (ConditionalPairMean.secondMarginal (LocalReferenceEnergy.pairAt security primary scalar)).atom_le_one output
  have hf0 := (ConditionalPairMean.firstMarginal (LocalReferenceEnergy.pairAt security primary scalar)).nonneg output
  have hs0 := (ConditionalPairMean.secondMarginal (LocalReferenceEnergy.pairAt security primary scalar)).nonneg output
  change |(ConditionalPairMean.firstMarginal (LocalReferenceEnergy.pairAt security primary scalar)).weight output+
    (ConditionalPairMean.secondMarginal (LocalReferenceEnergy.pairAt security primary scalar)).weight output| ≤ 2
  rw [abs_of_nonneg (add_nonneg hf0 hs0)]
  linarith

theorem pairProfile_error (security bits : ℕ) (scalar : FirstHistogram.Scalar security) (primary output : FirstHistogram.Palette security) :
    |(pairProfile security bits primary.val scalar.val output.val:ℝ)-actualPairProfile security scalar primary output| ≤
      6*(Parameters.modulus security:ℝ)*(1/(2:ℝ)^bits) := by
  unfold pairProfile
  rw [Rat.cast_add, Rat.cast_sum, Rat.cast_sum, colors, PublicParameterProgram.modulus_value]
  unfold actualPairProfile
  have hf : |(∑ other : FirstHistogram.Palette security, (LocalPairProgram.current security bits primary.val scalar.val output.val other.val:ℝ))-
      ∑ other : FirstHistogram.Palette security, (LocalReferenceEnergy.pairAt security primary scalar).weight (output, other)| ≤
      (Parameters.modulus security:ℝ)*(3/(2:ℝ)^bits) := by
    rw [← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun other _ => LocalPairProgram.current_error security bits primary output other scalar)).trans_eq (by simp))
  have hs : |(∑ other : FirstHistogram.Palette security, (LocalPairProgram.current security bits primary.val scalar.val other.val output.val:ℝ))-
      ∑ other : FirstHistogram.Palette security, (LocalReferenceEnergy.pairAt security primary scalar).weight (other, output)| ≤
      (Parameters.modulus security:ℝ)*(3/(2:ℝ)^bits) := by
    rw [← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun other _ => LocalPairProgram.current_error security bits primary other output scalar)).trans_eq (by simp))
  have hid (a b c d : ℝ) : a+b-(c+d)=(a-c)+(b-d) := by ring
  rw [hid]
  exact (abs_add_le _ _).trans ((add_le_add hf hs).trans_eq (by ring))

theorem pairMean_cast (security bits : ℕ) (scalar : FirstHistogram.Scalar security) (output : FirstHistogram.Palette security) :
    (pairMean security bits scalar.val output.val:ℝ) =
      (RationalProposalProgram.approximatePrimaryLaw security bits).expectation
        (fun primary => (pairProfile security bits primary.val scalar.val output.val:ℝ)) := by
  unfold pairMean
  rw [Rat.cast_sum, colors, PublicParameterProgram.modulus_value]
  simp only [FiniteDist.expectation, RationalProposalProgram.approximatePrimaryLaw, Rat.cast_mul]

theorem pairMean_error (security bits : ℕ) (scalar : FirstHistogram.Scalar security) (output : FirstHistogram.Palette security)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ))) :
    |(pairMean security bits scalar.val output.val:ℝ)-ConditionalPairMean.pairMean security scalar output| ≤
      profileErrorConstant security*(1/(2:ℝ)^bits) := by
  rw [pairMean_cast, ConditionalPairMean.pairMean_actual]
  have hx := RationalFiniteMean.expectation_error (primaryLaw security) (RationalProposalProgram.approximatePrimaryLaw security bits)
    (fun primary => actualPairProfile security scalar primary output)
    (fun primary => (pairProfile security bits primary.val scalar.val output.val:ℝ))
    (6*(Parameters.modulus security:ℝ)*(1/(2:ℝ)^bits))
    (64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits)) 2
    (by positivity) (by norm_num) (fun primary => pairProfile_error security bits scalar primary output)
    (fun primary => by simpa only [RationalProposalProgram.approximatePrimaryLaw, primaryLaw] using RationalProposalProgram.primary_error security bits primary hprecision hbudget)
    (fun primary => actualPairProfile_bound security scalar primary output)
  exact hx.trans_eq (by unfold profileErrorConstant; simp only [Fintype.card_fin]; ring)

theorem centeredMean_error (security bits : ℕ) (scalar : FirstHistogram.Scalar security) (output : FirstHistogram.Palette security)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ))) :
    |(centeredMean security bits scalar.val output.val:ℝ)-ConditionalPairMean.centeredMean security scalar output| ≤
      profileErrorConstant security*(1/(2:ℝ)^bits) := by
  simp only [centeredMean, Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast, colors, PublicParameterProgram.modulus_value,
    ConditionalPairMean.centeredMean, FringeCertificate.uniformProfile]
  convert pairMean_error security bits scalar output hprecision hbudget using 1
  congr 1
  ring

theorem centeredMean_bound (security bits : ℕ) (scalar : FirstHistogram.Scalar security) (output : FirstHistogram.Palette security) :
    |(centeredMean security bits scalar.val output.val:ℝ)| ≤ computedBound security := by
  have heps : 1/(2:ℝ)^bits ≤ 1 := by
    exact (div_le_one (by positivity : (0:ℝ)<2^bits)).mpr (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
  have hp (primary : FirstHistogram.Palette security) : |(pairProfile security bits primary.val scalar.val output.val:ℝ)| ≤ 2+6*(Parameters.modulus security:ℝ) := by
    have hx := pairProfile_error security bits scalar primary output
    have hy := actualPairProfile_bound security scalar primary output
    have hz := abs_sub_le (pairProfile security bits primary.val scalar.val output.val:ℝ)
      (actualPairProfile security scalar primary output) 0
    simp only [sub_zero] at hz
    exact hz.trans ((add_le_add hx hy).trans (by nlinarith [mul_le_mul_of_nonneg_left heps (by positivity : (0:ℝ)≤6*Parameters.modulus security)]))
  have hm : |(pairMean security bits scalar.val output.val:ℝ)| ≤ 2+6*(Parameters.modulus security:ℝ) := by
    rw [pairMean_cast]
    exact CalibrationCoordinateError.expectation_abs_bound _ _ _ hp
  have hq : (1:ℝ) ≤ Parameters.modulus security := by exact_mod_cast (Nat.succ_le_of_lt (Parameters.modulus_spec security).2.pos)
  have hu : |2/(Parameters.modulus security:ℝ)| ≤ 2 := by
    rw [abs_of_nonneg (by positivity : (0:ℝ)≤2/(Parameters.modulus security:ℝ))]
    exact (div_le_iff₀ (by positivity)).mpr (by linarith)
  simp only [centeredMean, Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast, colors, PublicParameterProgram.modulus_value]
  exact (abs_sub _ _).trans ((add_le_add hm hu).trans_eq (by unfold computedBound; ring))

theorem data (security order : ℕ) (horder : 1 ≤ order) (scalar : FirstHistogram.Scalar security) :
    RationalBackgroundTable.firstTable order (RationalMassLiftProgram.actual security (ConditionalPairMean.centeredMean security scalar))
      (fun _ : SafePalette security => (0:ℝ)) =
    fun arity => (ConditionalPairLinear.certificate security order horder scalar arity).val := by
  exact RationalMassCertificateTable.data security order horder (ConditionalPairMean.centeredMean security scalar)
    (ConditionalPairLinear.wordMean_centered security scalar) (ConditionalPairLinear.wordMean_symmetric security scalar)

theorem errorConstant_nonneg (security : ℕ) : 0 ≤ errorConstant security := by
  simp only [errorConstant, computedBound, profileErrorConstant, RationalMassLiftProgram.errorConstant,
    RationalTensorInverseProgram.actualBound, RationalDensityInverseProgram.inverseBound, RationalFirstResponseProgram.inverseErrorConstant]
  positivity

theorem current_error (security bits order : ℕ) (horder : 1 ≤ order) (scalar : FirstHistogram.Scalar security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(current security bits order scalar.val arity (fun index => (colors index).val) (fun index => (centers index).val.val):ℝ)-
      (ConditionalPairLinear.certificate security order horder scalar arity).val colors centers| ≤ errorConstant security*(1/(2:ℝ)^bits) := by
  have hl (primary : FirstHistogram.Palette security) :
      |(RationalMassLiftProgram.current security bits (centeredMean security bits scalar.val) primary.val:ℝ)-
        RationalMassLiftProgram.actual security (ConditionalPairMean.centeredMean security scalar) primary| ≤ errorConstant security*(1/(2:ℝ)^bits) := by
    exact (RationalMassLiftProgram.current_profile_error security bits (centeredMean security bits scalar.val)
      (ConditionalPairMean.centeredMean security scalar) (computedBound security) (profileErrorConstant security*(1/(2:ℝ)^bits))
      (by unfold computedBound; positivity) (by unfold profileErrorConstant; positivity)
      (centeredMean_bound security bits scalar) (fun output => centeredMean_error security bits scalar output hprecision hbudget)
      hfirst hprecision hbudget primary).trans_eq (by unfold errorConstant; ring)
  have hx := RationalBackgroundTable.firstTable_error order (RationalMassLiftProgram.current security bits (centeredMean security bits scalar.val)) (fun _ => 0)
    (RationalMassLiftProgram.actual security (ConditionalPairMean.centeredMean security scalar)) (fun _ : SafePalette security => 0)
    Fin.val (fun color => color.val.val) (errorConstant security*(1/(2:ℝ)^bits)) 0
    (mul_nonneg (errorConstant_nonneg security) (by positivity)) (by norm_num) hl (fun _ => by norm_num) arity colors centers
  rw [data security order horder scalar] at hx
  simpa only [add_zero] using hx

end
end CurrentAFT.RationalConditionalPairProgram
