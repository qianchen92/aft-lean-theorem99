import CurrentAFT.RationalMarkedSeedBounds
import CurrentAFT.RationalFamilyProductProgram

/-! # The actual marked `(1,1)` canonical coefficient data -/
namespace CurrentAFT.RationalMarkedCertificateProgram
open AFT ControlCoordinates GradedControlAlgebra ActualControls MarkedPairCertificates
open scoped BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def current (security bits order : ℕ) (scalar : ℤ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  fun arity colors centers => if h : arity.val.1.val=1 ∧ arity.val.2.val=1 then
    RationalMarkedSeedProgram.inverseDensity security bits scalar (colors ⟨0, by omega⟩) (centers ⟨0, by omega⟩) else 0

noncomputable section
open scoped Classical
local instance certificateFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def ideal (security order : ℕ) (scalar : MarkedPairSeed.Scalar security) :
    RationalFamilyProductProgram.Table ℝ (FirstHistogram.Palette security) (SafePalette security) order :=
  fun arity colors centers => if h : arity.val.1.val=1 ∧ arity.val.2.val=1 then
    MarkedPairCertificates.inverseDensity security scalar (colors ⟨0, by omega⟩) (centers ⟨0, by omega⟩) else 0

theorem data (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    ideal security order scalar = fun arity => (markedMixedCertificate security order horder scalar arity).val := by
  funext arity colors centers
  by_cases h : arity = mixedArity order horder
  · subst arity
    simp [ideal, markedMixedCertificate, mixedArity, mixedKernel]
  · have hshape : ¬(arity.val.1.val=1 ∧ arity.val.2.val=1) := by
      intro hs
      apply h
      apply Subtype.ext
      exact Prod.ext (Fin.ext hs.1) (Fin.ext hs.2)
    simp only [ideal, dif_neg hshape, markedMixedCertificate, Pi.single_eq_of_ne h, Submodule.coe_zero, Pi.zero_apply]

theorem errorConstant_nonneg (security : ℕ) : 0 ≤ RationalMarkedSeedProgram.inverseErrorConstant security := by
  simp only [RationalMarkedSeedProgram.inverseErrorConstant, RationalMarkedSeedProgram.seedErrorConstant, RationalMarkedSeedProgram.meanErrorConstant, RationalMarkedSeedProgram.profileBound, RationalMarkedSeedProgram.uniformErrorConstant, RationalMarkedSeedProgram.primaryErrorConstant, RationalBackgroundDensities.bodyErrorConstant, RationalBackgroundDensities.centerErrorConstant, RationalDensityInverseProgram.errorConstant, RationalDensityInverseProgram.inverseBound, RationalTensorInverseProgram.actualBound, RationalFirstResponseProgram.inverseErrorConstant]
  positivity

theorem current_error (security bits order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(current security bits order scalar.val arity (fun index => (colors index).val) (fun index => (centers index).val.val):ℝ)-
      (markedMixedCertificate security order horder scalar arity).val colors centers| ≤
      RationalMarkedSeedProgram.inverseErrorConstant security*(1/(2:ℝ)^bits) := by
  have he := congrFun (congrFun (congrFun (data security order horder scalar) arity) colors) centers
  rw [← he]
  unfold current ideal
  split_ifs
  · exact RationalMarkedSeedProgram.inverseDensity_error security bits scalar _ _ hfirst hprecision hbudget
  · simpa only [Rat.cast_zero, sub_self, abs_zero] using mul_nonneg (errorConstant_nonneg security) (by positivity : (0:ℝ) ≤ 1/2^bits)

end
end CurrentAFT.RationalMarkedCertificateProgram
