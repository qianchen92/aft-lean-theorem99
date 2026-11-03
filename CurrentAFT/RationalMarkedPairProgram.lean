import CurrentAFT.RationalPrimaryDeviationProgram
import CurrentAFT.RationalMarkedCertificateProgram
import CurrentAFT.RationalBackgroundProgram
import CurrentAFT.RationalActualFamilyApproximation
import CurrentAFT.PairQuadraticFamilies

/-! # The complete original marked quadratic certificate data -/
namespace CurrentAFT.RationalMarkedPairProgram
open AFT GradedControlAlgebra ActualControls BackgroundFamilies
open RationalActualFamilyApproximation
open scoped BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base PublicParameterProgram.modulus
  ProposalPrimary.primaryLaw ActualControls.bodyReference
  RationalPrimaryDeviationProgram.current RationalBackgroundProgram.free
  RationalMarkedCertificateProgram.current RationalFamilyProductProgram.product

def current (security bits order : ℕ) (scalar : ℤ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  fun arity colors centers => RationalMarkedCertificateProgram.current security bits order scalar arity colors centers+
    RationalFamilyProductProgram.product order (RationalPrimaryDeviationProgram.current security bits order)
      (RationalBackgroundProgram.free security bits order) arity colors centers

noncomputable section
open scoped Classical
local instance markedPairFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def primaryBound (security order : ℕ) : ℝ := coordinateFactor security order*24
def freeBound (security order : ℕ) : ℝ := coordinateFactor security order*84
def errorConstant (security order : ℕ) : ℝ :=
  RationalMarkedSeedProgram.inverseErrorConstant security+
    productError order (primaryBound security order) (freeBound security order)
      (RationalPrimaryDeviationProgram.errorConstant security) (RationalBackgroundProgram.freeErrorConstant security)

theorem primary_bound (security order : ℕ) (horder : 1 ≤ order) :
    ∀ arity colors centers,
      |data security order (PrimaryDeviationCertificate.certificate security order horder) arity colors centers| ≤ primaryBound security order := by
  have hb : (1:ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  exact point_bound security order _ 24 ((PrimaryDeviationCertificate.certificate_norm security order horder).trans
    (div_le_self (by norm_num) (one_le_pow₀ hb)))

theorem free_bound (security order : ℕ) (horder : 1 ≤ order) :
    ∀ arity colors centers,
      |data security order (freeCertificate security order horder) arity colors centers| ≤ freeBound security order := by
  have hb : (1:ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  exact point_bound security order _ 84 ((freeCertificate_norm_decay security order horder).trans
    (div_le_self (by norm_num) (one_le_pow₀ hb)))

theorem data_identity (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    data security order (PairQuadraticFamilies.markedPairCertificate security order horder scalar) =
      data security order (MarkedPairCertificates.markedMixedCertificate security order horder scalar)+
      data security order (familyProduct (ProposalPrimary.primaryLaw security) (bodyReference security) order
        (PrimaryDeviationCertificate.certificate security order (by omega)) (freeCertificate security order (by omega))) := rfl

theorem interpret_current (security bits order : ℕ) (scalar : ℤ) :
    interpret security order (current security bits order scalar) =
      interpret security order (RationalMarkedCertificateProgram.current security bits order scalar)+
      interpret security order (RationalFamilyProductProgram.product order
        (RationalPrimaryDeviationProgram.current security bits order) (RationalBackgroundProgram.free security bits order)) := by
  funext arity colors centers
  exact Rat.cast_add _ _

theorem errorConstant_nonneg (security order : ℕ) : 0 ≤ errorConstant security order := by
  have hm := RationalMarkedCertificateProgram.errorConstant_nonneg security
  have hp := RationalPrimaryDeviationProgram.errorConstant_nonneg security
  rcases RationalBackgroundProgram.density_constants_nonneg security with ⟨hfree, _, hbody⟩
  have hf : 0 ≤ RationalBackgroundProgram.freeErrorConstant security := by
    unfold RationalBackgroundProgram.freeErrorConstant
    positivity
  have hprod := productError_nonneg order (primaryBound security order) (freeBound security order)
    _ _ (by unfold primaryBound coordinateFactor; positivity) (by unfold freeBound coordinateFactor; positivity) hp hf
  exact add_nonneg hm hprod

theorem current_error (security bits order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(current security bits order scalar.val arity (fun index => (colors index).val) (fun index => (centers index).val.val):ℝ)-
      (PairQuadraticFamilies.markedPairCertificate security order horder scalar arity).val colors centers| ≤
      errorConstant security order*(1/(2:ℝ)^bits) := by
  have hp := RationalPrimaryDeviationProgram.errorConstant_nonneg security
  rcases RationalBackgroundProgram.density_constants_nonneg security with ⟨hfree, _, hbody⟩
  have hf : 0 ≤ RationalBackgroundProgram.freeErrorConstant security := by
    unfold RationalBackgroundProgram.freeErrorConstant
    positivity
  have hprod := product_error security bits order
    (PrimaryDeviationCertificate.certificate security order (by omega)) (freeCertificate security order (by omega))
    (RationalPrimaryDeviationProgram.current security bits order) (RationalBackgroundProgram.free security bits order)
    (primaryBound security order) (freeBound security order)
    (RationalPrimaryDeviationProgram.errorConstant security) (RationalBackgroundProgram.freeErrorConstant security)
    (by unfold primaryBound coordinateFactor; positivity) (by unfold freeBound coordinateFactor; positivity) hp hf
    (primary_bound security order (by omega)) (free_bound security order (by omega))
    (RationalPrimaryDeviationProgram.current_error security bits order (by omega) hfirst hprecision hbudget)
    (RationalBackgroundProgram.free_error security bits order (by omega) hfirst hprecision hbudget) arity colors centers
  have hm := RationalMarkedCertificateProgram.current_error security bits order horder scalar hfirst hprecision hbudget arity colors centers
  change |interpret security order (current security bits order scalar.val) arity colors centers-
    data security order (PairQuadraticFamilies.markedPairCertificate security order horder scalar) arity colors centers| ≤ _
  rw [interpret_current, data_identity]
  simp only [Pi.add_apply]
  have hid (a b c d : ℝ) : a+b-(c+d)=(a-c)+(b-d) := by ring
  rw [hid]
  exact (abs_add_le _ _).trans ((add_le_add hm hprod).trans_eq (by unfold errorConstant; ring))

end
end CurrentAFT.RationalMarkedPairProgram
