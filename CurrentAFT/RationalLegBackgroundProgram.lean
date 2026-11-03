import CurrentAFT.RationalPairQuadraticProgram
import CurrentAFT.RationalConditionalPairProgram
import CurrentAFT.RationalScalarFamilyAverage
import CurrentAFT.LegBackgroundFamilies

/-! # The original complete leg atom with the shared scalar averaged last -/
namespace CurrentAFT.RationalLegBackgroundProgram
open AFT GradedControlAlgebra ActualControls BackgroundFamilies DiffuseProfiles
open RationalActualFamilyApproximation
open scoped BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw bodyReference
  RationalPairQuadraticProgram.current RationalConditionalPairProgram.current
  RationalBackgroundProgram.translation RationalFamilyProductProgram.product

def conditionalQuadratic (security bits order : ℕ) (scalar : ℤ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  fun arity colors centers => RationalPairQuadraticProgram.current security bits order scalar arity colors centers+
    RationalFamilyProductProgram.product order (RationalConditionalPairProgram.current security bits order scalar)
      (RationalBackgroundProgram.translation security bits order scalar) arity colors centers

def conditionalCubic (security bits order : ℕ) (scalar : ℤ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  RationalFamilyProductProgram.product order (RationalPairQuadraticProgram.current security bits order scalar)
    (RationalBackgroundProgram.translation security bits order scalar)

def quadratic (security bits order : ℕ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  RationalScalarFamilyAverage.current security bits order (conditionalQuadratic security bits order)

def cubic (security bits order : ℕ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  RationalScalarFamilyAverage.current security bits order (conditionalCubic security bits order)

def current (security bits order : ℕ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  fun arity colors centers => RationalBackgroundLinearProgram.legLinear security bits order arity colors centers+
    quadratic security bits order arity colors centers+cubic security bits order arity colors centers

noncomputable section
open scoped Classical
local instance legBackgroundFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def conditionalLinearBound (security order : ℕ) : ℝ := coordinateFactor security order*32768
def pairBound (security order : ℕ) : ℝ := coordinateFactor security order*406880
def quadraticBound (security order : ℕ) : ℝ := coordinateFactor security order*2241888
def cubicBound (security order : ℕ) : ℝ := coordinateFactor security order*22785280
def conditionalQuadraticError (security order : ℕ) : ℝ :=
  RationalPairQuadraticProgram.errorConstant security order+
    productError order (conditionalLinearBound security order) (RationalBackgroundLinearProgram.translationBound security order)
      (RationalConditionalPairProgram.errorConstant security) (RationalBackgroundProgram.translationErrorConstant security)
def conditionalCubicError (security order : ℕ) : ℝ :=
  productError order (pairBound security order) (RationalBackgroundLinearProgram.translationBound security order)
    (RationalPairQuadraticProgram.errorConstant security order) (RationalBackgroundProgram.translationErrorConstant security)
def errorConstant (security order : ℕ) : ℝ := RationalBackgroundLinearProgram.linearErrorConstant security order+
  (conditionalQuadraticError security order+quadraticBound security order)+
  (conditionalCubicError security order+cubicBound security order)

private theorem base_one (security : ℕ) : (1:ℝ) ≤ Parameters.base security := by
  exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)

theorem conditionalLinear_bound (security order : ℕ) (horder : 1 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    ∀ arity colors centers, |data security order (ConditionalPairLinear.certificate security order horder scalar) arity colors centers| ≤ conditionalLinearBound security order :=
  point_bound security order _ 32768 ((ConditionalPairLinear.certificate_norm security order horder scalar).trans
    (div_le_self (by norm_num) (one_le_pow₀ (base_one security))))

theorem pair_bound (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    ∀ arity colors centers, |data security order (PairQuadraticFamilies.pairQuadraticCertificate security order horder scalar) arity colors centers| ≤ pairBound security order :=
  point_bound security order _ 406880 ((PairQuadraticFamilies.pairQuadraticCertificate_norm security order horder scalar).trans
    (div_le_self (by norm_num) (one_le_pow₀ (base_one security))))

theorem quadratic_bound (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    ∀ arity colors centers, |data security order (LegBackgroundFamilies.conditionalQuadratic security order horder scalar) arity colors centers| ≤ quadraticBound security order :=
  point_bound security order _ 2241888 ((LegBackgroundFamilies.conditionalQuadratic_norm security order horder scalar).trans
    (div_le_self (by norm_num) (one_le_pow₀ (base_one security))))

theorem cubic_bound (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    ∀ arity colors centers, |data security order (LegBackgroundFamilies.conditionalCubic security order horder scalar) arity colors centers| ≤ cubicBound security order :=
  point_bound security order _ 22785280 ((LegBackgroundFamilies.conditionalCubic_norm security order horder scalar).trans
    (div_le_self (by norm_num) (one_le_pow₀ (base_one security))))

theorem translationError_nonneg (security : ℕ) : 0 ≤ RationalBackgroundProgram.translationErrorConstant security := by
  rcases RationalBackgroundProgram.density_constants_nonneg security with ⟨hp, hr, hb⟩
  unfold RationalBackgroundProgram.translationErrorConstant
  positivity

theorem errorConstant_nonneg (security order : ℕ) : 0 ≤ errorConstant security order := by
  have hp := RationalConditionalPairProgram.errorConstant_nonneg security
  have hpair := RationalPairQuadraticProgram.errorConstant_nonneg security order
  have ht := translationError_nonneg security
  rcases RationalBackgroundProgram.density_constants_nonneg security with ⟨hprimary, _, hbody⟩
  have hf : 0 ≤ RationalBackgroundProgram.freeErrorConstant security := by
    unfold RationalBackgroundProgram.freeErrorConstant
    positivity
  have hm : 0 ≤ RationalBackgroundLinearProgram.meanErrorConstant security order := by
    unfold RationalBackgroundLinearProgram.meanErrorConstant RationalBackgroundLinearProgram.translationBound
    positivity
  have hl : 0 ≤ RationalBackgroundLinearProgram.linearErrorConstant security order := by
    unfold RationalBackgroundLinearProgram.linearErrorConstant
    exact div_nonneg (add_nonneg (mul_nonneg (ProposalPrimary.freeMass_nonneg security) hf)
      (mul_nonneg (Nat.cast_nonneg _) hm)) (Nat.cast_nonneg _)
  have hprod1 := productError_nonneg order (conditionalLinearBound security order)
    (RationalBackgroundLinearProgram.translationBound security order) _ _
    (by unfold conditionalLinearBound coordinateFactor; positivity)
    (by unfold RationalBackgroundLinearProgram.translationBound; positivity) hp ht
  have hprod2 := productError_nonneg order (pairBound security order)
    (RationalBackgroundLinearProgram.translationBound security order) _ _
    (by unfold pairBound coordinateFactor; positivity)
    (by unfold RationalBackgroundLinearProgram.translationBound; positivity) hpair ht
  unfold errorConstant conditionalQuadraticError conditionalCubicError quadraticBound cubicBound coordinateFactor
  positivity

theorem conditionalQuadratic_error (security bits order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (conditionalQuadratic security bits order scalar.val) arity colors centers-
      data security order (LegBackgroundFamilies.conditionalQuadratic security order horder scalar) arity colors centers| ≤
      conditionalQuadraticError security order*(1/(2:ℝ)^bits) := by
  have hprod := product_error security bits order
    (ConditionalPairLinear.certificate security order (by omega) scalar) (translationCertificate security order (by omega) scalar.val)
    (RationalConditionalPairProgram.current security bits order scalar.val) (RationalBackgroundProgram.translation security bits order scalar.val)
    (conditionalLinearBound security order) (RationalBackgroundLinearProgram.translationBound security order)
    (RationalConditionalPairProgram.errorConstant security) (RationalBackgroundProgram.translationErrorConstant security)
    (by unfold conditionalLinearBound coordinateFactor; positivity) (by unfold RationalBackgroundLinearProgram.translationBound; positivity)
    (RationalConditionalPairProgram.errorConstant_nonneg security) (translationError_nonneg security)
    (conditionalLinear_bound security order (by omega) scalar) (RationalBackgroundLinearProgram.translation_bound security order (by omega) scalar.val)
    (RationalConditionalPairProgram.current_error security bits order (by omega) scalar hfirst hprecision hbudget)
    (RationalBackgroundProgram.translation_error security bits order (by omega) scalar.val hfirst hprecision hbudget) arity colors centers
  have hpair := RationalPairQuadraticProgram.current_error security bits order horder scalar hfirst hprecision hbudget arity colors centers
  have hinterpret : interpret security order (conditionalQuadratic security bits order scalar.val) =
      interpret security order (RationalPairQuadraticProgram.current security bits order scalar.val)+
      interpret security order (RationalFamilyProductProgram.product order (RationalConditionalPairProgram.current security bits order scalar.val)
        (RationalBackgroundProgram.translation security bits order scalar.val)) := by
    funext arity colors centers
    exact Rat.cast_add _ _
  rw [hinterpret]
  change |((_:ℝ)+(_:ℝ))-((_:ℝ)+(_:ℝ))| ≤ (_:ℝ)
  rw [show ∀ a b c d : ℝ, a+b-(c+d)=(a-c)+(b-d) by intros; ring]
  exact (abs_add_le _ _).trans ((add_le_add hpair hprod).trans_eq (by unfold conditionalQuadraticError; ring))

theorem conditionalCubic_error (security bits order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (conditionalCubic security bits order scalar.val) arity colors centers-
      data security order (LegBackgroundFamilies.conditionalCubic security order horder scalar) arity colors centers| ≤
      conditionalCubicError security order*(1/(2:ℝ)^bits) :=
  product_error security bits order
    (PairQuadraticFamilies.pairQuadraticCertificate security order horder scalar) (translationCertificate security order (by omega) scalar.val)
    (RationalPairQuadraticProgram.current security bits order scalar.val) (RationalBackgroundProgram.translation security bits order scalar.val)
    (pairBound security order) (RationalBackgroundLinearProgram.translationBound security order)
    (RationalPairQuadraticProgram.errorConstant security order) (RationalBackgroundProgram.translationErrorConstant security)
    (by unfold pairBound coordinateFactor; positivity) (by unfold RationalBackgroundLinearProgram.translationBound; positivity)
    (RationalPairQuadraticProgram.errorConstant_nonneg security order) (translationError_nonneg security)
    (pair_bound security order horder scalar) (RationalBackgroundLinearProgram.translation_bound security order (by omega) scalar.val)
    (RationalPairQuadraticProgram.current_error security bits order horder scalar hfirst hprecision hbudget)
    (RationalBackgroundProgram.translation_error security bits order (by omega) scalar.val hfirst hprecision hbudget) arity colors centers

theorem quadratic_error (security bits order : ℕ) (horder : 2 ≤ order)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (quadratic security bits order) arity colors centers-
      data security order (LegBackgroundFamilies.legQuadratic security order horder) arity colors centers| ≤
      (conditionalQuadraticError security order+quadraticBound security order)*(1/(2:ℝ)^bits) :=
  RationalScalarFamilyAverage.current_error security bits order
    (LegBackgroundFamilies.conditionalQuadratic security order horder) (conditionalQuadratic security bits order)
    (quadraticBound security order) (conditionalQuadraticError security order) (by unfold quadraticBound coordinateFactor; positivity)
    (quadratic_bound security order horder) (fun scalar => conditionalQuadratic_error security bits order horder scalar hfirst hprecision hbudget)
    arity colors centers

theorem cubic_error (security bits order : ℕ) (horder : 2 ≤ order)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (cubic security bits order) arity colors centers-
      data security order (LegBackgroundFamilies.legCubic security order horder) arity colors centers| ≤
      (conditionalCubicError security order+cubicBound security order)*(1/(2:ℝ)^bits) :=
  RationalScalarFamilyAverage.current_error security bits order
    (LegBackgroundFamilies.conditionalCubic security order horder) (conditionalCubic security bits order)
    (cubicBound security order) (conditionalCubicError security order) (by unfold cubicBound coordinateFactor; positivity)
    (cubic_bound security order horder) (fun scalar => conditionalCubic_error security bits order horder scalar hfirst hprecision hbudget)
    arity colors centers

theorem current_error (security bits order : ℕ) (horder : 2 ≤ order)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(current security bits order arity (fun index => (colors index).val) (fun index => (centers index).val.val):ℝ)-
      (LegBackgroundFamilies.completeLegAtom security order horder arity).val colors centers| ≤
      errorConstant security order*(1/(2:ℝ)^bits) := by
  have hl := RationalBackgroundLinearProgram.legLinear_error security bits order (by omega) hfirst hprecision hbudget arity colors centers
  have hq := quadratic_error security bits order horder hfirst hprecision hbudget arity colors centers
  have hc := cubic_error security bits order horder hfirst hprecision hbudget arity colors centers
  simp only [current, Rat.cast_add, LegBackgroundFamilies.completeLegAtom, Pi.add_apply, Submodule.coe_add]
  rw [show ∀ a b c A B C : ℝ, a+b+c-(A+B+C)=(a-A)+(b-B)+(c-C) by intros; ring]
  exact (abs_add_le _ _).trans ((add_le_add ((abs_add_le _ _).trans (add_le_add hl hq)) hc).trans_eq
    (by unfold errorConstant; ring))

end
end CurrentAFT.RationalLegBackgroundProgram
