import CurrentAFT.RationalMarkedPairProgram
import CurrentAFT.RationalDiffuseFamilyProgram

/-! # The actual activation mixture of the original two quadratic certificates -/
namespace CurrentAFT.RationalPairQuadraticProgram
open AFT GradedControlAlgebra ActualControls BackgroundFamilies DiffuseProfiles
open RationalActualFamilyApproximation
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw bodyReference
  RationalDiffuseFamilyProgram.current RationalMarkedPairProgram.current

def current (security bits order : ℕ) (scalar : ℤ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  fun arity colors centers =>
    (1-LocalPairProgram.activationApprox security bits)*
      RationalDiffuseFamilyProgram.current security bits order scalar arity colors centers+
    LocalPairProgram.activationApprox security bits*
      RationalMarkedPairProgram.current security bits order scalar arity colors centers

noncomputable section
open scoped Classical
local instance pairQuadraticFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def diffuseBound (security order : ℕ) : ℝ := coordinateFactor security order*388480
def markedBound (security order : ℕ) : ℝ := coordinateFactor security order*18400
def errorConstant (security order : ℕ) : ℝ :=
  RationalDiffuseFamilyProgram.errorConstant security+RationalMarkedPairProgram.errorConstant security order+
    (diffuseBound security order+markedBound security order)/2

theorem diffuse_bound (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    ∀ arity colors centers,
      |data security order (DiffusePairCertificates.diffuseCertificate security order horder scalar.val) arity colors centers| ≤ diffuseBound security order := by
  have hb : (1:ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  apply point_bound security order _ 388480
  exact (DiffusePairCertificates.diffuseCertificate_norm security order horder scalar.val
    ((InwardAnchor.scalar_bound security scalar).trans (by omega))).trans (div_le_self (by norm_num) (one_le_pow₀ hb))

theorem marked_bound (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    ∀ arity colors centers,
      |data security order (PairQuadraticFamilies.markedPairCertificate security order horder scalar) arity colors centers| ≤ markedBound security order := by
  have hb : (1:ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  exact point_bound security order _ 18400 ((PairQuadraticFamilies.markedPairCertificate_norm security order horder scalar).trans
    (div_le_self (by norm_num) (one_le_pow₀ hb)))

theorem errorConstant_nonneg (security order : ℕ) : 0 ≤ errorConstant security order := by
  have hm := RationalMarkedPairProgram.errorConstant_nonneg security order
  have hd := RationalDiffuseFamilyProgram.errorConstant_nonneg security
  unfold errorConstant diffuseBound markedBound coordinateFactor
  positivity

private theorem mixture_error (x y X Y a r ε e f A B : ℝ)
    (hε : 0 ≤ ε) (he : 0 ≤ e) (hf : 0 ≤ f) (_hA : 0 ≤ A) (_hB : 0 ≤ B)
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hx : |x-X| ≤ e*ε) (hy : |y-Y| ≤ f*ε)
    (hX : |X| ≤ A) (hY : |Y| ≤ B) (hr : |a-r| ≤ (1/2:ℝ)*ε) :
    |(1-a)*x+a*y-((1-r)*X+r*Y)| ≤ (e+f+(A+B)/2)*ε := by
  have hrem : 0 ≤ 1-a := by linarith
  have hrem1 : 1-a ≤ 1 := by linarith
  have hgap : |Y-X| ≤ A+B := (abs_sub _ _).trans ((add_le_add hY hX).trans_eq (by ring))
  rw [show (1-a)*x+a*y-((1-r)*X+r*Y)=(1-a)*(x-X)+a*(y-Y)+(a-r)*(Y-X) by ring]
  calc
    _ ≤ |(1-a)*(x-X)|+|a*(y-Y)|+|(a-r)*(Y-X)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = (1-a)*|x-X|+a*|y-Y|+|a-r| * |Y-X| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hrem, abs_of_nonneg ha]
    _ ≤ e*ε+f*ε+((1/2:ℝ)*ε)*(A+B) := by
      apply add_le_add
      · exact add_le_add
          ((mul_le_mul_of_nonneg_left hx hrem).trans ((mul_le_mul_of_nonneg_right hrem1 (mul_nonneg he hε)).trans_eq (one_mul _)))
          ((mul_le_mul_of_nonneg_left hy ha).trans ((mul_le_mul_of_nonneg_right ha1 (mul_nonneg hf hε)).trans_eq (one_mul _)))
      · exact mul_le_mul hr hgap (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem current_error (security bits order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(current security bits order scalar.val arity (fun index => (colors index).val) (fun index => (centers index).val.val):ℝ)-
      (PairQuadraticFamilies.pairQuadraticCertificate security order horder scalar arity).val colors centers| ≤
      errorConstant security order*(1/(2:ℝ)^bits) := by
  have hd := RationalDiffuseFamilyProgram.current_error security bits order horder scalar.val hfirst hprecision hbudget arity colors centers
  have hm := RationalMarkedPairProgram.current_error security bits order horder scalar hfirst hprecision hbudget arity colors centers
  have ha := LocalPairProgram.activationApprox_bounds security bits
  have hrate := LocalPairProgram.activationApprox_error security bits
  simp only [current, Rat.cast_add, Rat.cast_mul, Rat.cast_sub, Rat.cast_one,
    PairQuadraticFamilies.pairQuadraticCertificate, Pi.add_apply, Pi.smul_apply,
    Submodule.coe_add, Submodule.coe_smul, smul_eq_mul]
  exact mixture_error _ _ _ _ _ _ _ _ _ _ _ (by positivity) (RationalDiffuseFamilyProgram.errorConstant_nonneg security)
    (RationalMarkedPairProgram.errorConstant_nonneg security order)
    (by unfold diffuseBound coordinateFactor; positivity) (by unfold markedBound coordinateFactor; positivity)
    ha.1 (ha.2.trans (by norm_num)) hd hm (diffuse_bound security order horder scalar arity colors centers)
    (marked_bound security order horder scalar arity colors centers) hrate

end
end CurrentAFT.RationalPairQuadraticProgram
