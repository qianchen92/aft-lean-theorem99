import CurrentAFT.RationalFamilyPullback
import CurrentAFT.ActualCoordinateBounds

/-! # Arithmetic errors in the literal current mixed coefficient data -/
namespace CurrentAFT.RationalActualFamilyApproximation
open AFT GradedControlAlgebra ActualControls BackgroundFamilies
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance approximationFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def interpret (security order : ℕ) (table : RationalFamilyProductProgram.Table ℚ ℕ ℕ order) :
    RationalFamilyProductProgram.Table ℝ (FirstHistogram.Palette security) (SafePalette security) order :=
  RationalFamilyProductProgram.pullback order Fin.val (fun color : SafePalette security => color.val.val)
    (RationalFamilyProductProgram.realTable order table)

def data (security order : ℕ) (family : ActualFamily security order) :
    RationalFamilyProductProgram.Table ℝ (FirstHistogram.Palette security) (SafePalette security) order :=
  fun arity => (family arity).val

theorem interpret_product (security order : ℕ)
    (first second : RationalFamilyProductProgram.Table ℚ ℕ ℕ order) :
    interpret security order (RationalFamilyProductProgram.product order first second) =
      RationalFamilyProductProgram.product order (interpret security order first) (interpret security order second) := by
  unfold interpret
  rw [RationalFamilyProductProgram.product_cast, RationalFamilyProductProgram.pullback_product]

theorem data_product (security order : ℕ) (first second : ActualFamily security order) :
    RationalFamilyProductProgram.product order (data security order first) (data security order second) =
      data security order (GradedControlAlgebra.familyProduct (ProposalPrimary.primaryLaw security)
        (ActualControls.bodyReference security) order first second) :=
  RationalFamilyProductProgram.product_actual _ _ _ _ _

def coordinateFactor (security order : ℕ) : ℝ :=
  (2*(Parameters.modulus security:ℝ)*Parameters.dimension security)^order

theorem point_bound (security order : ℕ) (family : ActualFamily security order) (bound : ℝ)
    (hbound : LocalRaisingBounds.coefficientNorm security order family ≤ bound)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |data security order family arity colors centers| ≤ coordinateFactor security order*bound := by
  exact (ActualCoordinateBounds.family_point_bound security order family arity colors centers).trans
    (mul_le_mul_of_nonneg_left hbound (by positivity))

def productError (order : ℕ) (A B e f : ℝ) : ℝ :=
  (Fintype.card (TruncatedArity order):ℝ)^2*(e*B+(A+e)*f)

theorem productError_nonneg (order : ℕ) (A B e f : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (he : 0 ≤ e) (hf : 0 ≤ f) :
    0 ≤ productError order A B e f := by
  unfold productError
  positivity

theorem product_error (security bits order : ℕ)
    (first second : ActualFamily security order)
    (computedFirst computedSecond : RationalFamilyProductProgram.Table ℚ ℕ ℕ order)
    (A B e f : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (he : 0 ≤ e) (hf : 0 ≤ f)
    (ha : ∀ arity colors centers, |data security order first arity colors centers| ≤ A)
    (hb : ∀ arity colors centers, |data security order second arity colors centers| ≤ B)
    (hea : ∀ arity colors centers,
      |interpret security order computedFirst arity colors centers-data security order first arity colors centers| ≤ e*(1/(2:ℝ)^bits))
    (heb : ∀ arity colors centers,
      |interpret security order computedSecond arity colors centers-data security order second arity colors centers| ≤ f*(1/(2:ℝ)^bits))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (RationalFamilyProductProgram.product order computedFirst computedSecond) arity colors centers-
      data security order (GradedControlAlgebra.familyProduct (ProposalPrimary.primaryLaw security)
        (ActualControls.bodyReference security) order first second) arity colors centers| ≤
      productError order A B e f*(1/(2:ℝ)^bits) := by
  have hε : (0:ℝ) ≤ 1/2^bits := by positivity
  have hε1 : 1/(2:ℝ)^bits ≤ 1 :=
    (div_le_one (by positivity : (0:ℝ)<2^bits)).mpr (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
  rw [interpret_product, ← data_product]
  have h := RationalFamilyProductProgram.product_error order
    (data security order first) (interpret security order computedFirst)
    (data security order second) (interpret security order computedSecond)
    A B (e*(1/(2:ℝ)^bits)) (f*(1/(2:ℝ)^bits)) hA hB
    (mul_nonneg he hε) (mul_nonneg hf hε) ha hb hea heb arity colors centers
  apply h.trans
  calc
    _ ≤ (Fintype.card (TruncatedArity order):ℝ)^2*
        ((e*(1/(2:ℝ)^bits))*B+(A+e)*(f*(1/(2:ℝ)^bits))) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      have hAe : A+e*(1/(2:ℝ)^bits) ≤ A+e := by
        nlinarith [mul_le_mul_of_nonneg_left hε1 he]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hAe (mul_nonneg hf hε))
    _ = _ := by unfold productError; ring

end
end CurrentAFT.RationalActualFamilyApproximation
