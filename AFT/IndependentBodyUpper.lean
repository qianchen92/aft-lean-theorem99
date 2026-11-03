import AFT.IndependentBodyInverse
import AFT.LocalQuotientAlgebra

/-! # The ordinary-body quotient on arbitrary joint input seeds -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance independentBodyUpperFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- The root convolution is already the exact body leading channel.  Its
entire upper correction therefore consists of the positive-factor reciprocal. -/
def independentBodyUpper (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (seed : InputSeed (Fin (Parameters.modulus n))) (depth : ℕ) :
    Table (InputSeed (Fin (Parameters.modulus n))) :=
  MvPolynomial.X seed*(independentBodyReciprocal C n beta operator depth-1)

theorem independentBodyUpper_hasOrder (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (seed : InputSeed (Fin (Parameters.modulus n))) (depth : ℕ) :
    HasOrder (fun seed : InputSeed (Fin (Parameters.modulus n)) => seed.primaryOrder+seed.bodyOrder)
      (seed.primaryOrder+seed.bodyOrder+1) (independentBodyUpper C n beta operator seed depth) := by
  apply hasOrder_mul
  · simpa only [map_one,one_mul] using hasOrder_C_mul_X
      (fun seed : InputSeed (Fin (Parameters.modulus n)) => seed.primaryOrder+seed.bodyOrder)
      (seed.primaryOrder+seed.bodyOrder) seed 1 le_rfl
  · exact hasOrder_finiteCorrection_sub_one _ _ depth (referenceInverseTable_hasOrder _ _ _ _ _ _)

theorem independentBodyUpper_activity_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n ∧ Parameters.legs n ≤ 2*pool n) :
    ∀ᶠ n in atTop,
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n → ∀ bodyPool radius : ℝ,0 ≤ radius →
    ∀ (seed : InputSeed (Fin (Parameters.modulus n))) (depth : ℕ),
    activity (inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
      (pool n) bodyPool radius) (independentBodyUpper C n (beta n) operator seed depth) ≤
      (2*independentBodyInputConstant C)/(n : ℝ)^(43/4 : ℝ)*
        inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
          (pool n) bodyPool radius seed := by
  have ht : Tendsto (fun n : ℕ => independentBodyInputConstant C/(n : ℝ)^(43/4 : ℝ)) atTop (𝓝 0) :=
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<43/4)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)).const_div_atTop _
  have hs := Filter.Tendsto.eventually_le_const (by norm_num : (0:ℝ)<1/2) ht
  filter_upwards [independentBodyInputTable_activity_eventually C hC beta pool htypical,hs]
    with n he hs operator hop bodyPool radius hradius seed depth
  let weight := inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (pool n) bodyPool radius
  have hw (seed) : 0 ≤ weight seed := inputWeight_nonneg _ _ _ _ _ seed hradius
  have herr := he operator hop bodyPool radius hradius
  have hrec := activity_finiteCorrection_sub_one_le weight hw
    (independentBodyInputTable C n (beta n) operator) depth (herr.trans hs)
  have hh := (activity_mul_le weight hw (MvPolynomial.X seed)
    (independentBodyReciprocal C n (beta n) operator depth-1)).trans
    (mul_le_mul_of_nonneg_left hrec (activity_nonneg weight hw _))
  rw [activity_X] at hh
  apply hh.trans
  exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left herr (by norm_num : (0:ℝ)≤2))
    (hw seed)).trans_eq (by ring)

theorem independentBodyUpper_canonical_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n →
    ∀ seed : InputSeed (Fin (Parameters.modulus n)),
    Hoeffding.Canonical (inputReference (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) seed)
      Finset.univ seed.kernel → ∀ depth : ℕ,
    InputTableCanonical (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
      (independentBodyUpper C n (beta n) operator seed depth) := by
  filter_upwards [independentBodyInputTable_canonical_eventually C hC beta hbeta]
    with n he operator hop seed hseed depth
  exact (InputTableCanonical.X seed hseed).mul
    (((he operator hop).finiteCorrection depth).sub InputTableCanonical.one)

theorem independentBodyUpper_image (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (hop : operator.toLinearMap=actualResponse C n) (hrho : v7Activation C n ≠ 0)
    (hp : ∀ color,0 < (actualPrimaryLaw C n beta).weight color)
    (seed : InputSeed (Fin (Parameters.modulus n))) (depth : ℕ) :
    actualLeadingOutput C n beta (MvPolynomial.X seed+independentBodyUpper C n beta operator seed depth)=
      actualLeadingOutput C n beta (MvPolynomial.X seed)*
        finiteCorrection (centeredGeneratingLinear (actualReferenceLaw C n beta).weight
          (independentBodyPositiveMass C n beta)-1) depth := by
  have he : MvPolynomial.X seed+independentBodyUpper C n beta operator seed depth=
      MvPolynomial.X seed*independentBodyReciprocal C n beta operator depth := by
    unfold independentBodyUpper
    ring
  rw [he,map_mul,independentBodyReciprocal_image C n beta operator hop hrho hp]

end
end AFT.V7Calibration
