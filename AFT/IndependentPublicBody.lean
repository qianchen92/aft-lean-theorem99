import AFT.IndependentPublicFactorization
import AFT.SafeBodyOutput

/-! # The full independent body response and exact canonical cancellation -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance independentBodyColorDecEq (Color : Type*) : DecidableEq Color := Classical.decEq _
local instance independentBodyFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {Color : Type*} [Fintype Color]

theorem centeredGeneratingLinear_single_mass (reference profile : Color → ℝ) :
    centeredGeneratingLinear reference (fun word : Fin 1 → Color => profile (word 0))=
      singleGenerating reference profile := by
  unfold centeredGeneratingLinear
  simp only [LinearMap.coe_mk,AddHom.coe_mk]
  rw [← (Equiv.funUnique (Fin 1) Color).symm.sum_comp]
  simp only [Fin.prod_univ_one,Equiv.funUnique_symm_apply,uniqueElim_const,
    Algebra.smul_def,MvPolynomial.algebraMap_eq,singleGenerating]
end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open GaussianSource RepresentedPolynomial SafeConvolution Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
local instance independentPublicBodyFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- This retains the complete constant and linear body response before
any canonical assumption is applied. -/
theorem independent_body_generating_average (C : ℝ) (n : ℕ) (beta : ℝ)
    (density : Fin (Parameters.modulus n) → ℝ) :
    (∑ root : Window (v7RootCutoff n),MvPolynomial.C ((bodyRootReference n).weight root)*
      centeredGeneratingLinear (actualReferenceLaw C n beta).weight
        (actualBodyDensityChannel C n beta root density))=
      singleGenerating (actualReferenceLaw C n beta).weight
        (rootProfileOperator n (fun color => (actualBodyLaw C n beta).weight color*density color)) := by
  have he (root : Window (v7RootCutoff n)) :
      actualBodyDensityChannel C n beta root density=
        fun word : Fin 1 → Fin (Parameters.modulus n) => actualBodySignedProfile C n beta density root (word 0) := rfl
  simp_rw [he,centeredGeneratingLinear_single_mass]
  simp only [singleGenerating,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro color _
  simp only [← mul_assoc,← map_mul,← Finset.sum_mul,← map_sum]
  rfl

theorem independent_body_generating_formula_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ density : Fin (Parameters.modulus n) → ℝ,
      (∑ root : Window (v7RootCutoff n),MvPolynomial.C ((bodyRootReference n).weight root)*
        centeredGeneratingLinear (actualReferenceLaw C n (beta n)).weight
          (actualBodyDensityChannel C n (beta n) root density))=
      actualLeadingOutput C n (beta n) (MvPolynomial.X (bodySingletonInput density))+
        MvPolynomial.C ((actualBodyLaw C n (beta n)).expectation density)*
          (1-profileForm (actualReferenceLaw C n (beta n)).weight) := by
  filter_upwards [actual_reference_laws_eventually C hC beta hbeta,
    actual_body_center_probability_eventually C hC beta hbeta,eventually_ge_atTop 2]
    with n hl hb hn density
  let profile := fun color => (actualBodyLaw C n (beta n)).weight color*density color
  have hs (color) (ho : color ∉ safePalette n) : profile color=0 := by
    dsimp [profile]
    rw [hl.2.1,hb.2.2 color ho,zero_mul]
  have hm : v7RootCutoff n ≤ Parameters.safeMargin n := by
    simp only [v7RootCutoff,Parameters.safeMargin,Parameters.security_eq n hn]
    omega
  have he := safe_root_convolution_eq n profile hs hm
  rw [independent_body_generating_average,← he,singleGenerating_formula,actualLeadingOutput_body]
  have hmass : (∑ color,convolution (actualRootLaw n).weight profile color)=
      (actualBodyLaw C n (beta n)).expectation density := by
    simp_rw [← actualBodyChannel_profile]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum,actualBodyChannel_mass,mul_one]
    rfl
  rw [hmass]
  rfl

theorem independent_body_generating_canonical_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ density : Fin (Parameters.modulus n) → ℝ,
      (actualBodyLaw C n (beta n)).expectation density=0 →
      (∑ root : Window (v7RootCutoff n),MvPolynomial.C ((bodyRootReference n).weight root)*
        centeredGeneratingLinear (actualReferenceLaw C n (beta n)).weight
          (actualBodyDensityChannel C n (beta n) root density))=
      actualLeadingOutput C n (beta n) (MvPolynomial.X (bodySingletonInput density)) := by
  filter_upwards [independent_body_generating_formula_eventually C hC beta hbeta] with n he density hd
  rw [he density,hd,map_zero,zero_mul,add_zero]
end
end AFT.V7Calibration
