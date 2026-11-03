import AFT.IndependentRootBlock
import AFT.IndependentBodyPositive
import AFT.PhysicalRootFactorization
import AFT.SafeBodyOutput

/-! # The literal positive local denominators are the actual background blocks -/
namespace AFT.RepresentedPolynomial
open PhysicalBlockTensors
open scoped BigOperators Classical
noncomputable section
variable {Color : Type*} [Fintype Color]
local instance independentDenominatorGenericFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

theorem centeredGeneratingLinear_triple_mul_single (reference : Color → ℝ)
    (triple : Color → Color → Color → ℝ) (single : Color → ℝ) :
    centeredGeneratingLinear reference (fun word : Fin 4 → Color =>
      triple (word 0) (word 1) (word 2)*single (word 3)) =
      tripleGenerating reference triple*singleGenerating reference single := by
  unfold centeredGeneratingLinear
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [← quadrupleEquiv.symm.sum_comp]
  simp only [Fintype.sum_prod_type, Fin.prod_univ_four]
  change (∑ first, ∑ second, ∑ third, ∑ fourth,
    (triple first second third*single fourth) •
      (centeredFactor reference first*centeredFactor reference second*
        centeredFactor reference third*centeredFactor reference fourth)) = _
  simp only [tripleGenerating, singleGenerating]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq, map_mul]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  apply Finset.sum_congr rfl
  intro third _
  apply Finset.sum_congr rfl
  intro fourth _
  ring
end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration PhysicalBlockTensors RepresentedPolynomial Filter SafeConvolution
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
local instance independentDenominatorFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance independentDenominatorSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
attribute [local instance] actualModulusNeZero

theorem conditionalJointOutput_primary (C : ℝ) (n : ℕ)
    (primary : FiniteDist (Fin (Parameters.modulus n)))
    (hsign : ∑ mark, primary.weight mark*paletteSign (Parameters.modulus n) mark = 0)
    (attached : Window (legCutoff C n-1) → ℝ) (first second) :
    (∑ mark, primary.weight mark*conditionalJointOutput C n mark attached first second) =
      (1-v7Activation C n)*(∑ source, (inactiveLegSource C n).weight source*
        inactivePairAtSource C n source first second*attached source) +
      v7Activation C n*primary.weight first*
        blurredAnchorKernel (Parameters.modulus n) (Parameters.anchorWidth n)
          (bodyShift C n) (bodyBlur C n) first second.val*attached (windowZero _) := by
  have hpair (source) : (∑ mark, primary.weight mark*conditionalPairAtSource C n mark source first second) =
      inactivePairAtSource C n source first second := by
    simp only [conditionalPairAtSource_formula, mul_add, Finset.sum_add_distrib,
      ← mul_assoc, ← Finset.sum_mul, hsign, primary.sum_one, one_mul, zero_mul, add_zero]
  simp only [conditionalJointOutput, mul_add, Finset.sum_add_distrib]
  apply congrArg₂ (· + ·)
  · calc
      _ = (1-v7Activation C n)*∑ source, ((inactiveLegSource C n).weight source*attached source)*
          ∑ mark, primary.weight mark*conditionalPairAtSource C n mark source first second := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro source _
        apply Finset.sum_congr rfl
        intro mark _
        ring
      _ = _ := by
        simp only [hpair, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro source _
        ring
  · simp only [mul_ite, ite_mul, mul_zero, zero_mul, mul_one, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    ring

/-- The true calibrated-primary average of the full chart has the same
retained attachment source as the physical background triple. -/
theorem signedChartTriple_primary_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    (∀ mark attached first second, publicChartRaw C n mark (charts mark) attached first second =
      conditionalJointOutput C n mark attached first second) →
    ∀ root queue : ℤ, |root| ≤ (v7RootCutoff n : ℤ) → |queue| ≤ (queueCutoff n : ℤ) →
      signedChartTriple C n (beta n) charts root queue (actualPrimaryLaw C n (beta n)).weight =
        actualFixedRootTriple C n (beta n) root queue := by
  filter_upwards [actual_reference_laws_eventually C hC beta hbeta,
    actual_shifted_body_law_eventually C hC beta hbeta] with n hl hb charts hc root queue hr hq
  have hsign : (∑ mark, (actualPrimaryLaw C n (beta n)).weight mark*paletteSign (Parameters.modulus n) mark) = 0 := by
    rw [hl.1]
    exact actualPrimary_sign_fair C (beta n) n
  funext first second attached
  unfold signedChartTriple fixedChartTriple
  simp only [hc]
  rw [conditionalJointOutput_primary C n _ hsign]
  have hbody (source : Window (legCutoff C n-1)) :
      (actualShiftedBodyLaw C n (beta n) (root+source+queue)).weight =
        integerShiftProfile n (actualBodyCenter C n (beta n)) (root+source+queue) :=
    (hb _ (actualBodyBranch_shift_bound C n root queue hr hq (.inr source))).1
  have hzero := hb (root+queue) (by
    simpa only [actualSourceShift, add_zero] using actualBodyBranch_shift_bound C n root queue hr hq (.inl ()))
  simp only [hbody, windowZero, add_zero, hzero.1, actualFixedRootTriple, actualMarkedPair, hl.1]
  ring

/-- This is equality of the actual four-output mass, before any truncation
or inverse. The two roots are independent here and only here. -/
theorem independentPairedPositiveMass_factor_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    (∀ mark attached first second, publicChartRaw C n mark (charts mark) attached first second =
      conditionalJointOutput C n mark attached first second) → ∀ word : Fin 4 → Fin (Parameters.modulus n),
      independentPairedPositiveMass C n (beta n) charts word =
        actualLocalTriple C n (beta n) 0 (word 0) (word 1) (word 2)*
          attachedBodyAtSource C n (beta n) 0 0 (word 3) := by
  filter_upwards [signedChartTriple_primary_eventually C hC beta hbeta,
    actual_reference_laws_eventually C hC beta hbeta] with n ht hl charts hc word
  unfold independentPairedPositiveMass
  simp_rw [fixedPairedKernel_average_factor]
  change (∑ roots, (pairedRootReference n).weight roots*
    (signedChartTriple C n (beta n) charts roots.1 0 (actualPrimaryLaw C n (beta n)).weight
      (word 0) (word 1) (word 2)*
        integerShiftProfile n (actualBodyLaw C n (beta n)).weight roots.2 (word 3))) = _
  have he (roots : Window (v7RootCutoff n) × Window (v7RootCutoff n)) :=
    congrFun (congrFun (congrFun (ht charts hc roots.1 0
      (abs_le.mpr (Finset.mem_Icc.mp roots.1.property)) (by simp)) (word 0)) (word 1)) (word 2)
  simp_rw [he, hl.2.1]
  rw [← actualFixedRootTriple_root_average C n (beta n) 0 (word 0) (word 1) (word 2)]
  simp only [pairedRootReference, FiniteDist.prod_weight, Fintype.sum_prod_type, attachedBodyAtSource,
    add_zero]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro firstRoot _
  apply Finset.sum_congr rfl
  intro secondRoot _
  ring

theorem independentPairedPositiveMass_polynomial_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    (∀ mark attached first second, publicChartRaw C n mark (charts mark) attached first second =
      conditionalJointOutput C n mark attached first second) →
    ∀ leg : Fin (Parameters.legs n), ∀ body : Fin (Parameters.bodies n-Parameters.legs n),
      centeredGeneratingLinear (actualReferenceLaw C n (beta n)).weight (independentPairedPositiveMass C n (beta n) charts) =
        blockPhysicalPolynomial C n (beta n) (.inl leg) 0*blockPhysicalPolynomial C n (beta n) (.inr body) 0 := by
  filter_upwards [independentPairedPositiveMass_factor_eventually C hC beta hbeta,
    actual_reference_laws_eventually C hC beta hbeta] with n hf hl charts hc leg body
  have he := funext (hf charts hc)
  rw [he, centeredGeneratingLinear_triple_mul_single, hl.2.2]
  rfl

/-- The reserved-body denominator is also the actual unshifted background
block, with the true calibrated center and root marginal. -/
theorem independentBodyPositiveMass_polynomial_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ body : Fin (Parameters.bodies n-Parameters.legs n),
      centeredGeneratingLinear (actualReferenceLaw C n (beta n)).weight (independentBodyPositiveMass C n (beta n)) =
        blockPhysicalPolynomial C n (beta n) (.inr body) 0 := by
  filter_upwards [actual_reference_laws_eventually C hC beta hbeta,
    actual_body_center_probability_eventually C hC beta hbeta, eventually_ge_atTop 2] with n hl hb hn body
  have hmargin : v7RootCutoff n ≤ Parameters.safeMargin n := by
    simp only [v7RootCutoff, Parameters.safeMargin, Parameters.security_eq n hn]
    omega
  have he : independentBodyPositiveProfile C n (beta n) = attachedBodyAtSource C n (beta n) 0 0 := by
    funext output
    unfold independentBodyPositiveProfile
    rw [actualBodyChannel_profile, hl.2.1,
      safe_root_convolution_eq n _ hb.2.2 hmargin]
    simp only [rootProfileOperator, LinearMap.coe_mk, AddHom.coe_mk, attachedBodyAtSource, add_zero]
  unfold centeredGeneratingLinear
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [← (Equiv.funUnique (Fin 1) (Fin (Parameters.modulus n))).symm.sum_comp]
  simp only [Fin.prod_univ_one, Equiv.funUnique_symm_apply, uniqueElim_const, independentBodyPositiveMass,
    he, Algebra.smul_def, MvPolynomial.algebraMap_eq, hl.2.2, blockPhysicalPolynomial, singleGenerating]
end
end AFT.V7Calibration
