import CurrentAFT.RationalPositiveReferenceProgram
import CurrentAFT.RationalLegCoefficientExtraction
import CurrentAFT.RootReferenceColumns
import CurrentAFT.CalibrationCoordinateError

/-! # The actual same-scalar three-endpoint mass before its higher coefficients -/
namespace CurrentAFT.RationalLegMassProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion
open PositiveFirstCoefficient (positiveTripleLaw positiveFourLaw consEquiv)
open PairedReferenceEnergy (compensatorAt)
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def fixed (security bits : ℕ) (root scalar : ℤ) (word : Fin 3 → ℕ) : ℚ :=
  ∑ compensator : Fin (PublicParameterProgram.modulus security).count,
    RationalPositiveReferenceProgram.fixedMass security bits 0 root scalar (Fin.cons compensator.val word)

def atRoot (security bits : ℕ) (root : ℤ) (word : Fin 3 → ℕ) : ℚ :=
  ∑ scalar : Window ((security + 2)^2 - 1),
    RationalProposalProgram.gaussianWeight security ((security + 2)^2 - 1) bits scalar *
      fixed security bits root scalar.val word

def mean (security bits : ℕ) (word : Fin 3 → ℕ) : ℚ :=
  ∑ root : Fin (PublicParameterProgram.modulus security).count,
    RootSignedMassProgram.referenceEntry security bits root.val * atRoot security bits root.val word

def difference (security bits : ℕ) (root : ℤ) (word : Fin 3 → ℕ) : ℚ :=
  atRoot security bits root word - mean security bits word

noncomputable section
open scoped Classical
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw centerLaw PublicParameterProgram.modulus
attribute [local irreducible] rootReference ActualBlockFock.primaryLawAt

theorem four_marginal (security : ℕ) (root : ℤ) (scalar : FirstHistogram.Scalar security)
    (word : Fin 3 → Palette security) :
    (∑ compensator : Palette security,
      (positiveFourLaw security 0 root scalar).weight (Fin.cons compensator word)) =
        (positiveTripleLaw security root scalar).weight word := by
  have hpoint (compensator : Palette security) :
      (positiveFourLaw security 0 root scalar).weight (Fin.cons compensator word) =
        (compensatorAt security 0).weight compensator * (positiveTripleLaw security root scalar).weight word := by
    change (((compensatorAt security 0).prod (positiveTripleLaw security root scalar)).map
      (consEquiv (Palette security))).weight (Fin.cons compensator word) = _
    rw [FiniteDist.map_equiv_weight]
    rfl
  simp only [hpoint, ← Finset.sum_mul, FiniteDist.sum_one, one_mul]

theorem fixed_error (security bits : ℕ) (root : ℤ) (scalar : FirstHistogram.Scalar security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) (word : Fin 3 → Palette security) :
    |(fixed security bits root scalar.val (fun index => (word index).val) : ℝ) -
      (positiveTripleLaw security root scalar).weight word| ≤
      (Parameters.modulus security : ℝ) * RationalPositiveReferenceProgram.fixedErrorConstant security * (1 / (2 : ℝ)^bits) := by
  unfold fixed
  rw [PublicParameterProgram.modulus_value, Rat.cast_sum, ← four_marginal, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _compensator : Palette security,
        RationalPositiveReferenceProgram.fixedErrorConstant security * (1 / (2 : ℝ)^bits) := by
      apply Finset.sum_le_sum
      intro compensator _
      exact RationalPositiveReferenceProgram.fixedMass_error security bits 0 root scalar hprecision hbudget (Fin.cons compensator word)
    _ = _ := by simp; ring

def atRootErrorConstant (security : ℕ) : ℝ :=
  (Parameters.modulus security : ℝ) * RationalPositiveReferenceProgram.fixedErrorConstant security + 1

theorem atRootError_nonneg (security : ℕ) : 0 ≤ atRootErrorConstant security := by
  unfold atRootErrorConstant RationalPositiveReferenceProgram.fixedErrorConstant RationalRootMassProgram.primaryErrorConstant
  positivity

theorem atRoot_cast (security bits : ℕ) (root : ℤ) (word : Fin 3 → Palette security) :
    (atRoot security bits root (fun index => (word index).val) : ℝ) =
      (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (Parameters.sourceCutoff security - 1) bits).expectation
        (fun scalar => (fixed security bits root scalar.val (fun index => (word index).val) : ℝ)) := by
  have hcut : (security + 2)^2 - 1 = Parameters.sourceCutoff security - 1 := by
    simp only [Parameters.sourceCutoff, Parameters.base]
  unfold atRoot
  rw [hcut]
  simp only [Rat.cast_sum, Rat.cast_mul, RationalProposalProgram.gaussianWeight_eq,
    FiniteDist.expectation, windowApproxLaw]

theorem atRoot_error (security bits : ℕ) (root : ℤ)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) (word : Fin 3 → Palette security) :
    |(atRoot security bits root (fun index => (word index).val) : ℝ) - (ActualBlockFock.primaryLawAt security root).weight word| ≤
      atRootErrorConstant security * (1 / (2 : ℝ)^bits) := by
  let approximate := windowApproxLaw (WindowGaussianSampler.squaredWidth security) (Parameters.sourceCutoff security - 1) bits
  let test := fun scalar : FirstHistogram.Scalar security => (positiveTripleLaw security root scalar).weight word
  let computed := fun scalar : FirstHistogram.Scalar security =>
    (fixed security bits root scalar.val (fun index => (word index).val) : ℝ)
  have hl1 : (∑ scalar, |approximate.weight scalar - (scalarLaw security).weight scalar|) ≤ 1 / (2 : ℝ)^bits :=
    windowApproxLaw_l1 _ _ _ _ (WindowGaussianSampler.squaredWidth_positive security)
      (WindowGaussianSampler.squaredWidth_real security).symm
  have htest (scalar : FirstHistogram.Scalar security) : |test scalar| ≤ 1 := by
    rw [abs_of_nonneg ((positiveTripleLaw security root scalar).nonneg word)]
    exact (positiveTripleLaw security root scalar).atom_le_one word
  have hk : |approximate.expectation computed - approximate.expectation test| ≤
      (Parameters.modulus security : ℝ) * RationalPositiveReferenceProgram.fixedErrorConstant security * (1 / (2 : ℝ)^bits) := by
    have h := CalibrationCoordinateError.expectation_abs_bound approximate (fun scalar => computed scalar - test scalar) _
      (fun scalar => fixed_error security bits root scalar hprecision hbudget word)
    simpa only [FiniteDist.expectation, mul_sub, Finset.sum_sub_distrib] using h
  have hs := (CyclePatternProgram.expectation_difference_le_l1 approximate (scalarLaw security) test 1 htest).trans
    (by simpa only [one_mul] using hl1)
  rw [atRoot_cast]
  rw [ActualBlockFock.primaryLawAt, FiniteDist.mix_weight]
  change |approximate.expectation computed - (scalarLaw security).expectation test| ≤ _
  exact (abs_sub_le _ (approximate.expectation test) _).trans ((add_le_add hk hs).trans_eq (by unfold atRootErrorConstant; ring))

theorem finEquiv_val (modulus : ℕ) [NeZero modulus] (color : Fin modulus) :
    ((ZMod.finEquiv modulus) color).val = color.val := by
  cases modulus with
  | zero => exact (NeZero.ne (0 : ℕ) rfl).elim
  | succ modulus => rfl

theorem mean_cast (security bits : ℕ) (word : Fin 3 → Palette security) :
    (mean security bits (fun index => (word index).val) : ℝ) =
      ∑ root : Root security, (RootSignedMassProgram.referenceEntry security bits root.val : ℝ) *
        (atRoot security bits root.val (fun index => (word index).val) : ℝ) := by
  unfold mean
  rw [PublicParameterProgram.modulus_value]
  simp only [Rat.cast_sum, Rat.cast_mul]
  calc
    _ = ∑ root : Palette security,
        (RootSignedMassProgram.referenceEntry security bits ((ZMod.finEquiv (Parameters.modulus security)) root).val : ℝ) *
          (atRoot security bits ((ZMod.finEquiv (Parameters.modulus security)) root).val (fun index => (word index).val) : ℝ) := by
      apply Finset.sum_congr (by ext; simp)
      intro root _
      simp only [finEquiv_val]
    _ = _ := (ZMod.finEquiv (Parameters.modulus security)).toEquiv.sum_comp (fun root : Root security =>
        (RootSignedMassProgram.referenceEntry security bits root.val : ℝ) *
          (atRoot security bits root.val (fun index => (word index).val) : ℝ))

def meanErrorConstant (security : ℕ) : ℝ :=
  (Parameters.modulus security : ℝ) * (atRootErrorConstant security + 2)

theorem mean_error (security bits : ℕ)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) (word : Fin 3 → Palette security) :
    |(mean security bits (fun index => (word index).val) : ℝ) - RootTaggedLegHigher.rawMassLinear security 1 word| ≤
      meanErrorConstant security * (1 / (2 : ℝ)^bits) := by
  rw [mean_cast]
  simp only [RootTaggedLegHigher.rawMassLinear, LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply, mul_one]
  change |(∑ root : Root security, _) - ∑ root : Root security,
    (rootReference security).weight root * (ActualBlockFock.primaryLawAt security root.val).weight word| ≤ _
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _root : Root security, (atRootErrorConstant security + 2) * (1 / (2 : ℝ)^bits) := by
      apply Finset.sum_le_sum
      intro root _
      have hroot := RootSignedMassProgram.referenceEntry_bounds security bits root
      have hrootError := RootSignedMassProgram.referenceEntry_error security bits root
      have hvalue := atRoot_error security bits root.val hprecision hbudget word
      have hmass : |(ActualBlockFock.primaryLawAt security root.val).weight word| ≤ 1 := by
        rw [abs_of_nonneg ((ActualBlockFock.primaryLawAt security root.val).nonneg word)]
        exact (ActualBlockFock.primaryLawAt security root.val).atom_le_one word
      calc
        _ = |(RootSignedMassProgram.referenceEntry security bits root.val : ℝ) *
            ((atRoot security bits root.val (fun index => (word index).val) : ℝ) - (ActualBlockFock.primaryLawAt security root.val).weight word) +
            ((RootSignedMassProgram.referenceEntry security bits root.val : ℝ) - (rootReference security).weight root) *
              (ActualBlockFock.primaryLawAt security root.val).weight word| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
        _ ≤ 1 * (atRootErrorConstant security * (1 / (2 : ℝ)^bits)) + (2 / (2 : ℝ)^bits) * 1 := by
          simp only [abs_mul]
          exact add_le_add (mul_le_mul (by rw [abs_of_nonneg hroot.1]; exact hroot.2) hvalue (abs_nonneg _) (by norm_num))
            (mul_le_mul hrootError hmass (abs_nonneg _) (by positivity))
        _ = _ := by ring
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]; unfold meanErrorConstant; ring

def differenceErrorConstant (security : ℕ) : ℝ := atRootErrorConstant security + meanErrorConstant security

theorem errorConstants_nonneg (security : ℕ) :
    0 ≤ meanErrorConstant security ∧ 0 ≤ differenceErrorConstant security := by
  have h := atRootError_nonneg security
  have hmean : 0 ≤ meanErrorConstant security := by unfold meanErrorConstant; positivity
  exact ⟨hmean, add_nonneg h hmean⟩

theorem difference_error (security bits : ℕ) (root : ℤ)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) (word : Fin 3 → Palette security) :
    |(difference security bits root (fun index => (word index).val) : ℝ) -
      ((ActualBlockFock.primaryLawAt security root).weight word - RootTaggedLegHigher.rawMassLinear security 1 word)| ≤
      differenceErrorConstant security * (1 / (2 : ℝ)^bits) := by
  rw [difference, Rat.cast_sub]
  have hsplit : (atRoot security bits root (fun index => (word index).val) : ℝ) -
      (mean security bits (fun index => (word index).val) : ℝ) -
      ((ActualBlockFock.primaryLawAt security root).weight word - RootTaggedLegHigher.rawMassLinear security 1 word) =
      ((atRoot security bits root (fun index => (word index).val) : ℝ) - (ActualBlockFock.primaryLawAt security root).weight word) -
      ((mean security bits (fun index => (word index).val) : ℝ) - RootTaggedLegHigher.rawMassLinear security 1 word) := by ring
  rw [hsplit]
  exact (abs_sub _ _).trans ((add_le_add (atRoot_error security bits root hprecision hbudget word)
    (mean_error security bits hprecision hbudget word)).trans_eq (by unfold differenceErrorConstant; ring))

end
end CurrentAFT.RationalLegMassProgram
