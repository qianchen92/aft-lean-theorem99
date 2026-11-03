import CurrentAFT.RationalRootMassProgram
import CurrentAFT.IndependentReferenceEnergy

/-! # Computed independent positive four-endpoint mass

Both compensator and attachment roots are independently averaged, while
one and the same scalar is retained in the pair and attachment. Every
leaf is an actual rational proposal, local pair, or Gaussian table entry.
-/
namespace CurrentAFT.RationalPositiveReferenceProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles ProposalPrimary
  RationalProposalProgram LocalReferenceEnergy RationalRootMassProgram
open scoped BigOperators
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def fixedMass (security bits : ℕ) (compensatorRoot attachmentRoot scalar : ℤ)
    (word : Fin 4 → ℕ) : ℚ :=
  ∑ primaryColor : Fin (PublicParameterProgram.modulus security).count,
    ∑ centerColor : Fin (PublicParameterProgram.modulus security).count,
      primary security bits primaryColor.val * center security bits centerColor.val *
        LocalPairProgram.current security bits primaryColor.val scalar (word 1) (word 2) *
          controlRest security compensatorRoot attachmentRoot scalar centerColor.val word

def current (security bits : ℕ) (word : Fin 4 → ℕ) : ℚ :=
  ∑ scalar : Window (Parameters.sourceCutoff security - 1),
    gaussianWeight security (Parameters.sourceCutoff security - 1) bits scalar *
      seedEvaluate security bits (fun compensator => seedEvaluate security bits (fun attachment =>
        fixedMass security bits (actualBlur security compensator) (actualBlur security attachment) scalar.val word))

noncomputable section
open scoped Classical
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw centerLaw

theorem fixedMass_cast (security bits : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : FirstHistogram.Scalar security) (word : Fin 4 → FirstHistogram.Palette security) :
    (fixedMass security bits compensatorRoot attachmentRoot scalar.val (fun i => (word i).val) : ℝ) =
      ∑ primaryColor : FirstHistogram.Palette security, ∑ centerColor : FirstHistogram.Palette security,
        (approximatePrimaryLaw security bits).weight primaryColor *
          (approximateCenterLaw security bits).weight centerColor *
            (LocalPairProgram.current security bits primaryColor.val scalar.val (word 1).val (word 2).val : ℝ) *
              actualRest security compensatorRoot attachmentRoot scalar centerColor word := by
  unfold fixedMass
  rw [PublicParameterProgram.modulus_value]
  simp only [Rat.cast_sum, Rat.cast_mul, controlRest_cast]
  rfl

theorem actual_fixedMass_formula (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : FirstHistogram.Scalar security) (word : Fin 4 → FirstHistogram.Palette security) :
    (PositiveFirstCoefficient.positiveFourLaw security compensatorRoot attachmentRoot scalar).weight word =
      ∑ primaryColor, ∑ centerColor, (primaryLaw security).weight primaryColor *
        (centerLaw security).weight centerColor *
          (pairAt security primaryColor scalar).weight (word 1, word 2) *
            actualRest security compensatorRoot attachmentRoot scalar centerColor word := by
  rw [IndependentReferenceEnergy.fixedPositive_control]
  simp only [PhysicalSynthesis.groupLaw, FiniteDist.prod_weight, Fintype.sum_prod_type,
    FixedPairedFirst.fixedControlLaw_weight]
  apply Finset.sum_congr rfl
  intro primaryColor _
  apply Finset.sum_congr rfl
  intro centerColor _
  unfold actualRest PairedReferenceEnergy.controlMass FirstHistogram.atom
  split_ifs <;> ring

private theorem product_error (a a' b b' c c' A B epsilon : ℝ)
    (ha : |a| ≤ 1) (hda : |a' - a| ≤ A * epsilon)
    (hb : |b| ≤ 1) (hb' : |b'| ≤ 1) (hdb : |b' - b| ≤ B * epsilon)
    (hc' : |c'| ≤ 4) (hdc : |c' - c| ≤ 3 * epsilon)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (he : 0 ≤ epsilon) :
    |a' * b' * c' - a * b * c| ≤ (4 * A + 4 * B + 3) * epsilon := by
  calc
    _ = |(a'-a)*b'*c' + a*(b'-b)*c' + a*b*(c'-c)| := by congr 1; ring
    _ ≤ |(a'-a)*b'*c'| + |a*(b'-b)*c'| + |a*b*(c'-c)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (A*epsilon)*1*4 + 1*(B*epsilon)*4 + 1*1*(3*epsilon) := by
      simp only [abs_mul]
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul (mul_le_mul hda hb' (abs_nonneg _) (by positivity)) hc'
            (abs_nonneg _) (by positivity)
        · exact mul_le_mul (mul_le_mul ha hdb (abs_nonneg _) (by norm_num)) hc'
            (abs_nonneg _) (by positivity)
      · exact mul_le_mul (mul_le_mul ha hb (abs_nonneg _) (by norm_num)) hdc
          (abs_nonneg _) (by norm_num)
    _ = _ := by ring

def fixedErrorConstant (security : ℕ) : ℝ :=
  (Parameters.modulus security : ℝ)^2 * (4 * primaryErrorConstant security +
    4 * (primaryErrorConstant security * Parameters.modulus security + 2) + 3)

theorem fixedMass_error (security bits : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : FirstHistogram.Scalar security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (word : Fin 4 → FirstHistogram.Palette security) :
    |(fixedMass security bits compensatorRoot attachmentRoot scalar.val (fun i => (word i).val) : ℝ) -
      (PositiveFirstCoefficient.positiveFourLaw security compensatorRoot attachmentRoot scalar).weight word| ≤
        fixedErrorConstant security * (1 / (2 : ℝ)^bits) := by
  let epsilon : ℝ := 1 / (2 : ℝ)^bits
  let A := primaryErrorConstant security
  let B := A * Parameters.modulus security + 2
  have he : 0 ≤ epsilon := by positivity
  have he1 : epsilon ≤ 1 := by
    have hpow : (1 : ℝ) ≤ 2^bits := one_le_pow₀ (by norm_num)
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < 2^bits)).mpr (by simpa using hpow)
  have hA : 0 ≤ A := by dsimp [A, primaryErrorConstant]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  rw [fixedMass_cast, actual_fixedMass_formula, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _primaryColor : FirstHistogram.Palette security,
        ∑ _centerColor : FirstHistogram.Palette security, (4*A+4*B+3)*epsilon := by
      apply Finset.sum_le_sum
      intro primaryColor _
      rw [← Finset.sum_sub_distrib]
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro centerColor _
      let c' : ℝ := LocalPairProgram.current security bits primaryColor.val scalar.val (word 1).val (word 2).val
      let c := (pairAt security primaryColor scalar).weight (word 1, word 2)
      have hc : |c'-c| ≤ 3*epsilon :=
        (LocalPairProgram.current_error security bits primaryColor (word 1) (word 2) scalar).trans_eq (by dsimp [epsilon]; ring)
      have hctrue : |c| ≤ 1 := by
        rw [abs_of_nonneg ((pairAt security primaryColor scalar).nonneg _)]
        exact (pairAt security primaryColor scalar).atom_le_one _
      have hc' : |c'| ≤ 4 := by
        have h := (abs_add_le (c'-c) c).trans (add_le_add hc hctrue)
        have hid : c'-c+c=c' := by ring
        rw [hid] at h
        linarith
      have hp : |(approximatePrimaryLaw security bits).weight primaryColor - (primaryLaw security).weight primaryColor| ≤ A*epsilon := by
        simpa only [approximatePrimaryLaw, primaryLaw, A, primaryErrorConstant, epsilon] using
          primary_error security bits primaryColor hprecision hbudget
      have hb : |(approximateCenterLaw security bits).weight centerColor - (centerLaw security).weight centerColor| ≤ B*epsilon := by
        simpa only [approximateCenterLaw, centerLaw, B, A, primaryErrorConstant, epsilon] using
          center_error security bits centerColor hprecision hbudget
      have hterm := product_error ((primaryLaw security).weight primaryColor)
        ((approximatePrimaryLaw security bits).weight primaryColor) ((centerLaw security).weight centerColor)
        ((approximateCenterLaw security bits).weight centerColor) c c' A B epsilon
        (by rw [abs_of_nonneg ((primaryLaw security).nonneg _)]; exact (primaryLaw security).atom_le_one _) hp
        (by rw [abs_of_nonneg ((centerLaw security).nonneg _)]; exact (centerLaw security).atom_le_one _)
        (by rw [abs_of_nonneg ((approximateCenterLaw security bits).nonneg _)]; exact (approximateCenterLaw security bits).atom_le_one _) hb
        hc' hc hA hB he
      rw [← sub_mul, abs_mul]
      exact (mul_le_mul hterm (actualRest_bound security compensatorRoot attachmentRoot scalar centerColor word)
        (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      dsimp [fixedErrorConstant, A, B, epsilon]
      ring

def approximateRootLaw (security bits : ℕ) : FiniteDist (IndependentReferenceEnergy.Roots security) :=
  (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (Parameters.sourceCutoff security - 1) bits).prod
    ((approximateSeedLaw security bits).prod (approximateSeedLaw security bits))

theorem current_cast (security bits : ℕ) (word : Fin 4 → FirstHistogram.Palette security) :
    (current security bits (fun i => (word i).val) : ℝ) =
      (approximateRootLaw security bits).expectation (fun roots =>
        (fixedMass security bits (actualBlur security roots.2.1) (actualBlur security roots.2.2)
          roots.1.val (fun i => (word i).val) : ℝ)) := by
  simp only [current, Rat.cast_sum, Rat.cast_mul, gaussianWeight_eq, seedEvaluate_cast]
  unfold approximateRootLaw
  simp only [FiniteDist.expectation_prod]
  rfl

theorem root_l1 (security bits : ℕ) :
    (∑ roots, |(approximateRootLaw security bits).weight roots -
      (IndependentReferenceEnergy.rootLaw security).weight roots|) ≤ 7 * (1 / (2 : ℝ)^bits) := by
  have hs := windowApproxLaw_l1 (WindowGaussianSampler.squaredWidth security) (Parameters.sourceWidth security)
    (Parameters.sourceCutoff security - 1) bits (WindowGaussianSampler.squaredWidth_positive security)
    (WindowGaussianSampler.squaredWidth_real security).symm
  have hp := FiniteDist.l1_prod_le (approximateSeedLaw security bits) (actualSeedLaw security)
    (approximateSeedLaw security bits) (actualSeedLaw security)
  have hall := FiniteDist.l1_prod_le
    (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (Parameters.sourceCutoff security - 1) bits)
    (scalarLaw security) ((approximateSeedLaw security bits).prod (approximateSeedLaw security bits))
    ((actualSeedLaw security).prod (actualSeedLaw security))
  exact hall.trans ((add_le_add hs (hp.trans (add_le_add (seed_l1 security bits) (seed_l1 security bits)))).trans_eq (by ring))

def errorConstant (security : ℕ) : ℝ := fixedErrorConstant security + 7

theorem current_error (security bits : ℕ)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (word : Fin 4 → FirstHistogram.Palette security) :
    |(current security bits (fun i => (word i).val) : ℝ) -
      (NormalizedLocalPolynomial.independentPositiveLaw security).weight word| ≤
        errorConstant security * (1 / (2 : ℝ)^bits) := by
  let approximate := approximateRootLaw security bits
  let actual := IndependentReferenceEnergy.rootLaw security
  let test := fun roots : IndependentReferenceEnergy.Roots security =>
    (PositiveFirstCoefficient.positiveFourLaw security (actualBlur security roots.2.1)
      (actualBlur security roots.2.2) roots.1).weight word
  let computed := fun roots : IndependentReferenceEnergy.Roots security =>
    (fixedMass security bits (actualBlur security roots.2.1) (actualBlur security roots.2.2)
      roots.1.val (fun i => (word i).val) : ℝ)
  have hsource : |approximate.expectation test - actual.expectation test| ≤ 7 * (1 / (2 : ℝ)^bits) := by
    have h := CyclePatternProgram.expectation_difference_le_l1 approximate actual test 1
      (fun roots => by
        rw [abs_of_nonneg (FiniteDist.nonneg _ _)]
        exact FiniteDist.atom_le_one _ _)
    exact h.trans (by simpa only [one_mul] using root_l1 security bits)
  have hentries : |approximate.expectation computed - approximate.expectation test| ≤
      fixedErrorConstant security * (1 / (2 : ℝ)^bits) := by
    unfold FiniteDist.expectation
    rw [← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ roots, approximate.weight roots * (fixedErrorConstant security * (1 / (2 : ℝ)^bits)) := by
        apply Finset.sum_le_sum
        intro roots _
        rw [← mul_sub, abs_mul, abs_of_nonneg (approximate.nonneg roots)]
        exact mul_le_mul_of_nonneg_left (fixedMass_error security bits _ _ roots.1 hprecision hbudget word)
          (approximate.nonneg roots)
      _ = _ := by rw [← Finset.sum_mul, approximate.sum_one, one_mul]
  rw [current_cast, IndependentReferenceEnergy.independentPositive_mixture]
  change |approximate.expectation computed - actual.expectation test| ≤ _
  exact ((abs_sub_le _ _ _).trans (add_le_add hentries hsource)).trans_eq (by unfold errorConstant; ring)

end
end CurrentAFT.RationalPositiveReferenceProgram
