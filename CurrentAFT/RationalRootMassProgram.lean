import CurrentAFT.RootMassColumns
import CurrentAFT.RationalPairedLiftProgram

/-! # Rational fixed-root paired mass entries

Multiplication by the center reference cancels the paired-score quotient.
The resulting program uses only the actual primary, center, anchor, pair
and scalar tables, finite sums, and rational arithmetic. Unsafe center
colors and zero root atoms require no exceptional division.
-/
namespace CurrentAFT.RationalRootMassProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles ProposalPrimary
  RationalProposalProgram LocalReferenceEnergy
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def anchorScore (security bits : ℕ) (score : ℕ → ℚ) (center : ℕ) : ℚ :=
  ∑ color : Fin (PublicParameterProgram.modulus security).count,
    anchor security bits color.val center * primary security bits color.val * score color.val

def weightedScore (security bits : ℕ) (score : ℕ → ℚ) (primaryColor centerColor : ℕ) : ℚ :=
  center security bits centerColor * score primaryColor -
    LocalPairProgram.activationApprox security bits * anchorScore security bits score centerColor

def controlRest (security : ℕ) (compensatorRoot attachmentRoot scalar : ℤ)
    (centerColor : ℕ) (word : Fin 4 → ℕ) : ℚ :=
  bodyKernel (PublicParameterProgram.modulus security).count (3 * (security + 2)^2)
    (attachmentRoot + scalar) (word 3) *
      (if ((centerColor : ℤ) + compensatorRoot) % (PublicParameterProgram.modulus security).count =
        (word 0 : ℤ) then 1 else 0)

def fixedMass (security bits : ℕ) (compensatorRoot attachmentRoot scalar : ℤ)
    (score : ℕ → ℚ) (word : Fin 4 → ℕ) : ℚ :=
  ∑ primaryColor : Fin (PublicParameterProgram.modulus security).count,
    ∑ centerColor : Fin (PublicParameterProgram.modulus security).count,
      primary security bits primaryColor.val *
        weightedScore security bits score primaryColor.val centerColor.val *
          LocalPairProgram.current security bits primaryColor.val scalar (word 1) (word 2) *
            controlRest security compensatorRoot attachmentRoot scalar centerColor.val word

def scalarAverage (security cutoff bits : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (score : ℕ → ℚ) (word : Fin 4 → ℕ) : ℚ :=
  ∑ scalar : Window cutoff, gaussianWeight security cutoff bits scalar *
    fixedMass security bits compensatorRoot attachmentRoot scalar.val score word

def primaryMass (security bits : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (score : ℕ → ℚ) (word : Fin 4 → ℕ) : ℚ :=
  scalarAverage security ((security + 2)^2 - 1) bits compensatorRoot attachmentRoot score word

noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base primaryLaw centerLaw

def actualWeightedScore (security : ℕ) (score : FirstHistogram.Palette security → ℝ)
    (primaryColor centerColor : FirstHistogram.Palette security) : ℝ :=
  (centerLaw security).weight centerColor * score primaryColor -
    DiffuseProfiles.activation security * PairedResponse.anchorWeightedScore security score centerColor

theorem actual_weightedScore (security : ℕ) (score : FirstHistogram.Palette security → ℝ)
    (primaryColor centerColor : FirstHistogram.Palette security) :
    actualWeightedScore security score primaryColor centerColor =
      (centerLaw security).weight centerColor * PairedResponse.pairedScore security score primaryColor centerColor := by
  unfold actualWeightedScore PairedResponse.pairedScore PairedResponse.compensatorScore
  by_cases hzero : (centerLaw security).weight centerColor = 0
  · rw [hzero, PairedResponse.centerLaw_zero_implies_anchorScore_zero security score centerColor hzero]
    ring
  · field_simp

theorem anchorScore_cast (security bits : ℕ) (score : ℕ → ℚ) (output : FirstHistogram.Palette security) :
    (anchorScore security bits score output.val : ℝ) =
      ControlCoordinates.anchorProfile (approximatePrimaryLaw security bits) (approximateAnchorLaw security bits)
        (fun color : FirstHistogram.Palette security => (score color.val : ℝ)) output := by
  unfold anchorScore
  rw [PublicParameterProgram.modulus_value]
  simp only [Rat.cast_sum, Rat.cast_mul, anchor_cast, ControlCoordinates.anchorProfile]
  apply Finset.sum_congr rfl
  intro color _
  change (approximateAnchorLaw security bits color).weight output *
    (approximatePrimaryLaw security bits).weight color * (score color.val : ℝ) = _
  ring

theorem actual_anchorScore (security : ℕ) (score : FirstHistogram.Palette security → ℝ)
    (output : FirstHistogram.Palette security) :
    PairedResponse.anchorWeightedScore security score output =
      ControlCoordinates.anchorProfile (primaryLaw security) (InwardAnchor.smoothedAnchorLaw security) score output := by
  unfold PairedResponse.anchorWeightedScore ControlCoordinates.anchorProfile
  apply Finset.sum_congr rfl
  intro color _
  ring

theorem weightedScore_cast (security bits : ℕ) (score : ℕ → ℚ)
    (primaryColor centerColor : FirstHistogram.Palette security) :
    (weightedScore security bits score primaryColor.val centerColor.val : ℝ) =
      (approximateCenterLaw security bits).weight centerColor * (score primaryColor.val : ℝ) -
        (LocalPairProgram.activationApprox security bits : ℝ) *
          ControlCoordinates.anchorProfile (approximatePrimaryLaw security bits) (approximateAnchorLaw security bits)
            (fun color : FirstHistogram.Palette security => (score color.val : ℝ)) centerColor := by
  simp only [weightedScore, Rat.cast_sub, Rat.cast_mul, anchorScore_cast]
  rfl

theorem weightedScore_bound (security bits : ℕ) (score : ℕ → ℚ) (bound : ℝ) (hb : 0 ≤ bound)
    (hscore : ∀ color : FirstHistogram.Palette security, |(score color.val : ℝ)| ≤ bound)
    (primaryColor centerColor : FirstHistogram.Palette security) :
    |(weightedScore security bits score primaryColor.val centerColor.val : ℝ)| ≤ 2 * bound := by
  rw [weightedScore_cast]
  apply (abs_sub _ _).trans
  rw [abs_mul, abs_of_nonneg ((approximateCenterLaw security bits).nonneg centerColor),
    abs_mul, abs_of_nonneg (LocalPairProgram.activationApprox_bounds security bits).1]
  have hp := RationalPairedLiftProgram.profile_bound (approximatePrimaryLaw security bits)
    (approximateAnchorLaw security bits) (fun color : FirstHistogram.Palette security => (score color.val : ℝ))
    bound hscore centerColor
  have hc := (approximateCenterLaw security bits).atom_le_one centerColor
  have ha := (LocalPairProgram.activationApprox_bounds security bits).2
  have hfirst := mul_le_mul hc (hscore primaryColor) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hsecond := mul_le_mul ha hp (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  nlinarith

theorem actualWeightedScore_bound (security : ℕ) (score : FirstHistogram.Palette security → ℝ)
    (bound : ℝ) (hb : 0 ≤ bound) (hscore : ∀ color, |score color| ≤ bound)
    (primaryColor centerColor : FirstHistogram.Palette security) :
    |actualWeightedScore security score primaryColor centerColor| ≤ 2 * bound := by
  rw [actualWeightedScore, actual_anchorScore]
  apply (abs_sub _ _).trans
  rw [abs_mul, abs_of_nonneg ((centerLaw security).nonneg centerColor),
    abs_mul, abs_of_pos (activation_pos security)]
  have hp := RationalPairedLiftProgram.profile_bound (primaryLaw security)
    (InwardAnchor.smoothedAnchorLaw security) score bound hscore centerColor
  have hfirst := mul_le_mul ((centerLaw security).atom_le_one centerColor) (hscore primaryColor)
    (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hsecond := mul_le_mul (activation_le_half security) hp (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  nlinarith

def primaryErrorConstant (security : ℕ) : ℝ :=
  64 * (Parameters.base security : ℝ) * Parameters.dimension security

def weightedErrorConstant (security : ℕ) : ℝ :=
  (primaryErrorConstant security * Parameters.modulus security + 2) + 1 +
    (Parameters.modulus security : ℝ) * (primaryErrorConstant security + 1)

theorem weightedScore_error (security bits : ℕ) (score : ℕ → ℚ) (bound : ℝ) (hb : 0 ≤ bound)
    (hscore : ∀ color : FirstHistogram.Palette security, |(score color.val : ℝ)| ≤ bound)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (primaryColor centerColor : FirstHistogram.Palette security) :
    |(weightedScore security bits score primaryColor.val centerColor.val : ℝ) -
      actualWeightedScore security (fun color => (score color.val : ℝ)) primaryColor centerColor| ≤
        weightedErrorConstant security * bound * (1 / (2 : ℝ)^bits) := by
  let epsilon : ℝ := 1 / (2 : ℝ)^bits
  let C := primaryErrorConstant security
  have he : 0 ≤ epsilon := by positivity
  have hC : 0 ≤ C := by dsimp [C, primaryErrorConstant]; positivity
  have hp (color : FirstHistogram.Palette security) :
      |(approximatePrimaryLaw security bits).weight color - (primaryLaw security).weight color| ≤ C * epsilon := by
    simpa only [approximatePrimaryLaw, primaryLaw, C, primaryErrorConstant, epsilon] using
      RationalProposalProgram.primary_error security bits color hprecision hbudget
  have hc : |(approximateCenterLaw security bits).weight centerColor - (centerLaw security).weight centerColor| ≤
      (C * Parameters.modulus security + 2) * epsilon := by
    simpa only [approximateCenterLaw, centerLaw, C, primaryErrorConstant, epsilon] using
      RationalProposalProgram.center_error security bits centerColor hprecision hbudget
  have hanchor := RationalPairedLiftProgram.profile_error (primaryLaw security) (approximatePrimaryLaw security bits)
    (InwardAnchor.smoothedAnchorLaw security) (approximateAnchorLaw security bits)
    (fun color : FirstHistogram.Palette security => (score color.val : ℝ)) bound (C * epsilon) epsilon hb
    (mul_nonneg hC he) he hscore hp (fun color output => by
      simpa only [← anchor_cast] using RationalProposalProgram.anchor_error security bits color output) centerColor
  have ha := LocalPairProgram.activationApprox_error security bits
  have hprofile := RationalPairedLiftProgram.profile_bound (approximatePrimaryLaw security bits)
    (approximateAnchorLaw security bits) (fun color : FirstHistogram.Palette security => (score color.val : ℝ))
    bound hscore centerColor
  rw [weightedScore_cast, actualWeightedScore, actual_anchorScore]
  let approxProfile := ControlCoordinates.anchorProfile (approximatePrimaryLaw security bits) (approximateAnchorLaw security bits)
    (fun color : FirstHistogram.Palette security => (score color.val : ℝ)) centerColor
  let profile := ControlCoordinates.anchorProfile (primaryLaw security) (InwardAnchor.smoothedAnchorLaw security)
    (fun color : FirstHistogram.Palette security => (score color.val : ℝ)) centerColor
  calc
    _ = |((approximateCenterLaw security bits).weight centerColor - (centerLaw security).weight centerColor) *
          (score primaryColor.val : ℝ) -
        (((LocalPairProgram.activationApprox security bits : ℝ) - DiffuseProfiles.activation security) * approxProfile +
          DiffuseProfiles.activation security * (approxProfile - profile))| := by dsimp only [approxProfile, profile]; congr 1; ring
    _ ≤ |((approximateCenterLaw security bits).weight centerColor - (centerLaw security).weight centerColor) *
          (score primaryColor.val : ℝ)| +
        |((LocalPairProgram.activationApprox security bits : ℝ) - DiffuseProfiles.activation security) * approxProfile| +
          |DiffuseProfiles.activation security * (approxProfile - profile)| := by
      have hsplit := abs_sub
        (((approximateCenterLaw security bits).weight centerColor - (centerLaw security).weight centerColor) *
          (score primaryColor.val : ℝ))
        (((LocalPairProgram.activationApprox security bits : ℝ) - DiffuseProfiles.activation security) * approxProfile +
          DiffuseProfiles.activation security * (approxProfile - profile))
      have hsum := abs_add_le
        (((LocalPairProgram.activationApprox security bits : ℝ) - DiffuseProfiles.activation security) * approxProfile)
        (DiffuseProfiles.activation security * (approxProfile - profile))
      linarith
    _ ≤ ((C * Parameters.modulus security + 2) * epsilon) * bound +
        ((1 / 2 : ℝ) * epsilon) * bound +
        (1 / 2 : ℝ) * ((Parameters.modulus security : ℝ) * bound * (C * epsilon + epsilon)) := by
      simp only [abs_mul]
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul hc (hscore primaryColor) (abs_nonneg _) (by positivity)
        · exact mul_le_mul ha hprofile (abs_nonneg _) (by positivity)
      · rw [abs_of_pos (activation_pos security)]
        exact mul_le_mul (activation_le_half security) (by simpa only [Fintype.card_fin] using hanchor)
          (abs_nonneg _) (by norm_num)
    _ ≤ _ := by
      change _ ≤ ((C * Parameters.modulus security + 2) + 1 +
        (Parameters.modulus security : ℝ) * (C + 1)) * bound * epsilon
      have hq : 0 ≤ (Parameters.modulus security : ℝ) := Nat.cast_nonneg _
      nlinarith [mul_nonneg (mul_nonneg hq hb) he,
        mul_nonneg (mul_nonneg (mul_nonneg hq hb) hC) he]

def actualRest (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : FirstHistogram.Scalar security) (centerColor : FirstHistogram.Palette security)
    (word : Fin 4 → FirstHistogram.Palette security) : ℝ :=
  (attachmentAt security attachmentRoot scalar).weight (word 3) *
    FirstHistogram.atom (shiftEquiv security compensatorRoot centerColor) (word 0)

theorem controlRest_cast (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : FirstHistogram.Scalar security) (centerColor : FirstHistogram.Palette security)
    (word : Fin 4 → FirstHistogram.Palette security) :
    (controlRest security compensatorRoot attachmentRoot scalar.val centerColor.val
      (fun index => (word index).val) : ℝ) =
        actualRest security compensatorRoot attachmentRoot scalar centerColor word := by
  have hmargin : 3 * (security + 2)^2 = Parameters.safeMargin security := by
    simp only [Parameters.safeMargin, Parameters.sourceCutoff, Parameters.base]
  unfold controlRest
  rw [PublicParameterProgram.modulus_value, hmargin]
  simp only [Rat.cast_mul]
  rw [bodyKernel_cast]
  change (attachmentAt security attachmentRoot scalar).weight (word 3) * _ = _
  unfold actualRest FirstHistogram.atom
  by_cases hshift : shiftEquiv security compensatorRoot centerColor = word 0
  · simp only [if_pos ((shift_condition security _ _ _).mp hshift), if_pos hshift, Rat.cast_one]
  · simp only [if_neg (mt (shift_condition security _ _ _).mpr hshift), if_neg hshift, Rat.cast_zero]

theorem actualRest_bound (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : FirstHistogram.Scalar security) (centerColor : FirstHistogram.Palette security)
    (word : Fin 4 → FirstHistogram.Palette security) :
    |actualRest security compensatorRoot attachmentRoot scalar centerColor word| ≤ 1 := by
  unfold actualRest FirstHistogram.atom
  split_ifs
  · rw [mul_one, abs_of_nonneg ((attachmentAt security attachmentRoot scalar).nonneg _)]
    exact (attachmentAt security attachmentRoot scalar).atom_le_one _
  · norm_num

theorem fixedMass_cast (security bits : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : FirstHistogram.Scalar security) (score : ℕ → ℚ)
    (word : Fin 4 → FirstHistogram.Palette security) :
    (fixedMass security bits compensatorRoot attachmentRoot scalar.val score (fun index => (word index).val) : ℝ) =
      ∑ primaryColor : FirstHistogram.Palette security, ∑ centerColor : FirstHistogram.Palette security,
        (approximatePrimaryLaw security bits).weight primaryColor *
          (weightedScore security bits score primaryColor.val centerColor.val : ℝ) *
            (LocalPairProgram.current security bits primaryColor.val scalar.val (word 1).val (word 2).val : ℝ) *
              actualRest security compensatorRoot attachmentRoot scalar centerColor word := by
  unfold fixedMass
  rw [PublicParameterProgram.modulus_value]
  simp only [Rat.cast_sum, Rat.cast_mul, controlRest_cast]
  rfl

theorem actual_fixedMass_formula (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : FirstHistogram.Scalar security) (score : FirstHistogram.Palette security → ℝ)
    (word : Fin 4 → FirstHistogram.Palette security) :
    PairedReferenceEnergy.pairedMassAt security compensatorRoot attachmentRoot scalar score word =
      ∑ primaryColor, ∑ centerColor, (primaryLaw security).weight primaryColor *
        actualWeightedScore security score primaryColor centerColor *
          (pairAt security primaryColor scalar).weight (word 1, word 2) *
            actualRest security compensatorRoot attachmentRoot scalar centerColor word := by
  rw [PairedReferenceEnergy.pairedMassAt_control_sum]
  apply Finset.sum_congr rfl
  intro primaryColor _
  apply Finset.sum_congr rfl
  intro centerColor _
  rw [actual_weightedScore]
  unfold actualRest FirstHistogram.atom
  split_ifs <;> ring

private theorem product_error (a a' b b' c c' A B epsilon bound : ℝ)
    (ha : |a| ≤ 1) (ha' : |a' - a| ≤ A * epsilon)
    (hb : |b| ≤ 2 * bound) (hb' : |b'| ≤ 2 * bound)
    (hbdiff : |b' - b| ≤ B * bound * epsilon)
    (hc' : |c'| ≤ 4) (hcdiff : |c' - c| ≤ 3 * epsilon)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (he : 0 ≤ epsilon) (hbound : 0 ≤ bound) :
    |a' * b' * c' - a * b * c| ≤ (8 * A + 4 * B + 6) * bound * epsilon := by
  calc
    _ = |(a' - a) * b' * c' + a * (b' - b) * c' + a * b * (c' - c)| := by congr 1; ring
    _ ≤ |(a' - a) * b' * c'| + |a * (b' - b) * c'| + |a * b * (c' - c)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (A * epsilon) * (2 * bound) * 4 + 1 * (B * bound * epsilon) * 4 +
        1 * (2 * bound) * (3 * epsilon) := by
      simp only [abs_mul]
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul (mul_le_mul ha' hb' (abs_nonneg _) (by positivity)) hc'
            (abs_nonneg _) (by positivity)
        · exact mul_le_mul (mul_le_mul ha hbdiff (abs_nonneg _) (by norm_num)) hc'
            (abs_nonneg _) (by positivity)
      · exact mul_le_mul (mul_le_mul ha hb (abs_nonneg _) (by norm_num)) hcdiff
          (abs_nonneg _) (by positivity)
    _ = _ := by ring

def fixedErrorConstant (security : ℕ) : ℝ :=
  (Parameters.modulus security : ℝ)^2 *
    (8 * primaryErrorConstant security + 4 * weightedErrorConstant security + 6)

/-- A true simultaneous entry estimate for the current four-endpoint
signed physical mass, with its one retained scalar and two fixed roots. -/
theorem fixedMass_error (security bits : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : FirstHistogram.Scalar security) (score : ℕ → ℚ) (bound : ℝ) (hb : 0 ≤ bound)
    (hscore : ∀ color : FirstHistogram.Palette security, |(score color.val : ℝ)| ≤ bound)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (word : Fin 4 → FirstHistogram.Palette security) :
    |(fixedMass security bits compensatorRoot attachmentRoot scalar.val score (fun index => (word index).val) : ℝ) -
      PairedReferenceEnergy.pairedMassAt security compensatorRoot attachmentRoot scalar
        (fun color => (score color.val : ℝ)) word| ≤
          fixedErrorConstant security * bound * (1 / (2 : ℝ)^bits) := by
  let epsilon : ℝ := 1 / (2 : ℝ)^bits
  let A := primaryErrorConstant security
  let B := weightedErrorConstant security
  have he : 0 ≤ epsilon := by positivity
  have he1 : epsilon ≤ 1 := by
    have ht : (1 : ℝ) ≤ (2 : ℝ)^bits := one_le_pow₀ (by norm_num)
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < 2^bits)).mpr (by simpa using ht)
  have hA : 0 ≤ A := by dsimp [A, primaryErrorConstant]; positivity
  have hB : 0 ≤ B := by dsimp [B, weightedErrorConstant, primaryErrorConstant]; positivity
  rw [fixedMass_cast, actual_fixedMass_formula, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _primaryColor : FirstHistogram.Palette security,
        ∑ _centerColor : FirstHistogram.Palette security, (8 * A + 4 * B + 6) * bound * epsilon := by
      apply Finset.sum_le_sum
      intro primaryColor _
      rw [← Finset.sum_sub_distrib]
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro centerColor _
      let c' : ℝ := LocalPairProgram.current security bits primaryColor.val scalar.val (word 1).val (word 2).val
      let c := (pairAt security primaryColor scalar).weight (word 1, word 2)
      have hc : |c' - c| ≤ 3 * epsilon :=
        (LocalPairProgram.current_error security bits primaryColor (word 1) (word 2) scalar).trans_eq (by dsimp [epsilon]; ring)
      have hc' : |c'| ≤ 4 := by
        have hctrue : |c| ≤ 1 := by
          rw [abs_of_nonneg ((pairAt security primaryColor scalar).nonneg _)]
          exact (pairAt security primaryColor scalar).atom_le_one _
        have h := (abs_add_le (c' - c) c).trans (add_le_add hc hctrue)
        have hsplit : c' - c + c = c' := by ring
        rw [hsplit] at h
        linarith
      have hp : |(approximatePrimaryLaw security bits).weight primaryColor - (primaryLaw security).weight primaryColor| ≤ A * epsilon := by
        simpa only [approximatePrimaryLaw, primaryLaw, A, primaryErrorConstant, epsilon] using
          primary_error security bits primaryColor hprecision hbudget
      have hterm := product_error ((primaryLaw security).weight primaryColor)
        ((approximatePrimaryLaw security bits).weight primaryColor)
        (actualWeightedScore security (fun color => (score color.val : ℝ)) primaryColor centerColor)
        (weightedScore security bits score primaryColor.val centerColor.val : ℝ) c c' A B epsilon bound
        (by rw [abs_of_nonneg ((primaryLaw security).nonneg _)]; exact (primaryLaw security).atom_le_one _)
        hp (actualWeightedScore_bound security _ bound hb hscore _ _) (weightedScore_bound security bits score bound hb hscore _ _)
        (weightedScore_error security bits score bound hb hscore hprecision hbudget _ _) hc' hc hA hB he hb
      rw [← sub_mul, abs_mul]
      exact (mul_le_mul hterm (actualRest_bound security compensatorRoot attachmentRoot scalar centerColor word)
        (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul];
                dsimp [fixedErrorConstant, A, B, epsilon]; ring

theorem actual_fixedMass_bound (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : FirstHistogram.Scalar security) (score : FirstHistogram.Palette security → ℝ)
    (bound : ℝ) (hb : 0 ≤ bound) (hscore : ∀ color, |score color| ≤ bound)
    (word : Fin 4 → FirstHistogram.Palette security) :
    |PairedReferenceEnergy.pairedMassAt security compensatorRoot attachmentRoot scalar score word| ≤
      (2 * (Parameters.modulus security : ℝ)^2) * bound := by
  rw [actual_fixedMass_formula]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _primaryColor : FirstHistogram.Palette security,
        ∑ _centerColor : FirstHistogram.Palette security, 2 * bound := by
      apply Finset.sum_le_sum
      intro primaryColor _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro centerColor _
      simp only [abs_mul, abs_of_nonneg ((primaryLaw security).nonneg _),
        abs_of_nonneg ((pairAt security primaryColor scalar).nonneg _)]
      have h := mul_le_mul
        (mul_le_mul (mul_le_mul ((primaryLaw security).atom_le_one primaryColor)
          (actualWeightedScore_bound security score bound hb hscore primaryColor centerColor)
          (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))
          ((pairAt security primaryColor scalar).atom_le_one (word 1, word 2))
          ((pairAt security primaryColor scalar).nonneg (word 1, word 2))
          (by positivity : (0 : ℝ) ≤ 1 * (2 * bound)))
        (actualRest_bound security compensatorRoot attachmentRoot scalar centerColor word)
        (abs_nonneg _) (by positivity : (0 : ℝ) ≤ 1 * (2 * bound) * 1)
      simpa only [one_mul, mul_one] using h
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem primaryMass_cast (security bits : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (score : ℕ → ℚ) (word : Fin 4 → FirstHistogram.Palette security) :
    (primaryMass security bits compensatorRoot attachmentRoot score (fun index => (word index).val) : ℝ) =
      ∑ scalar : FirstHistogram.Scalar security,
        (windowApproxLaw (WindowGaussianSampler.squaredWidth security)
          (Parameters.sourceCutoff security - 1) bits).weight scalar *
          (fixedMass security bits compensatorRoot attachmentRoot scalar.val score
            (fun index => (word index).val) : ℝ) := by
  have hcutoff : (security + 2)^2 - 1 = Parameters.sourceCutoff security - 1 := by
    simp only [Parameters.sourceCutoff, Parameters.base]
  unfold primaryMass
  rw [hcutoff]
  simp only [scalarAverage, Rat.cast_sum, Rat.cast_mul, gaussianWeight_eq]
  rfl

theorem primaryMassAt_apply (security : ℕ) (roots : RootTaggedSelected.RootPair security)
    (score : FirstHistogram.Palette security → ℝ) (word : Fin 4 → FirstHistogram.Palette security) :
    RootMassColumns.primaryMassAt security roots score word =
      ∑ scalar : FirstHistogram.Scalar security, (scalarLaw security).weight scalar *
        PairedReferenceEnergy.pairedMassAt security roots.1.val roots.2.val scalar score word := by
  simp only [RootMassColumns.primaryMassAt, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, PairedReferenceEnergy.pairedMassLinear_apply]

theorem primaryMassAt_bound (security : ℕ) (roots : RootTaggedSelected.RootPair security)
    (score : FirstHistogram.Palette security → ℝ) (bound : ℝ) (hb : 0 ≤ bound)
    (hscore : ∀ color, |score color| ≤ bound) (word : Fin 4 → FirstHistogram.Palette security) :
    |RootMassColumns.primaryMassAt security roots score word| ≤
      (2 * (Parameters.modulus security : ℝ)^2) * bound := by
  rw [primaryMassAt_apply]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ scalar, (scalarLaw security).weight scalar * ((2 * (Parameters.modulus security : ℝ)^2) * bound) := by
      apply Finset.sum_le_sum
      intro scalar _
      rw [abs_mul, abs_of_nonneg ((scalarLaw security).nonneg scalar)]
      exact mul_le_mul_of_nonneg_left (actual_fixedMass_bound security _ _ scalar score bound hb hscore word)
        ((scalarLaw security).nonneg scalar)
    _ = _ := by rw [← Finset.sum_mul, (scalarLaw security).sum_one, one_mul]

def primaryMassErrorConstant (security : ℕ) : ℝ :=
  fixedErrorConstant security + 2 * (Parameters.modulus security : ℝ)^2

theorem primaryMass_error (security bits : ℕ) (roots : RootTaggedSelected.RootPair security)
    (score : ℕ → ℚ) (bound : ℝ) (hb : 0 ≤ bound)
    (hscore : ∀ color : FirstHistogram.Palette security, |(score color.val : ℝ)| ≤ bound)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (word : Fin 4 → FirstHistogram.Palette security) :
    |(primaryMass security bits roots.1.val roots.2.val score (fun index => (word index).val) : ℝ) -
      RootMassColumns.primaryMassAt security roots (fun color => (score color.val : ℝ)) word| ≤
        primaryMassErrorConstant security * bound * (1 / (2 : ℝ)^bits) := by
  let approximate := windowApproxLaw (WindowGaussianSampler.squaredWidth security)
    (Parameters.sourceCutoff security - 1) bits
  let test := fun scalar : FirstHistogram.Scalar security =>
    PairedReferenceEnergy.pairedMassAt security roots.1.val roots.2.val scalar
      (fun color => (score color.val : ℝ)) word
  let approximateTest := fun scalar : FirstHistogram.Scalar security =>
    (fixedMass security bits roots.1.val roots.2.val scalar.val score (fun index => (word index).val) : ℝ)
  have htest (scalar : FirstHistogram.Scalar security) :
      |test scalar| ≤ (2 * (Parameters.modulus security : ℝ)^2) * bound :=
    actual_fixedMass_bound security _ _ scalar _ bound hb hscore word
  have hl1 : (∑ scalar, |approximate.weight scalar - (scalarLaw security).weight scalar|) ≤ 1 / (2 : ℝ)^bits :=
    windowApproxLaw_l1 _ _ _ _ (WindowGaussianSampler.squaredWidth_positive security)
      (WindowGaussianSampler.squaredWidth_real security).symm
  have hsource : |approximate.expectation test - (scalarLaw security).expectation test| ≤
      (1 / (2 : ℝ)^bits) * ((2 * (Parameters.modulus security : ℝ)^2) * bound) := by
    unfold FiniteDist.expectation
    rw [← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ scalar, |approximate.weight scalar - (scalarLaw security).weight scalar| *
          ((2 * (Parameters.modulus security : ℝ)^2) * bound) := by
        apply Finset.sum_le_sum
        intro scalar _
        rw [← sub_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (htest scalar) (abs_nonneg _)
      _ = _ := Finset.sum_mul .. |>.symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hl1 (by positivity)
  have hentries : |approximate.expectation approximateTest - approximate.expectation test| ≤
      fixedErrorConstant security * bound * (1 / (2 : ℝ)^bits) := by
    unfold FiniteDist.expectation
    rw [← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ scalar, approximate.weight scalar *
          (fixedErrorConstant security * bound * (1 / (2 : ℝ)^bits)) := by
        apply Finset.sum_le_sum
        intro scalar _
        rw [← mul_sub, abs_mul, abs_of_nonneg (approximate.nonneg scalar)]
        exact mul_le_mul_of_nonneg_left
          (fixedMass_error security bits _ _ scalar score bound hb hscore hprecision hbudget word)
          (approximate.nonneg scalar)
      _ = _ := by rw [← Finset.sum_mul, approximate.sum_one, one_mul]
  rw [primaryMass_cast, primaryMassAt_apply]
  change |approximate.expectation approximateTest - (scalarLaw security).expectation test| ≤ _
  calc
    _ ≤ |approximate.expectation approximateTest - approximate.expectation test| +
        |approximate.expectation test - (scalarLaw security).expectation test| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add hentries hsource
    _ = _ := by unfold primaryMassErrorConstant; ring

end
end CurrentAFT.RationalRootMassProgram
