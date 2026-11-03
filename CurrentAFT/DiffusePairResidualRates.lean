import CurrentAFT.DiffusePairResidual

/-! Explicit decay of the complete current diffuse-pair residual. -/

namespace CurrentAFT.DiffusePairResidualRates

open AFT AFT.TrimmedSlice AFT.SafePair AFT.SafeConvolution
  DiffuseProfiles ProposalPrimary FirstResponse ActualControls PairSmoothing
  DiffusePair DiffusePairBounds DiffusePairResidual
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
  Parameters.safeMargin ProposalPrimary.primaryLaw ProposalPrimary.centerLaw ActualControls.bodyReference
  DiffusePair.pairProfile DiffusePair.safePairProfile DiffusePair.liftedPairProfile
  DiffusePair.rootPairLaw DiffusePair.rootPairShift
  DiffusePairResidual.originalProfile DiffusePairResidual.restrictedProfile DiffusePairResidual.seedProfile
  DiffusePairResidual.residualProfile DiffusePairResidual.rootResiduePairLaw

def pullbackPair (modulus : ℕ) [NeZero modulus] (profile : ZMod modulus × ZMod modulus → ℝ)
    (first second : Fin modulus) : ℝ :=
  profile ((ZMod.finEquiv modulus) first, (ZMod.finEquiv modulus) second)

theorem pullbackPair_add (modulus : ℕ) [NeZero modulus]
    (first second : ZMod modulus × ZMod modulus → ℝ) (left right : Fin modulus) :
    pullbackPair modulus (first + second) left right =
      pullbackPair modulus first left right + pullbackPair modulus second left right := rfl

theorem pullbackPair_countingL2 (modulus : ℕ) [NeZero modulus]
    (profile : ZMod modulus × ZMod modulus → ℝ) :
    pairCountingL2 (pullbackPair modulus profile) = countingL2 profile := by
  unfold pairCountingL2 countingL2
  congr 1
  exact ((ZMod.finEquiv modulus).toEquiv.prodCongr (ZMod.finEquiv modulus).toEquiv).sum_comp
    (fun color => profile color ^ 2)

theorem pullbackPair_canonical (modulus : ℕ) [NeZero modulus]
    (profile : ZMod modulus × ZMod modulus → ℝ) (hcanonical : PairCanonical profile) :
    (∀ first, ∑ second, pullbackPair modulus profile first second = 0) ∧
    (∀ second, ∑ first, pullbackPair modulus profile first second = 0) := by
  constructor
  · intro first
    exact ((ZMod.finEquiv modulus).toEquiv.sum_comp
      (fun second => profile ((ZMod.finEquiv modulus) first, second))).trans
        (hcanonical.1 ((ZMod.finEquiv modulus) first))
  · intro second
    exact ((ZMod.finEquiv modulus).toEquiv.sum_comp
      (fun first => profile (first, (ZMod.finEquiv modulus) second))).trans
        (hcanonical.2 ((ZMod.finEquiv modulus) second))

theorem uniformCanonical_canonical {Group : Type*} [Fintype Group] [AddCommGroup Group]
    (profile : Group × Group → ℝ) : PairCanonical (uniformCanonical profile) := by
  have hmass : (∑ _ : Group, 1 / (Fintype.card Group : ℝ)) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_one_div_cancel (by exact_mod_cast Fintype.card_ne_zero)
  exact ⟨canonicalPair_first _ _ hmass, canonicalPair_second _ _ hmass⟩

theorem canonicalPair_symmetric {Color : Type*} [Fintype Color]
    (reference : Color → ℝ) (profile : Color → Color → ℝ)
    (hsymmetric : ∀ first second, profile first second = profile second first) (first second : Color) :
    canonicalPair reference profile first second = canonicalPair reference profile second first := by
  have htranspose : (fun first second => profile second first) = profile := by
    funext first second
    exact hsymmetric second first
  rw [canonicalPair_transpose, htranspose]

theorem smoothProfile_prod_symmetric {Seed Group : Type*} [Fintype Seed] [Sub Group]
    (law : FiniteDist Seed) (shift : Seed → Group) (profile : Group × Group → ℝ)
    (hsymmetric : ∀ first second, profile (first, second) = profile (second, first)) (first second : Group) :
    smoothProfile (law.prod law) (fun seed => (shift seed.1, shift seed.2)) profile (first, second) =
      smoothProfile (law.prod law) (fun seed => (shift seed.1, shift seed.2)) profile (second, first) := by
  simp only [smoothProfile, Fintype.sum_prod_type, FiniteDist.prod_weight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro one _
  apply Finset.sum_congr rfl
  intro two _
  change law.weight two * law.weight one * profile (first - shift two, second - shift one) =
    law.weight one * law.weight two * profile (second - shift one, first - shift two)
  rw [hsymmetric]
  ring

theorem mapped_convolution_prod_symmetric {Seed Group : Type*} [Fintype Seed] [Fintype Group] [AddCommGroup Group]
    (law : FiniteDist Seed) (shift : Seed → Group) (profile : Group × Group → ℝ)
    (hsymmetric : ∀ first second, profile (first, second) = profile (second, first)) (first second : Group) :
    convolution ((law.prod law).map (fun seed => (shift seed.1, shift seed.2))).weight profile (first, second) =
      convolution ((law.prod law).map (fun seed => (shift seed.1, shift seed.2))).weight profile (second, first) := by
  have heq (color : Group × Group) :
      convolution ((law.prod law).map (fun seed => (shift seed.1, shift seed.2))).weight profile color =
        smoothProfile (law.prod law) (fun seed => (shift seed.1, shift seed.2)) profile color := by
    change ((law.prod law).map (fun seed => (shift seed.1, shift seed.2))).expectation
      (fun vector => profile (color - vector)) = _
    rw [FiniteDist.expectation_map]
    rfl
  rw [heq, heq]
  exact smoothProfile_prod_symmetric law shift profile hsymmetric first second

theorem reference_budget_decay (security : ℕ) :
    128 * (Parameters.safeMargin security : ℝ) / Parameters.modulus security ≤
      384 / (Parameters.base security : ℝ) ^ 62 := by
  have hb := FirstResponse.base_pos security
  have hql : (Parameters.base security : ℝ) ^ 64 ≤ Parameters.modulus security := by
    have h := (Parameters.modulus_bounds security).1
    have hpow : 0 < Parameters.base security ^ 64 := pow_pos (Parameters.base_pos security) _
    exact_mod_cast (show Parameters.base security ^ 64 ≤ Parameters.modulus security by omega)
  calc
    _ ≤ 128 * (Parameters.safeMargin security : ℝ) / (Parameters.base security : ℝ) ^ 64 :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hb _) hql
    _ = _ := by
      simp only [Parameters.safeMargin, Parameters.sourceCutoff, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
      field_simp
      ring

theorem edge_budget_decay (security : ℕ) :
    16 * (Parameters.safeMargin security : ℝ) / Parameters.anchorWidth security =
      48 / (Parameters.base security : ℝ) ^ 46 := by
  have hb := FirstResponse.base_pos security
  simp only [Parameters.safeMargin, Parameters.sourceCutoff, anchorWidth_eq,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  field_simp
  ring

theorem reference_error_norm_decay (security : ℕ) (scalar : ℤ)
    (hscalar : |scalar| ≤ Parameters.sourceCutoff security) :
    (Parameters.modulus security : ℝ) *
      countingL2 (seedProfile security scalar - uniformCanonical (restrictedProfile security scalar)) ≤
        20 / (Parameters.base security : ℝ) ^ 31 := by
  have hb := FirstResponse.base_pos security
  apply le_of_sq_le_sq _ (by positivity : (0 : ℝ) ≤ 20 / (Parameters.base security : ℝ) ^ 31)
  calc
    _ ≤ 128 * (Parameters.safeMargin security : ℝ) / Parameters.modulus security :=
      reference_error_scaled_square security scalar hscalar
    _ ≤ 384 / (Parameters.base security : ℝ) ^ 62 := reference_budget_decay security
    _ ≤ 400 / (Parameters.base security : ℝ) ^ 62 :=
      div_le_div_of_nonneg_right (by norm_num) (pow_nonneg hb.le _)
    _ = _ := by ring

theorem edge_error_norm_decay (security : ℕ) (scalar : ℤ)
    (hscalar : |scalar| ≤ Parameters.sourceCutoff security) :
    (Parameters.modulus security : ℝ) *
      countingL2 (restrictedProfile security scalar - originalProfile security scalar) ≤
        7 / (Parameters.base security : ℝ) ^ 23 := by
  have hb := FirstResponse.base_pos security
  apply le_of_sq_le_sq _ (by positivity : (0 : ℝ) ≤ 7 / (Parameters.base security : ℝ) ^ 23)
  calc
    _ ≤ 16 * (Parameters.safeMargin security : ℝ) / Parameters.anchorWidth security :=
      edge_error_scaled_square security scalar hscalar
    _ = 48 / (Parameters.base security : ℝ) ^ 46 := edge_budget_decay security
    _ ≤ 49 / (Parameters.base security : ℝ) ^ 46 :=
      div_le_div_of_nonneg_right (by norm_num) (pow_nonneg hb.le _)
    _ = _ := by ring

theorem smoothing_error_norm_decay (security : ℕ) (scalar : ℤ)
    (hscalar : |scalar| ≤ Parameters.sourceCutoff security) :
    (Parameters.modulus security : ℝ) *
      countingL2 (convolution (rootResiduePairLaw security).weight (restrictedProfile security scalar) -
        restrictedProfile security scalar) ≤
        3000 / (Parameters.base security : ℝ) ^ 15 := by
  have hb := FirstResponse.base_pos security
  apply le_of_sq_le_sq _ (by positivity : (0 : ℝ) ≤ 3000 / (Parameters.base security : ℝ) ^ 15)
  rw [mul_pow, countingL2, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  rw [root_convolution, restrictedProfile_eq]
  calc
    _ ≤ 8388896 / (Parameters.base security : ℝ) ^ 30 :=
      liftedPairProfile_scaled_smoothing_decay security scalar hscalar
    _ ≤ 9000000 / (Parameters.base security : ℝ) ^ 30 :=
      div_le_div_of_nonneg_right (by norm_num) (pow_nonneg hb.le _)
    _ = _ := by ring

theorem residualProfile_scaled_norm_decay (security : ℕ) (scalar : ℤ)
    (hscalar : |scalar| ≤ Parameters.sourceCutoff security) :
    (Parameters.modulus security : ℝ) * countingL2 (residualProfile security scalar) ≤
      3027 / (Parameters.base security : ℝ) ^ 15 := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  calc
    _ ≤ (Parameters.modulus security : ℝ) *
        (countingL2 (seedProfile security scalar - uniformCanonical (restrictedProfile security scalar)) +
          countingL2 (convolution (rootResiduePairLaw security).weight (restrictedProfile security scalar) - restrictedProfile security scalar) +
          countingL2 (restrictedProfile security scalar - originalProfile security scalar)) :=
      mul_le_mul_of_nonneg_left (residualProfile_counting_bound security scalar) (Nat.cast_nonneg _)
    _ = (Parameters.modulus security : ℝ) *
          countingL2 (seedProfile security scalar - uniformCanonical (restrictedProfile security scalar)) +
        (Parameters.modulus security : ℝ) *
          countingL2 (convolution (rootResiduePairLaw security).weight (restrictedProfile security scalar) - restrictedProfile security scalar) +
        (Parameters.modulus security : ℝ) * countingL2 (restrictedProfile security scalar - originalProfile security scalar) := by ring
    _ ≤ 20 / (Parameters.base security : ℝ) ^ 31 + 3000 / (Parameters.base security : ℝ) ^ 15 +
        7 / (Parameters.base security : ℝ) ^ 23 :=
      add_le_add (add_le_add (reference_error_norm_decay security scalar hscalar)
        (smoothing_error_norm_decay security scalar hscalar)) (edge_error_norm_decay security scalar hscalar)
    _ ≤ 20 / (Parameters.base security : ℝ) ^ 15 + 3000 / (Parameters.base security : ℝ) ^ 15 +
        7 / (Parameters.base security : ℝ) ^ 15 := by
      apply add_le_add
      · exact add_le_add (div_le_div_of_nonneg_left (by norm_num) (pow_pos hb _)
          (pow_le_pow_right₀ hb1 (by omega))) le_rfl
      · exact div_le_div_of_nonneg_left (by norm_num) (pow_pos hb _)
          (pow_le_pow_right₀ hb1 (by omega))
    _ = _ := by ring

def finiteResidual (security : ℕ) (scalar : ℤ) (first second : ActualControls.Palette security) : ℝ :=
  pullbackPair (Parameters.modulus security) (residualProfile security scalar) first second

theorem finiteResidual_countingL2 (security : ℕ) (scalar : ℤ) :
    pairCountingL2 (finiteResidual security scalar) = countingL2 (residualProfile security scalar) := by
  exact pullbackPair_countingL2 _ _

theorem residualProfile_canonical (security : ℕ) (scalar : ℤ) :
    PairCanonical (residualProfile security scalar) := by
  have hseed : PairCanonical (seedProfile security scalar) := by
    constructor
    · intro first
      unfold seedProfile
      change (∑ second, PairReindex.liftPair (ZMod.finEquiv (Parameters.modulus security)).toEquiv
        (safePairProfile security scalar) first second) = 0
      rw [PairReindex.liftPair_second_sum]
      exact (safePairProfile_canonical security scalar).1 _
    · intro second
      unfold seedProfile
      change (∑ first, PairReindex.liftPair (ZMod.finEquiv (Parameters.modulus security)).toEquiv
        (safePairProfile security scalar) first second) = 0
      rw [PairReindex.liftPair_first_sum]
      exact (safePairProfile_canonical security scalar).2 _
  rw [residualProfile]
  exact (uniformCanonical_canonical _).sub (convolution_pairCanonical _ _ hseed)

theorem finiteResidual_canonical (security : ℕ) (scalar : ℤ) :
    (∀ first, ∑ second, finiteResidual security scalar first second = 0) ∧
    (∀ second, ∑ first, finiteResidual security scalar first second = 0) :=
  pullbackPair_canonical _ _ (residualProfile_canonical security scalar)

theorem coreSeed_symmetric {Color : Type*} [Fintype Color] [DecidableEq Color]
    (core : Finset Color) (profile : Color → Color → ℝ)
    (hsymmetric : ∀ first second, profile first second = profile second first) (first second : Color) :
    coreSeed core profile first second = coreSeed core profile second first := by
  have hrestrict : ∀ first second, restrictPair core profile first second = restrictPair core profile second first := by
    intro first second
    by_cases hfirst : first ∈ core <;> by_cases hsecond : second ∈ core <;>
      simp only [restrictPair, hfirst, hsecond, and_self, and_true, and_false, if_true, if_false, hsymmetric]
  exact canonicalPair_symmetric _ _ hrestrict first second

theorem finite_residual_symmetric {Seed : Type*} [Fintype Seed]
    (modulus : ℕ) [NeZero modulus] (core : Finset (Fin modulus)) (profile : Fin modulus → Fin modulus → ℝ)
    (law : FiniteDist Seed) (shift : Seed → ZMod modulus)
    (hsymmetric : ∀ first second, profile first second = profile second first)
    (first second : ZMod modulus) :
    (uniformCanonical (fun color : ZMod modulus × ZMod modulus =>
        PairReindex.liftPair (ZMod.finEquiv modulus).toEquiv profile color.1 color.2) -
      convolution ((law.prod law).map (fun seed => (shift seed.1, shift seed.2))).weight
        (fun color : ZMod modulus × ZMod modulus =>
          PairReindex.liftPair (ZMod.finEquiv modulus).toEquiv (coreSeed core profile) color.1 color.2)) (first, second) =
    (uniformCanonical (fun color : ZMod modulus × ZMod modulus =>
        PairReindex.liftPair (ZMod.finEquiv modulus).toEquiv profile color.1 color.2) -
      convolution ((law.prod law).map (fun seed => (shift seed.1, shift seed.2))).weight
        (fun color : ZMod modulus × ZMod modulus =>
          PairReindex.liftPair (ZMod.finEquiv modulus).toEquiv (coreSeed core profile) color.1 color.2)) (second, first) := by
  have horiginal := PairReindex.liftPair_symmetric (ZMod.finEquiv modulus).toEquiv profile hsymmetric
  have hseed := PairReindex.liftPair_symmetric (ZMod.finEquiv modulus).toEquiv (coreSeed core profile)
    (coreSeed_symmetric core profile hsymmetric)
  simp only [Pi.sub_apply, uniformCanonical_apply]
  rw [canonicalPair_symmetric _ _ horiginal]
  rw [mapped_convolution_prod_symmetric law shift _ hseed]

theorem residualProfile_symmetric (security : ℕ) (scalar : ℤ)
    (first second : ZMod (Parameters.modulus security)) :
    residualProfile security scalar (first, second) = residualProfile security scalar (second, first) := by
  unfold residualProfile originalProfile seedProfile rootResiduePairLaw rootPairLaw rootPairShift safePairProfile
  exact finite_residual_symmetric (Parameters.modulus security) (safeCore security) (pairProfile security scalar)
    (actualSeedLaw security) (fun seed => (actualBlur security seed : ZMod (Parameters.modulus security)))
    (pairProfile_symmetric security scalar) first second

theorem finiteResidual_symmetric (security : ℕ) (scalar : ℤ) (first second : ActualControls.Palette security) :
    finiteResidual security scalar first second = finiteResidual security scalar second first :=
  residualProfile_symmetric security scalar _ _

theorem finiteResidual_primary_energy (security : ℕ) (scalar : ℤ) :
    BlockDensity.pairEnergy (primaryLaw security).weight (primaryLaw security).weight (finiteResidual security scalar) ≤
      4 * (Parameters.modulus security : ℝ) ^ 2 *
        (countingL2 (residualProfile security scalar)) ^ 2 := by
  have hq := FirstResponse.modulus_pos security
  have hden (first second : ActualControls.Palette security) :
      1 / (4 * (Parameters.modulus security : ℝ) ^ 2) ≤
        (primaryLaw security).weight first * (primaryLaw security).weight second := by
    have hfirst : 1 / (2 * (Parameters.modulus security : ℝ)) ≤ (primaryLaw security).weight first := by
      simpa only [primaryLaw] using primaryProfile_atom_lower security first
    have hsecond : 1 / (2 * (Parameters.modulus security : ℝ)) ≤ (primaryLaw security).weight second := by
      simpa only [primaryLaw] using primaryProfile_atom_lower security second
    have h := mul_le_mul hfirst hsecond
      (by positivity : (0 : ℝ) ≤ 1 / (2 * (Parameters.modulus security : ℝ)))
      (primaryReference_positive security first).le
    convert h using 1; ring
  have hsquare : (countingL2 (residualProfile security scalar)) ^ 2 =
      ∑ first, ∑ second, finiteResidual security scalar first second ^ 2 := by
    rw [← finiteResidual_countingL2, pairCountingL2, countingL2,
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Fintype.sum_prod_type]
  rw [hsquare]
  unfold BlockDensity.pairEnergy
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro first _
  apply Finset.sum_le_sum
  intro second _
  calc
    _ ≤ finiteResidual security scalar first second ^ 2 / (1 / (4 * (Parameters.modulus security : ℝ) ^ 2)) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (hden first second)
    _ = _ := by field_simp [hq.ne']

theorem finiteResidual_primary_norm_decay (security : ℕ) (scalar : ℤ)
    (hscalar : |scalar| ≤ Parameters.sourceCutoff security) :
    Real.sqrt (BlockDensity.pairEnergy (primaryLaw security).weight (primaryLaw security).weight (finiteResidual security scalar)) ≤
      6054 / (Parameters.base security : ℝ) ^ 15 := by
  have hq := FirstResponse.modulus_pos security
  have hstep : Real.sqrt (BlockDensity.pairEnergy (primaryLaw security).weight (primaryLaw security).weight (finiteResidual security scalar)) ≤
      2 * (Parameters.modulus security : ℝ) * countingL2 (residualProfile security scalar) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨mul_nonneg (by positivity) (countingL2_nonneg _), ?_⟩
    convert finiteResidual_primary_energy security scalar using 1; ring
  calc
    _ ≤ 2 * (Parameters.modulus security : ℝ) * countingL2 (residualProfile security scalar) := hstep
    _ = 2 * ((Parameters.modulus security : ℝ) * countingL2 (residualProfile security scalar)) := by ring
    _ ≤ 2 * (3027 / (Parameters.base security : ℝ) ^ 15) :=
      mul_le_mul_of_nonneg_left (residualProfile_scaled_norm_decay security scalar hscalar) (by norm_num)
    _ = _ := by ring

end

end CurrentAFT.DiffusePairResidualRates
