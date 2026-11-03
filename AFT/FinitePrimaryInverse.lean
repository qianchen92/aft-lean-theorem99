import AFT.Anchor

/-!
# A finite primary inverse in the actual profile activity

The activity below is the one-coordinate mixed activity of signed primary
profiles. A strict contraction gives an inverse by finite-dimensional
injectivity, so no unproved completeness or norm-equivalence assertion is
needed. The eventual concrete operator is obtained from the displayed
rank-one inverse and interval-anchor translation estimates.
-/

namespace AFT

open scoped BigOperators

section ProfileActivity

variable {ι : Type*} [Fintype ι]

/-- The one-primary-coordinate activity, with `rate = 1 / sqrt(pool)`. -/
noncomputable def primaryActivity (rate : ℝ) (primary profile : ι → ℝ) : ℝ :=
  rate * Real.sqrt (profileSquareNorm primary profile) +
    rate ^ 2 * ‖fun color => profile color / primary color‖

theorem primaryActivity_nonneg (rate : ℝ) (primary profile : ι → ℝ) (hrate : 0 ≤ rate) :
    0 ≤ primaryActivity rate primary profile := by
  unfold primaryActivity
  positivity

@[simp] theorem primaryActivity_neg (rate : ℝ) (primary profile : ι → ℝ) :
    primaryActivity rate primary (-profile) = primaryActivity rate primary profile := by
  have hs : profileSquareNorm primary (-profile) = profileSquareNorm primary profile := by
    simp [profileSquareNorm]
  have hd : (fun color => (-profile) color / primary color) =
      -(fun color => profile color / primary color) := by
    funext color
    simp only [Pi.neg_apply, neg_div]
  simp only [primaryActivity, hs, hd, norm_neg]

/-- Weighted finite Minkowski, with the cross term checked by finite
Cauchy--Schwarz. -/
theorem profileSquareNorm_sqrt_add_le (primary first second : ι → ℝ)
    (hp : ∀ color, 0 < primary color) :
    Real.sqrt (profileSquareNorm primary (first + second)) ≤
      Real.sqrt (profileSquareNorm primary first) + Real.sqrt (profileSquareNorm primary second) := by
  have hnfirst := profileSquareNorm_nonneg primary first (fun color => le_of_lt (hp color))
  have hnsecond := profileSquareNorm_nonneg primary second (fun color => le_of_lt (hp color))
  have hc : (∑ color, first color * second color / primary color) ^ 2 ≤
      profileSquareNorm primary first * profileSquareNorm primary second := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    · intro color _
      exact div_nonneg (sq_nonneg _) (le_of_lt (hp color))
    · intro color _
      exact div_nonneg (sq_nonneg _) (le_of_lt (hp color))
    · intro color _
      ring
  have hcross : (∑ color, first color * second color / primary color) ≤
      Real.sqrt (profileSquareNorm primary first) * Real.sqrt (profileSquareNorm primary second) := by
    simpa only [Real.sqrt_mul hnfirst] using Real.le_sqrt_of_sq_le hc
  have hexpand : profileSquareNorm primary (first + second) =
      profileSquareNorm primary first + profileSquareNorm primary second +
        2 * ∑ color, first color * second color / primary color := by
    simp only [profileSquareNorm, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro color _
    ring
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · rw [hexpand]
    nlinarith [Real.sq_sqrt hnfirst, Real.sq_sqrt hnsecond]

theorem primaryActivity_add_le (rate : ℝ) (primary first second : ι → ℝ)
    (hrate : 0 ≤ rate) (hp : ∀ color, 0 < primary color) :
    primaryActivity rate primary (first + second) ≤
      primaryActivity rate primary first + primaryActivity rate primary second := by
  have hnorm : ‖fun color => (first + second) color / primary color‖ ≤
      ‖fun color => first color / primary color‖ + ‖fun color => second color / primary color‖ := by
    have heq : (fun color => (first + second) color / primary color) =
        (fun color => first color / primary color) + (fun color => second color / primary color) := by
      funext color
      simp [add_div]
    rw [heq]
    exact norm_add_le _ _
  have htwo := mul_le_mul_of_nonneg_left
    (profileSquareNorm_sqrt_add_le primary first second hp) hrate
  have hsup := mul_le_mul_of_nonneg_left hnorm (sq_nonneg rate)
  unfold primaryActivity
  nlinarith only [htwo, hsup]

theorem primaryActivity_eq_zero (rate : ℝ) (primary profile : ι → ℝ)
    (hrate : 0 < rate) (hp : ∀ color, 0 < primary color)
    (hzero : primaryActivity rate primary profile = 0) : profile = 0 := by
  have hsup : ‖fun color => profile color / primary color‖ = 0 := by
    have hsqrt := Real.sqrt_nonneg (profileSquareNorm primary profile)
    have hn := norm_nonneg (fun color => profile color / primary color)
    have hsquare : 0 < rate ^ 2 := sq_pos_of_pos hrate
    unfold primaryActivity at hzero
    nlinarith
  have hd := norm_eq_zero.mp hsup
  funext color
  have he := congrFun hd color
  exact (div_eq_zero_iff.mp he).resolve_right (ne_of_gt (hp color))

@[simp] theorem primaryActivity_zero (rate : ℝ) (primary : ι → ℝ) :
    primaryActivity rate primary 0 = 0 := by
  simp [primaryActivity, profileSquareNorm]
  exact Or.inr rfl

/-- Absolute homogeneity of the concrete profile activity. -/
theorem primaryActivity_smul (rate scalar : ℝ) (primary profile : ι → ℝ) :
    primaryActivity rate primary (scalar • profile) = |scalar| * primaryActivity rate primary profile := by
  have hd : (fun color => (scalar • profile) color / primary color) =
      scalar • (fun color => profile color / primary color) := by
    funext color
    simp [mul_div_assoc]
  simp only [primaryActivity, profileSquareNorm_smul, Real.sqrt_mul (sq_nonneg scalar),
    Real.sqrt_sq_eq_abs, hd, norm_smul, Real.norm_eq_abs]
  ring

/-- Finite sums obey the triangle inequality with no palette constant. -/
theorem primaryActivity_sum_le {τ : Type*} (indices : Finset τ) (rate : ℝ)
    (primary : ι → ℝ) (profiles : τ → ι → ℝ)
    (hrate : 0 ≤ rate) (hp : ∀ color, 0 < primary color) :
    primaryActivity rate primary (∑ index ∈ indices, profiles index) ≤
      ∑ index ∈ indices, primaryActivity rate primary (profiles index) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert index indices hnot ih =>
    rw [Finset.sum_insert hnot, Finset.sum_insert hnot]
    exact (primaryActivity_add_le rate primary _ _ hrate hp).trans (add_le_add le_rfl ih)

/-- Combine concrete Hilbert and density-supremum bounds with the extra
fixed-coordinate pool penalty. -/
theorem primaryActivity_bound_of_parts (rate : ℝ) (primary input output : ι → ℝ)
    (hilbertBound rowBound : ℝ) (hrate : 0 ≤ rate)
    (hcoeff : 0 ≤ hilbertBound + rate * rowBound)
    (h2 : Real.sqrt (profileSquareNorm primary output) ≤
      hilbertBound * Real.sqrt (profileSquareNorm primary input))
    (hinf : ‖fun color => output color / primary color‖ ≤
      rowBound * Real.sqrt (profileSquareNorm primary input)) :
    primaryActivity rate primary output ≤
      (hilbertBound + rate * rowBound) * primaryActivity rate primary input := by
  have hnorm := norm_nonneg (fun color => input color / primary color)
  have hleft := mul_le_mul_of_nonneg_left h2 hrate
  have hright := mul_le_mul_of_nonneg_left hinf (sq_nonneg rate)
  have hextra := mul_nonneg hcoeff (mul_nonneg (sq_nonneg rate) hnorm)
  unfold primaryActivity
  nlinarith only [hleft, hright, hextra]

/-- Strict activity contraction proves injectivity of `Id + error`. -/
theorem primaryPerturbation_injective (rate : ℝ) (primary : ι → ℝ)
    (error : Module.End ℝ (ι → ℝ)) (constant : ℝ)
    (hrate : 0 < rate) (hp : ∀ color, 0 < primary color) (hsmall : constant < 1)
    (hcontract : ∀ profile, primaryActivity rate primary (error profile) ≤
      constant * primaryActivity rate primary profile) :
    Function.Injective ((LinearMap.id : Module.End ℝ (ι → ℝ)) + error) := by
  intro first second hequal
  have hz : ((LinearMap.id : Module.End ℝ (ι → ℝ)) + error) (first - second) = 0 := by
    rw [map_sub, hequal, sub_self]
  have he : error (first - second) = -(first - second) := by
    change first - second + error (first - second) = 0 at hz
    exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hz)
  have hc := hcontract (first - second)
  rw [he, primaryActivity_neg] at hc
  have hn := primaryActivity_nonneg rate primary (first - second) (le_of_lt hrate)
  have hact : primaryActivity rate primary (first - second) = 0 := by nlinarith
  exact sub_eq_zero.mp (primaryActivity_eq_zero rate primary (first - second) hrate hp hact)

/-- The finite-dimensional inverse exists because injectivity and
surjectivity coincide. No inverse is supplied as an assumption. -/
noncomputable def primaryPerturbationEquiv (rate : ℝ) (primary : ι → ℝ)
    (error : Module.End ℝ (ι → ℝ)) (constant : ℝ)
    (hrate : 0 < rate) (hp : ∀ color, 0 < primary color) (hsmall : constant < 1)
    (hcontract : ∀ profile, primaryActivity rate primary (error profile) ≤
      constant * primaryActivity rate primary profile) : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) :=
  LinearEquiv.ofBijective (LinearMap.id + error)
    ⟨primaryPerturbation_injective rate primary error constant hrate hp hsmall hcontract,
      LinearMap.surjective_of_injective
        (primaryPerturbation_injective rate primary error constant hrate hp hsmall hcontract)⟩

/-- The constructed inverse is bounded by the explicit geometric factor. -/
theorem primaryPerturbationEquiv_inverse_bound (rate : ℝ) (primary : ι → ℝ)
    (error : Module.End ℝ (ι → ℝ)) (constant : ℝ)
    (hrate : 0 < rate) (hp : ∀ color, 0 < primary color) (hsmall : constant < 1)
    (hcontract : ∀ profile, primaryActivity rate primary (error profile) ≤
      constant * primaryActivity rate primary profile) (target : ι → ℝ) :
    primaryActivity rate primary
      ((primaryPerturbationEquiv rate primary error constant hrate hp hsmall hcontract).symm target) ≤
      primaryActivity rate primary target / (1 - constant) := by
  let inverse := (primaryPerturbationEquiv rate primary error constant hrate hp hsmall hcontract).symm
  have heq : inverse target + error (inverse target) = target := by
    exact (primaryPerturbationEquiv rate primary error constant hrate hp hsmall hcontract).apply_symm_apply target
  have hrew : inverse target = target + -(error (inverse target)) := by
    calc
      inverse target = (inverse target + error (inverse target)) + -(error (inverse target)) := by abel
      _ = _ := by rw [heq]
  have ht := primaryActivity_add_le rate primary target (-(error (inverse target))) (le_of_lt hrate) hp
  rw [← hrew, primaryActivity_neg] at ht
  have hc := hcontract (inverse target)
  apply (le_div_iff₀ (by linarith : 0 < 1 - constant)).mpr
  change primaryActivity rate primary (inverse target) * (1 - constant) ≤ _
  nlinarith only [ht, hc]

/-- The concrete finite interval translation matrix on signed profiles. -/
noncomputable def intervalTranslationOperator (colors starts : ι → ℤ)
    (shift : ℤ) (width : ℕ) : Module.End ℝ (ι → ℝ) where
  toFun profile output := ∑ input,
    intervalAnchorDifference starts shift width input (colors output) * profile input
  map_add' first second := by
    funext output
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' scalar profile := by
    funext output
    simp [← Finset.mul_sum, mul_left_comm]

/-- The explicit translation activity constant after conversion to the
primary reference law. -/
noncomputable def intervalTranslationActivityConstant (rate shiftBound : ℝ)
    (width : ℕ) (lower : ℝ) : ℝ :=
  Real.sqrt (2 * shiftBound / ((width : ℝ) ^ 2 * lower)) + rate * (1 / ((width : ℝ) * lower))

theorem intervalTranslationOperator_activity_le (colors starts : ι → ℤ)
    (hinj : Function.Injective colors) (shift : ℤ) (width : ℕ)
    (rate shiftBound lower : ℝ) (primary profile : ι → ℝ)
    (hrate : 0 ≤ rate) (hp : ∀ input, 0 < primary input) (hmass : ∑ input, primary input = 1)
    (hlower : 0 < lower) (hout : ∀ output, lower ≤ primary output)
    (hshift : (shift.natAbs : ℝ) ≤ shiftBound) :
    primaryActivity rate primary (intervalTranslationOperator colors starts shift width profile) ≤
      intervalTranslationActivityConstant rate shiftBound width lower * primaryActivity rate primary profile := by
  have hsb : 0 ≤ shiftBound := (Nat.cast_nonneg shift.natAbs).trans hshift
  have hC : 0 ≤ 2 * shiftBound / ((width : ℝ) ^ 2 * lower) := by positivity
  apply primaryActivity_bound_of_parts rate primary profile _
    (Real.sqrt (2 * shiftBound / ((width : ℝ) ^ 2 * lower)))
    (1 / ((width : ℝ) * lower)) hrate (by positivity)
  · have hraw := finitePalette_anchorProfile_bound colors starts hinj shift width primary profile lower
      hp hmass hlower hout
    have hcoef : 2 * (shift.natAbs : ℝ) / ((width : ℝ) ^ 2 * lower) ≤
        2 * shiftBound / ((width : ℝ) ^ 2 * lower) := by
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    have hn := profileSquareNorm_nonneg primary profile (fun color => le_of_lt (hp color))
    have hbound := hraw.trans (mul_le_mul_of_nonneg_right hcoef hn)
    calc
      _ ≤ Real.sqrt ((2 * shiftBound / ((width : ℝ) ^ 2 * lower)) *
          profileSquareNorm primary profile) := Real.sqrt_le_sqrt hbound
      _ = _ := Real.sqrt_mul hC _
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro output
    rw [Real.norm_eq_abs]
    exact intervalAnchorDifference_density_row_bound starts shift (colors output) width primary profile
      (primary output) lower hp hmass hlower (hout output)

/-- Explicit rank-inverse activity constant obtained from the calibrated
sign-profile L1 and pointwise bounds. -/
noncomputable def rankInverseActivityConstant (rate activation majorant : ℝ)
    (signProfile sign : ι → ℝ) : ℝ :=
  1 + Real.sqrt (majorant * (∑ color, |signProfile color|) /
    (activation + signFunctional sign signProfile) ^ 2) +
      rate * (majorant / |activation + signFunctional sign signProfile|)

theorem finitePrimaryRankEquiv_activity_le (rate activation majorant : ℝ)
    (primary signProfile sign profile : ι → ℝ)
    (hrate : 0 ≤ rate) (hp : ∀ color, 0 < primary color) (hmass : ∑ color, primary color = 1)
    (hmajorant : 0 ≤ majorant) (hsign : ∀ color, |sign color| ≤ 1)
    (hprofile : ∀ color, |signProfile color| ≤ majorant * primary color)
    (hsmall : (∑ color, |signProfile color|) < activation) :
    primaryActivity rate primary ((finitePrimaryRankEquiv activation signProfile sign hsign hsmall).symm profile) ≤
      rankInverseActivityConstant rate activation majorant signProfile sign * primaryActivity rate primary profile := by
  let denominator := activation + signFunctional sign signProfile
  let correction := (signFunctional sign profile / denominator) • signProfile
  have hC : 0 ≤ majorant * (∑ color, |signProfile color|) / denominator ^ 2 := by
    exact div_nonneg (mul_nonneg hmajorant (Finset.sum_nonneg fun color _ => abs_nonneg _)) (sq_nonneg _)
  have hcorrection : primaryActivity rate primary correction ≤
      (Real.sqrt (majorant * (∑ color, |signProfile color|) / denominator ^ 2) +
        rate * (majorant / |denominator|)) * primaryActivity rate primary profile := by
    apply primaryActivity_bound_of_parts rate primary profile correction _ _ hrate (by positivity)
    · have hraw := rankCorrection_profileSquareNorm_le primary signProfile sign profile denominator majorant
        hp hmass hsign hmajorant hprofile
      calc
        _ ≤ Real.sqrt ((majorant * (∑ color, |signProfile color|) / denominator ^ 2) *
            profileSquareNorm primary profile) := Real.sqrt_le_sqrt hraw
        _ = _ := Real.sqrt_mul hC _
    · exact rankCorrection_densityNorm_le primary signProfile sign profile denominator majorant
        hp hmass hsign hmajorant hprofile
  have hrepr : (finitePrimaryRankEquiv activation signProfile sign hsign hsmall).symm profile =
      profile + -correction := by
    rw [finitePrimaryRankEquiv_inverse_apply]
    have hscalar : (activation + signFunctional sign signProfile)⁻¹ * signFunctional sign profile =
        signFunctional sign profile / denominator := by dsimp [denominator]; ring
    rw [hscalar]
    rfl
  rw [hrepr]
  have ht := primaryActivity_add_le rate primary profile (-correction) hrate hp
  rw [primaryActivity_neg] at ht
  unfold rankInverseActivityConstant
  dsimp [denominator] at hcorrection
  nlinarith only [ht, hcorrection]

/-- Average the actual interval difference operators over finite public
anchor branches and bounded source shifts. The source is not resampled
inside a row; each summand retains its prescribed branch and displacement. -/
noncomputable def averagedIntervalTranslationOperator {τ : Type*} [Fintype τ]
    (colors : ι → ℤ) (starts : τ → ι → ℤ) (shifts : τ → ℤ)
    (width : ℕ) (weights : τ → ℝ) : Module.End ℝ (ι → ℝ) :=
  ∑ source, weights source • intervalTranslationOperator colors (starts source) (shifts source) width

theorem averagedIntervalTranslationOperator_activity_le {τ : Type*} [Fintype τ]
    (colors : ι → ℤ) (starts : τ → ι → ℤ) (shifts : τ → ℤ)
    (width : ℕ) (weights : τ → ℝ) (hinj : Function.Injective colors)
    (rate shiftBound lower : ℝ) (primary profile : ι → ℝ)
    (hweights : ∀ source, 0 ≤ weights source) (hweightmass : ∑ source, weights source = 1)
    (hrate : 0 ≤ rate) (hp : ∀ input, 0 < primary input) (hmass : ∑ input, primary input = 1)
    (hlower : 0 < lower) (hout : ∀ output, lower ≤ primary output)
    (hshift : ∀ source, ((shifts source).natAbs : ℝ) ≤ shiftBound) :
    primaryActivity rate primary
      (averagedIntervalTranslationOperator colors starts shifts width weights profile) ≤
      intervalTranslationActivityConstant rate shiftBound width lower * primaryActivity rate primary profile := by
  simp only [averagedIntervalTranslationOperator, LinearMap.sum_apply, LinearMap.smul_apply]
  calc
    _ ≤ ∑ source, primaryActivity rate primary
        (weights source • intervalTranslationOperator colors (starts source) (shifts source) width profile) :=
      primaryActivity_sum_le Finset.univ rate primary _ hrate hp
    _ = ∑ source, weights source * primaryActivity rate primary
        (intervalTranslationOperator colors (starts source) (shifts source) width profile) := by
      simp only [primaryActivity_smul, abs_of_nonneg (hweights _)]
    _ ≤ ∑ source, weights source * (intervalTranslationActivityConstant rate shiftBound width lower *
        primaryActivity rate primary profile) := by
      exact Finset.sum_le_sum fun source _ => mul_le_mul_of_nonneg_left
        (intervalTranslationOperator_activity_le colors (starts source) hinj (shifts source) width
          rate shiftBound lower primary profile hrate hp hmass hlower hout (hshift source)) (hweights source)
    _ = _ := by rw [← Finset.sum_mul, hweightmass, one_mul]

/-- Construct the actual finite primary operator inverse from the concrete
calibrated sign profile and the actual averaged interval translation matrix.
The only smallness assumption is the displayed explicit numerical product;
it is not an invertibility or inverse-bound hypothesis. -/
theorem finiteIntervalPrimary_inverse_exists {τ : Type*} [Fintype τ]
    (colors : ι → ℤ) (starts : τ → ι → ℤ) (shifts : τ → ℤ)
    (width : ℕ) (weights : τ → ℝ) (hinj : Function.Injective colors)
    (rate shiftBound lower activation majorant : ℝ)
    (primary signProfile sign : ι → ℝ)
    (hweights : ∀ source, 0 ≤ weights source) (hweightmass : ∑ source, weights source = 1)
    (hrate : 0 < rate) (hp : ∀ input, 0 < primary input) (hmass : ∑ input, primary input = 1)
    (hlower : 0 < lower) (hout : ∀ output, lower ≤ primary output)
    (hshift : ∀ source, ((shifts source).natAbs : ℝ) ≤ shiftBound)
    (hmajorant : 0 ≤ majorant) (hsign : ∀ color, |sign color| ≤ 1)
    (hprofile : ∀ color, |signProfile color| ≤ majorant * primary color)
    (hsignsmall : (∑ color, |signProfile color|) < activation)
    (hsmall : rankInverseActivityConstant rate activation majorant signProfile sign *
      intervalTranslationActivityConstant rate shiftBound width lower < 1) :
    ∃ inverse : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ),
      inverse.toLinearMap = primaryRankOperator activation signProfile (profileSignMap sign) +
        averagedIntervalTranslationOperator colors starts shifts width weights ∧
      ∀ target, primaryActivity rate primary (inverse.symm target) ≤
        (rankInverseActivityConstant rate activation majorant signProfile sign /
          (1 - rankInverseActivityConstant rate activation majorant signProfile sign *
            intervalTranslationActivityConstant rate shiftBound width lower)) *
          primaryActivity rate primary target := by
  let rank := finitePrimaryRankEquiv activation signProfile sign hsign hsignsmall
  let error := averagedIntervalTranslationOperator colors starts shifts width weights
  let correction := rank.symm.toLinearMap.comp error
  let rankBound := rankInverseActivityConstant rate activation majorant signProfile sign
  let errorBound := intervalTranslationActivityConstant rate shiftBound width lower
  have hrank : ∀ profile, primaryActivity rate primary (rank.symm profile) ≤
      rankBound * primaryActivity rate primary profile := fun profile =>
    finitePrimaryRankEquiv_activity_le rate activation majorant primary signProfile sign profile
      (le_of_lt hrate) hp hmass hmajorant hsign hprofile hsignsmall
  have herr : ∀ profile, primaryActivity rate primary (error profile) ≤
      errorBound * primaryActivity rate primary profile := fun profile =>
    averagedIntervalTranslationOperator_activity_le colors starts shifts width weights hinj
      rate shiftBound lower primary profile hweights hweightmass (le_of_lt hrate)
      hp hmass hlower hout hshift
  have hrankNonneg : 0 ≤ rankBound := by
    dsimp [rankBound, rankInverseActivityConstant]
    positivity
  have hcontract : ∀ profile, primaryActivity rate primary (correction profile) ≤
      (rankBound * errorBound) * primaryActivity rate primary profile := by
    intro profile
    have h := (hrank (error profile)).trans
      (mul_le_mul_of_nonneg_left (herr profile) hrankNonneg)
    simpa only [correction, LinearMap.comp_apply, LinearEquiv.coe_coe, mul_assoc] using h
  let neumann := primaryPerturbationEquiv rate primary correction (rankBound * errorBound)
    hrate hp hsmall hcontract
  refine ⟨neumann.trans rank, ?_, ?_⟩
  · apply LinearMap.ext
    intro profile
    change rank (profile + rank.symm (error profile)) = rank profile + error profile
    simp only [map_add, LinearEquiv.apply_symm_apply]
  · intro target
    change primaryActivity rate primary (neumann.symm (rank.symm target)) ≤ _
    have hden : 0 < 1 - rankBound * errorBound := by dsimp [rankBound, errorBound]; linarith
    calc
      _ ≤ primaryActivity rate primary (rank.symm target) / (1 - rankBound * errorBound) :=
        primaryPerturbationEquiv_inverse_bound rate primary correction (rankBound * errorBound)
          hrate hp hsmall hcontract (rank.symm target)
      _ ≤ (rankBound * primaryActivity rate primary target) / (1 - rankBound * errorBound) :=
        div_le_div_of_nonneg_right (hrank target) (le_of_lt hden)
      _ = _ := by dsimp [rankBound, errorBound]; ring

/-- The actual mass-zero interior profile subspace. -/
def canonicalInteriorProfiles (interior : Finset ι) : Submodule ℝ (ι → ℝ) where
  carrier := {profile | (∑ color, profile color) = 0 ∧ ∀ color ∉ interior, profile color = 0}
  zero_mem' := by simp
  add_mem' := by
    intro first second hfirst hsecond
    constructor
    · simpa only [Pi.add_apply, Finset.sum_add_distrib, hfirst.1, hsecond.1] using add_zero (0 : ℝ)
    · intro color hout
      simp [hfirst.2 color hout, hsecond.2 color hout]
  smul_mem' := by
    intro scalar profile hprofile
    constructor
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hprofile.1, mul_zero]
    · intro color hout
      simp [hprofile.2 color hout]

/-- Canonical interior profiles are exactly annihilated by the concrete
boundary collapse, without any positivity assumption on the reference. -/
theorem boundaryCollapse_eq_zero_of_canonicalInterior [DecidableEq ι]
    (interior : Finset ι) (primary profile : ι → ℝ)
    (hprofile : profile ∈ canonicalInteriorProfiles interior) :
    boundaryCollapse interior primary profile = 0 := by
  have hsum : ∑ color ∈ interior, profile color = 0 := by
    calc
      _ = ∑ color, profile color :=
        Finset.sum_subset (Finset.subset_univ _) (fun color _ hout => hprofile.2 color hout)
      _ = 0 := hprofile.1
  funext color
  by_cases hc : color ∈ interior
  · simp [boundaryCollapse, hc, hsum]
  · simp [boundaryCollapse, hc, hprofile.2 color hc]

theorem boundaryIdealProjection_eq_self_of_canonicalInterior [DecidableEq ι]
    (interior : Finset ι) (primary profile : ι → ℝ)
    (hprofile : profile ∈ canonicalInteriorProfiles interior) :
    boundaryIdealProjection interior primary profile = profile := by
  simp only [boundaryIdealProjection, LinearMap.sub_apply, LinearMap.id_apply,
    boundaryCollapse_eq_zero_of_canonicalInterior interior primary profile hprofile, sub_zero]

theorem boundaryIdealProjection_mem_canonicalInterior [DecidableEq ι]
    (interior : Finset ι) (primary profile : ι → ℝ)
    (hmass : ∑ color ∈ interior, primary color ≠ 0) :
    boundaryIdealProjection interior primary profile ∈ canonicalInteriorProfiles interior :=
  boundaryIdealProjection_canonical interior primary profile hmass

/-- Concrete anchor support and row mass calculations place every
translation response in the boundary ideal. -/
theorem intervalTranslationOperator_mem_interior [DecidableEq ι]
    (colors starts : ι → ℤ) (hinj : Function.Injective colors) (shift : ℤ) (width : ℕ)
    (hwidth : width ≠ 0) (interior : Finset ι)
    (hsafe : ∀ input, anchorInterval (starts input) width ∪
      anchorInterval (starts input + shift) width ⊆ interior.image colors)
    (profile : ι → ℝ) :
    intervalTranslationOperator colors starts shift width profile ∈ canonicalInteriorProfiles interior := by
  constructor
  · change (∑ output, ∑ input,
      intervalAnchorDifference starts shift width input (colors output) * profile input) = 0
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro input _
    rw [← Finset.sum_mul, finitePalette_anchorDifference_mass colors starts hinj shift width hwidth input]
    · simp
    · exact (hsafe input).trans (Finset.image_subset_image (Finset.subset_univ _))
  · intro output hout
    change (∑ input, intervalAnchorDifference starts shift width input (colors output) * profile input) = 0
    apply Finset.sum_eq_zero
    intro input _
    have hz : intervalAnchorDifference starts shift width input (colors output) = 0 := by
      apply anchorTranslation_zero_outside
      intro hmem
      obtain ⟨color, hcolor, heq⟩ := Finset.mem_image.mp (hsafe input hmem)
      exact hout (hinj heq ▸ hcolor)
    rw [hz, zero_mul]

theorem averagedIntervalTranslationOperator_mem_interior {τ : Type*} [Fintype τ]
    [DecidableEq ι] (colors : ι → ℤ) (starts : τ → ι → ℤ) (shifts : τ → ℤ)
    (width : ℕ) (weights : τ → ℝ) (hinj : Function.Injective colors)
    (hwidth : width ≠ 0) (interior : Finset ι)
    (hsafe : ∀ source input, anchorInterval (starts source input) width ∪
      anchorInterval (starts source input + shifts source) width ⊆ interior.image colors)
    (profile : ι → ℝ) :
    averagedIntervalTranslationOperator colors starts shifts width weights profile ∈
      canonicalInteriorProfiles interior := by
  simp only [averagedIntervalTranslationOperator, LinearMap.sum_apply, LinearMap.smul_apply]
  apply Submodule.sum_mem
  intro source _
  apply Submodule.smul_mem
  exact intervalTranslationOperator_mem_interior colors (starts source) hinj (shifts source)
    width hwidth interior (hsafe source) profile

omit [Fintype ι] in
/-- If an invertible operator only adds mass-zero interior profiles, its
inverse has the same property. This establishes the precise boundary
preservation needed before the conjugated legal projection is applied. -/
theorem linearEquiv_inverse_difference_mem (operator : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))
    (subspace : Submodule ℝ (ι → ℝ))
    (hrange : ∀ profile, operator profile - profile ∈ subspace) (profile : ι → ℝ) :
    operator.symm profile - profile ∈ subspace := by
  have h := subspace.neg_mem (hrange (operator.symm profile))
  simpa only [LinearEquiv.apply_symm_apply, neg_sub] using h

/-- The actual local primary operator and its constructed inverse preserve
the boundary ideal, including for noncanonical ambient profiles. -/
theorem finitePrimary_inverse_preserves_interior {τ : Type*} [Fintype τ] [DecidableEq ι]
    (colors : ι → ℤ) (starts : τ → ι → ℤ) (shifts : τ → ℤ)
    (width : ℕ) (weights : τ → ℝ) (hinj : Function.Injective colors)
    (hwidth : width ≠ 0) (interior : Finset ι)
    (hsafe : ∀ source input, anchorInterval (starts source input) width ∪
      anchorInterval (starts source input + shifts source) width ⊆ interior.image colors)
    (activation : ℝ) (signProfile sign : ι → ℝ)
    (hsignProfile : signProfile ∈ canonicalInteriorProfiles interior)
    (operator : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))
    (hoperator : operator.toLinearMap = primaryRankOperator activation signProfile (profileSignMap sign) +
      averagedIntervalTranslationOperator colors starts shifts width weights)
    (profile : ι → ℝ) :
    operator profile - profile ∈ canonicalInteriorProfiles interior ∧
      operator.symm profile - profile ∈ canonicalInteriorProfiles interior := by
  have hforward : ∀ input, operator input - input ∈ canonicalInteriorProfiles interior := by
    intro input
    have heval := congrArg (fun map : Module.End ℝ (ι → ℝ) => map input) hoperator
    change operator input = primaryRankOperator activation signProfile (profileSignMap sign) input +
      averagedIntervalTranslationOperator colors starts shifts width weights input at heval
    rw [heval, primaryRankOperator_apply]
    have heq : input + (activation⁻¹ * profileSignMap sign input) • signProfile +
        averagedIntervalTranslationOperator colors starts shifts width weights input - input =
        (activation⁻¹ * profileSignMap sign input) • signProfile +
        averagedIntervalTranslationOperator colors starts shifts width weights input := by abel
    rw [heq]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hsignProfile)
      (averagedIntervalTranslationOperator_mem_interior colors starts shifts width weights hinj
        hwidth interior hsafe input)
  exact ⟨hforward profile, linearEquiv_inverse_difference_mem operator _ hforward profile⟩

/-- Conjugating the concrete boundary projection by the constructed local
inverse gives a genuine projection onto safe canonical inputs. It has the
required evaluated output and fixes every already safe canonical input. -/
theorem finitePrimary_safe_projection {τ : Type*} [Fintype τ] [DecidableEq ι]
    (colors : ι → ℤ) (starts : τ → ι → ℤ) (shifts : τ → ℤ)
    (width : ℕ) (weights : τ → ℝ) (hinj : Function.Injective colors)
    (hwidth : width ≠ 0) (interior : Finset ι)
    (hsafe : ∀ source input, anchorInterval (starts source input) width ∪
      anchorInterval (starts source input + shifts source) width ⊆ interior.image colors)
    (activation : ℝ) (primary signProfile sign : ι → ℝ)
    (hmass : ∑ color ∈ interior, primary color ≠ 0)
    (hsignProfile : signProfile ∈ canonicalInteriorProfiles interior)
    (operator : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))
    (hoperator : operator.toLinearMap = primaryRankOperator activation signProfile (profileSignMap sign) +
      averagedIntervalTranslationOperator colors starts shifts width weights) :
    (∀ profile, legalInputProjection operator (boundaryIdealProjection interior primary) profile ∈
      canonicalInteriorProfiles interior) ∧
    (∀ profile, operator (legalInputProjection operator (boundaryIdealProjection interior primary) profile) =
      boundaryIdealProjection interior primary (operator profile)) ∧
    (∀ profile ∈ canonicalInteriorProfiles interior,
      legalInputProjection operator (boundaryIdealProjection interior primary) profile = profile) := by
  have hpres := finitePrimary_inverse_preserves_interior colors starts shifts width weights hinj
    hwidth interior hsafe activation signProfile sign hsignProfile operator hoperator
  refine ⟨?_, ?_, ?_⟩
  · intro profile
    let output := boundaryIdealProjection interior primary (operator profile)
    have hout : output ∈ canonicalInteriorProfiles interior :=
      boundaryIdealProjection_mem_canonicalInterior interior primary (operator profile) hmass
    have hh := (canonicalInteriorProfiles interior).add_mem (hpres output).2 hout
    simpa only [sub_add_cancel] using hh
  · intro profile
    exact legalInputProjection_evaluation operator (boundaryIdealProjection interior primary) profile
  · intro profile hprofile
    have hout := (canonicalInteriorProfiles interior).add_mem (hpres profile).1 hprofile
    simp only [sub_add_cancel] at hout
    simp only [legalInputProjection, LinearMap.comp_apply, LinearEquiv.coe_coe,
      boundaryIdealProjection_eq_self_of_canonicalInterior interior primary (operator profile) hout,
      LinearEquiv.symm_apply_apply]

end ProfileActivity

end AFT
