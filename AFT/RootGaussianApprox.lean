import AFT.ClippedConvolution
import AFT.GaussianRatio

/-!
# The Gaussian approximation to the actual clipped-root marginal ratio

Every sum probability is that of the finite integer-window source.
All approximation hypotheses below are scalar comparisons with the explicit
Poisson-and-clipping error formula, not assumed probabilistic estimates.
-/

namespace AFT.GaussianSource

open scoped BigOperators Classical

noncomputable abbrev rootProbability (width : ℝ) (cutoff count : ℕ) (target : ℤ) : ℝ :=
  RootSlice.probability (fun _ : Fin count => windowGaussian width cutoff) (fun z => (z : ℤ)) target

theorem rootProbability_model_error (width error : ℝ) (cutoff count : ℕ)
    (hw : 0 < width) (hc : 0 < count) (he0 : 0 ≤ error) (he1 : error ≤ 1)
    (he : thetaError (width / Real.sqrt 2) ≤ error) (target : ℤ) :
    |rootProbability width cutoff count target / sumModel width (realNormalizer width) count target - 1| ≤
      rootSumError width error cutoff (count - 1) target := by
  have h := window_root_gaussian_relative_error width error cutoff (count - 1) hw he0 he1 he target
  unfold gaussianSumApprox at h
  rw [gaussianSumApprox_model width hw, Nat.sub_add_cancel hc] at h
  exact h

theorem prod_one_special {ι : Type*} [Fintype ι] [DecidableEq ι]
    (distinguished : ι) (special usual : ℝ) :
    (∏ i : ι, if i = distinguished then special else usual) =
      special * usual ^ (Fintype.card ι - 1) := by
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ distinguished]
  have hp : (∏ i : {i : ι // i ≠ distinguished}, if (i : ι) = distinguished then special else usual) =
      ∏ _i : {i : ι // i ≠ distinguished}, usual := by
    apply Finset.prod_congr rfl
    intro i _
    exact if_neg i.property
  rw [hp]
  simp

/-- Explicit error propagation for the exact root marginal divided by the
product of its exact one-coordinate marginals. The center can range over all
clipped tuples; only the displayed computable scalar errors need bounding. -/
theorem root_probability_ratio_error (width thetaBound error : ℝ) (cutoff population order : ℕ)
    (hw : 0 < width) (hp : order < population) (ho : 0 < order)
    (ht0 : 0 ≤ thetaBound) (ht1 : thetaBound ≤ 1)
    (ht : thetaError (width / Real.sqrt 2) ≤ thetaBound)
    (he0 : 0 ≤ error) (he1 : error < 1) (value : Fin order → ℤ)
    (hremaining : rootSumError width thetaBound cutoff (population - order - 1) (-∑ i, value i) ≤ error)
    (hroot : rootSumError width thetaBound cutoff (population - 1) 0 ≤ error)
    (hmarginal : ∀ i, rootSumError width thetaBound cutoff (population - 1 - 1) (-value i) ≤ error) :
    |(rootProbability width cutoff (population - order) (-∑ i, value i) *
          rootProbability width cutoff population 0 ^ (order - 1) /
          (∏ i, rootProbability width cutoff (population - 1) (-value i))) /
        (rootModelPrefactor width (realNormalizer width) population order *
          Real.exp (rootExponent width population value)) - 1| ≤ ratioError error order := by
  let distinguished : Fin order := ⟨0, ho⟩
  let numerator : Fin order → ℝ := fun i => if i = distinguished then
    rootProbability width cutoff (population - order) (-∑ j, value j)
    else rootProbability width cutoff population 0
  let modelNumerator : Fin order → ℝ := fun i => if i = distinguished then
    sumModel width (realNormalizer width) (population - order) (-∑ j, value j)
    else sumModel width (realNormalizer width) population 0
  let denominator : Fin order → ℝ := fun i => rootProbability width cutoff (population - 1) (-value i)
  let modelDenominator : Fin order → ℝ := fun i =>
    sumModel width (realNormalizer width) (population - 1) (-value i)
  have hn : 0 < population := by omega
  have hn1 : 0 < population - 1 := by omega
  have hrem : 0 < population - order := Nat.sub_pos_of_lt hp
  have hz : 0 < realNormalizer width := zero_lt_one.trans_le (realNormalizer_ge_one width hw)
  have hmodelN (i : Fin order) : 0 < modelNumerator i := by
    dsimp [modelNumerator]
    split_ifs
    · exact sumModel_pos width _ _ hw hz hrem _
    · exact sumModel_pos width _ _ hw hz hn _
  have hmodelD (i : Fin order) : 0 < modelDenominator i := sumModel_pos width _ _ hw hz hn1 _
  have hnum (i : Fin order) : |numerator i / modelNumerator i - 1| ≤ error := by
    dsimp [numerator, modelNumerator]
    split_ifs
    · exact (rootProbability_model_error width thetaBound cutoff (population - order)
        hw hrem ht0 ht1 ht _).trans hremaining
    · exact (rootProbability_model_error width thetaBound cutoff population
        hw hn ht0 ht1 ht _).trans hroot
  have hden (i : Fin order) : |denominator i / modelDenominator i - 1| ≤ error :=
    (rootProbability_model_error width thetaBound cutoff (population - 1)
      hw hn1 ht0 ht1 ht _).trans (hmarginal i)
  have h := product_quotient_relative_error numerator denominator modelNumerator modelDenominator
    error he0 he1 hmodelN hmodelD hnum hden
  dsimp only [numerator, denominator, modelNumerator, modelDenominator] at h
  rw [prod_one_special, prod_one_special, Fintype.card_fin,
    sumModel_root_ratio width (realNormalizer width) population order hp ho value] at h
  exact h

end AFT.GaussianSource
