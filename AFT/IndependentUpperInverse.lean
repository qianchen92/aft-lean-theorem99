import AFT.IndependentUpperOperator

/-! # Explicit finite Neumann correction of the actual independent upper map -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance independentUpperInverseFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- Every correction depth is finite. Its true residual is the next operator
power, so the lambda exponent increases with the requested depth. -/
theorem independentUpperLinear_finite_inverse_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ) (pool : ℕ → ℕ) (cutoff : ℕ)
    (htypical : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n ∧
      Parameters.legs n ≤ 2*pool n ∧ pool n ≤ Parameters.legs n) :
    ∀ᶠ n in atTop,
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n →
    ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    (∀ mark first second,publicChartRaw C n mark (charts mark) (fun _ => 1) first second=
      conditionalJointOutput C n mark (fun _ => 1) first second) →
    ∀ bodyPool radius : ℝ,0 ≤ radius → ∀ localDepth correctionDepth : ℕ,
    ∀ table : Table (InputSeed (Fin (Parameters.modulus n))),
    let weight := inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (pool n) bodyPool radius
    let upper := independentUpperLinear C n (beta n) operator charts cutoff localDepth
    activity weight (finiteCorrection upper correctionDepth table) ≤ 2*activity weight table ∧
    activity weight ((1+upper) (finiteCorrection upper correctionDepth table)-table) ≤
      (independentGlobalUpperConstant C cutoff/(n : ℝ)^(5/2 : ℝ))^(correctionDepth+1)*activity weight table := by
  have ht : Tendsto (fun n : ℕ => independentGlobalUpperConstant C cutoff/(n : ℝ)^(5/2 : ℝ)) atTop (𝓝 0) :=
    (((tendsto_rpow_atTop (by norm_num : (0:ℝ)<5/2)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)).const_div_atTop _)
  filter_upwards [independentUpperLinear_activity_eventually C hC beta pool cutoff htypical,
    Filter.Tendsto.eventually_le_const (by norm_num : (0:ℝ)<1/2) ht]
    with n hi hsmall operator hop charts hcharts bodyPool radius hradius localDepth correctionDepth table
  let weight := inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (pool n) bodyPool radius
  have hw (seed) : 0 ≤ weight seed := inputWeight_nonneg _ _ _ _ _ seed hradius
  have ha := activationConstant_pos C hC
  have hb : 0 ≤ independentGlobalUpperConstant C cutoff/(n : ℝ)^(5/2 : ℝ) := by
    unfold independentGlobalUpperConstant independentGlobalBudgetConstant independentJointHigherConstant
      independentReferenceHilbertConstant independentPositiveInputConstant independentBodyInputConstant
    positivity
  have hbound := hi operator hop charts hcharts bodyPool radius hradius localDepth
  exact ⟨activity_operator_correction_le_two weight hw _
    (fun input => (hbound input).trans (mul_le_mul_of_nonneg_right hsmall (activity_nonneg weight hw input)))
      correctionDepth table,
    activity_operator_correction_residual weight _ _ hb hbound correctionDepth table⟩

theorem independentUpperLinear_finite_inverse_canonical_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n →
    ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    ∀ cutoff localDepth correctionDepth : ℕ,∀ table : Table (InputSeed (Fin (Parameters.modulus n))),
    InputTableCanonical (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) table →
    InputTableCanonical (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
      (finiteCorrection (independentUpperLinear C n (beta n) operator charts cutoff localDepth) correctionDepth table) := by
  filter_upwards [independentUpperLinear_canonical_eventually C hC beta hbeta]
    with n hi operator hop charts cutoff localDepth correctionDepth table hc
  simp only [finiteCorrection,LinearMap.sum_apply]
  apply InputTableCanonical.sum
  intro power _
  cases power with
  | zero => simpa using hc
  | succ power =>
    rw [pow_succ',Module.End.mul_apply,LinearMap.neg_apply]
    exact (hi operator hop charts cutoff localDepth _).neg

end
end AFT.V7Calibration
