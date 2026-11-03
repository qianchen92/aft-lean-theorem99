import AFT.IndependentPairedFirst

/-! # Exact independent first response for any chart realizing the same law -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration PhysicalBlockTensors Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance independentPairedChartIdentityFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

theorem independentPairedNumerator_charts_eq (C : ℝ) (n : ℕ) (beta : ℝ)
    (first second : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (he : ∀ mark attached left right,publicChartRaw C n mark (first mark) attached left right=
      publicChartRaw C n mark (second mark) attached left right)
    (profile : Fin (Parameters.modulus n) → ℝ) :
    independentPairedNumerator C n beta first profile=independentPairedNumerator C n beta second profile := by
  funext word
  simp only [independentPairedNumerator,actualJointPairedNumerator,fixedPairedChartRaw,he]

theorem independentPaired_first_with_charts_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
    ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    (∀ mark attached first second,publicChartRaw C n mark (charts mark) attached first second=
      conditionalJointOutput C n mark attached first second) →
    ∀ profile : Fin (Parameters.modulus n) → ℝ,(∑ color,profile color)=0 →
      (∑ word,independentPairedNumerator C n (beta n) charts profile word)=0 ∧
      ∀ output,fourOutputCount (independentPairedNumerator C n (beta n) charts profile) output=
        v7Activation C n*actualResponse C n profile output := by
  filter_upwards [independentPaired_first_eventually C hC beta hbeta] with n hi charts hc profile hp
  obtain ⟨chosen,hchosen,hfirst⟩ := hi
  rw [independentPairedNumerator_charts_eq C n (beta n) charts chosen
    (fun mark attached first second => (hc mark attached first second).trans (hchosen mark attached first second).symm)]
  exact hfirst profile hp

end
end AFT.V7Calibration
