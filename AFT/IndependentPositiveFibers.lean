import AFT.IndependentRootBlock
import AFT.PositiveDensityFibers
import AFT.FixedPairedMarginals

/-! # Genuine fibers of the independent positive paired denominator -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance independentPositiveFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

def independentPairedPositiveDensity (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark)
    (word : Fin 4 → Fin (Parameters.modulus parameter)) : ℝ :=
  independentPairedPositiveMass cutoffScale parameter beta charts word /
    (FiniteDist.independent (fun _ : Fin 4 => actualPrimaryLaw cutoffScale parameter beta)).weight word

/-- Both the full density and every one-coordinate marginal are inherited
from the actual positive chart, averaged under the two independent root laws. -/
theorem independentPairedPositiveMass_bounds_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ)/(2*Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2*(Parameters.legs parameter : ℝ)/Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
    ∀ charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark,
    (∀ mark first second,publicChartRaw cutoffScale parameter mark (charts mark) (fun _ => 1) first second =
      conditionalJointOutput cutoffScale parameter mark (fun _ => 1) first second) →
    (∀ word,independentPairedPositiveMass cutoffScale parameter (beta parameter) charts word ≤
      (34816*(parameter : ℝ)^8)*(FiniteDist.independent
        (fun _ : Fin 4 => actualPrimaryLaw cutoffScale parameter (beta parameter))).weight word) ∧
    (∀ slot color,(∑ word,if word slot=color then independentPairedPositiveMass cutoffScale parameter (beta parameter) charts word else 0) ≤
      2048*(actualPrimaryLaw cutoffScale parameter (beta parameter)).weight color) := by
  filter_upwards [fixedPairedKernel_primary_density_eventually cutoffScale hscale beta hbeta,
    fixedPairedKernel_singleton_primary_eventually cutoffScale hscale beta hbeta]
    with parameter hd hm charts hc
  have hr (root : Window (v7RootCutoff parameter)) : |(root : ℤ)| ≤ (v7RootCutoff parameter : ℤ) :=
    abs_le.mpr (Finset.mem_Icc.mp root.property)
  constructor
  · intro word
    calc
      _ ≤ ∑ roots,(pairedRootReference parameter).weight roots *
          ((34816*(parameter : ℝ)^8)*(FiniteDist.independent
            (fun _ : Fin 4 => actualPrimaryLaw cutoffScale parameter (beta parameter))).weight word) := by
        exact Finset.sum_le_sum fun roots _ => mul_le_mul_of_nonneg_left
          (hd charts hc roots.1 roots.2 0 (hr roots.1) (by simp) word) (FiniteDist.nonneg _ _)
      _ = _ := by rw [← Finset.sum_mul,FiniteDist.sum_one,one_mul]
  · intro slot color
    have heq (word : Fin 4 → Fin (Parameters.modulus parameter)) :
        (if word slot=color then independentPairedPositiveMass cutoffScale parameter (beta parameter) charts word else 0) =
        ∑ roots,(pairedRootReference parameter).weight roots *
          (if word slot=color then ∑ input,
            ((actualPrimaryLaw cutoffScale parameter (beta parameter)).prod (actualBodyLaw cutoffScale parameter (beta parameter))).weight input *
              fixedPairedKernel cutoffScale parameter (beta parameter) charts roots.1 roots.2 0 input word else 0) := by
      split_ifs <;> simp [independentPairedPositiveMass]
    simp_rw [heq]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum]
    calc
      _ ≤ ∑ roots,(pairedRootReference parameter).weight roots *
          (2048*(actualPrimaryLaw cutoffScale parameter (beta parameter)).weight color) := by
        exact Finset.sum_le_sum fun roots _ => mul_le_mul_of_nonneg_left
          (hm charts hc roots.1 roots.2 0 (hr roots.1) (hr roots.2) (by simp) slot color) (FiniteDist.nonneg _ _)
      _ = _ := by rw [← Finset.sum_mul,FiniteDist.sum_one,one_mul]

/-- The positive denominator has lambda^4 integrated and one-fixed norms,
while two or more fixed coordinates use the lambda^8 density ceiling. -/
theorem independentPairedPositiveDensity_fibers_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ)/(2*Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2*(Parameters.legs parameter : ℝ)/Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
    ∀ charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark,
    (∀ mark first second,publicChartRaw cutoffScale parameter mark (charts mark) (fun _ => 1) first second =
      conditionalJointOutput cutoffScale parameter mark (fun _ => 1) first second) →
    (FiniteDist.independent (fun _ : Fin 4 => actualPrimaryLaw cutoffScale parameter (beta parameter))).l2Sq
      (independentPairedPositiveDensity cutoffScale parameter (beta parameter) charts) ≤ 34816*(parameter : ℝ)^8 ∧
    (∀ slot values,MixedKernel.fiberSq (fun _ : Fin 4 => actualPrimaryLaw cutoffScale parameter (beta parameter))
      (independentPairedPositiveDensity cutoffScale parameter (beta parameter) charts) {slot} values ≤
        (34816*2048)*(parameter : ℝ)^8) ∧
    (∀ word,|independentPairedPositiveDensity cutoffScale parameter (beta parameter) charts word| ≤ 34816*(parameter : ℝ)^8) := by
  filter_upwards [independentPairedPositiveMass_bounds_eventually cutoffScale hscale beta hbeta,
    independentPairedPositiveMass_probability_eventually cutoffScale hscale beta hbeta,
    actual_primary_law_quarter_lower_eventually cutoffScale hscale beta hbeta]
    with parameter hb hm hp charts hc
  have hq : (0 : ℝ) < Parameters.modulus parameter := Nat.cast_pos.mpr (Parameters.modulus_prime parameter).pos
  have hpositive (color) : 0 < (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight color :=
    (by positivity : (0 : ℝ) < 1/(4*(Parameters.modulus parameter : ℝ))).trans_le (hp color)
  have href (word : Fin 4 → Fin (Parameters.modulus parameter)) : 0 <
      (FiniteDist.independent (fun _ : Fin 4 => actualPrimaryLaw cutoffScale parameter (beta parameter))).weight word :=
    by
      change 0 < ∏ slot : Fin 4,(actualPrimaryLaw cutoffScale parameter (beta parameter)).weight (word slot)
      exact Finset.prod_pos fun slot _ => hpositive (word slot)
  have hh := hb charts hc
  have ht := hm charts
  refine ⟨?_,?_,?_⟩
  · exact positiveDensity_l2Sq_le _ _ _ href (by positivity) ht.1 ht.2.le hh.1
  · intro slot values
    have he := MixedKernel.positiveDensity_singleton_square_le
      (fun _ : Fin 4 => actualPrimaryLaw cutoffScale parameter (beta parameter))
      (independentPairedPositiveMass cutoffScale parameter (beta parameter) charts)
      (34816*(parameter : ℝ)^8) 2048 (fun _ => hpositive) (by positivity) ht.1 hh.1 hh.2 slot values
    exact he.trans_eq (by ring)
  · exact positiveDensity_abs_le _ _ _ href ht.1 hh.1

end
end AFT.V7Calibration
