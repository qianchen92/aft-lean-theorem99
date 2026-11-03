import AFT.ActualPairedBudgets
import AFT.ActualFockChannels
import AFT.FourOutputFock

/-! # The complete actual primary Fock channel has norm scale lambda^-15 -/
namespace AFT.V7Calibration
open Filter GaussianSource LocalTensors
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance actualPrimaryFockFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def primaryFockEnergyConstant : ℝ := 40 * fixedResponseEnergyConstant + 35200 * 409600

theorem primaryFockEnergyConstant_pos : 0 < primaryFockEnergyConstant := by
  unfold primaryFockEnergyConstant fixedResponseEnergyConstant responseEnergyConstant
  positivity

theorem weighted_profile_square {Color : Type*} [Fintype Color] (law : FiniteDist Color) (density : Color → ℝ) :
    profileSquareNorm law.weight (fun color => law.weight color * density color) = law.l2Sq density := by
  unfold profileSquareNorm FiniteDist.l2Sq FiniteDist.expectation
  apply Finset.sum_congr rfl
  intro color _
  by_cases hc : law.weight color = 0
  · simp only [hc, zero_mul, zero_pow (by omega : 2 ≠ 0), zero_div]
  · field_simp

/-- One actually constructed chart family works uniformly for every legal
fixed root and queue and every canonical primary density. Its entire signed
four-output polynomial has the required scale, not only a fixed truncation. -/
theorem actual_primary_fock_energy_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      ∃ charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark,
      (∀ mark attached first second, publicChartRaw cutoffScale parameter mark (charts mark) attached first second =
        conditionalJointOutput cutoffScale parameter mark attached first second) ∧
      ∀ attachedRoot compensatorRoot queue : ℤ,
        |attachedRoot| ≤ (v7RootCutoff parameter : ℤ) →
        |compensatorRoot| ≤ (v7RootCutoff parameter : ℤ) → |queue| ≤ (queueCutoff parameter : ℤ) →
      ∀ density : Fin (Parameters.modulus parameter) → ℝ,
        (actualPrimaryLaw cutoffScale parameter (beta parameter)).expectation density = 0 →
      BlockProducts.taggedCoefficientEnergy (actualReferenceLaw cutoffScale parameter (beta parameter))
        (actualPairedDensityChannel cutoffScale parameter (beta parameter) charts attachedRoot compensatorRoot queue density)
        (Parameters.dimension parameter) ((parameter : ℝ) ^ 2) ≤
          (Real.sqrt primaryFockEnergyConstant / (parameter : ℝ) ^ 15) ^ 2 *
            (actualPrimaryLaw cutoffScale parameter (beta parameter)).l2Sq density := by
  filter_upwards [actual_paired_degree_budgets_eventually cutoffScale hscale beta hbeta,
    eventually_ge_atTop 2] with parameter hb hp
  obtain ⟨charts, hcharts, hbudget⟩ := hb
  refine ⟨charts, hcharts, ?_⟩
  intro ar cr queue har hcr hqueue density hd
  let law := actualPrimaryLaw cutoffScale parameter (beta parameter)
  let profile := fun color => law.weight color * density color
  have hm : ∑ color, profile color = 0 := hd
  obtain ⟨hmass, hfirst, hhigher⟩ := hbudget ar cr queue har hcr hqueue profile hm
  have henergy : profileSquareNorm law.weight profile = law.l2Sq density := weighted_profile_square law density
  change _ ≤ _ * profileSquareNorm law.weight profile at hfirst
  change ∀ degree, _ ≤ _ * profileSquareNorm law.weight profile at hhigher
  rw [henergy] at hfirst
  simp_rw [henergy] at hhigher
  let scale := (parameter : ℝ) ^ 2 / Real.sqrt (Parameters.dimension parameter)
  have hx : (1 : ℝ) ≤ parameter := by exact_mod_cast (by omega : 1 ≤ parameter)
  have hx0 : (0 : ℝ) < parameter := lt_of_lt_of_le (by norm_num) hx
  have hs0 : 0 ≤ scale := by dsimp only [scale]; positivity
  have hs : scale ≤ 2 / (parameter : ℝ) ^ 28 := by
    apply le_trans _ (actualFockScale_le parameter hp)
    change scale ≤ Real.sqrt 2 * scale
    have hsqrt : 1 ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    nlinarith only [mul_le_mul_of_nonneg_right hsqrt hs0]
  have hs1 : scale ≤ 1 := hs.trans ((div_le_one (pow_pos hx0 28)).2
    ((show (2 : ℝ) ≤ parameter by exact_mod_cast hp).trans (le_self_pow₀ hx (by norm_num : 28 ≠ 0))))
  have hh := four_output_fock_energy_le (actualReferenceLaw cutoffScale parameter (beta parameter))
    (Parameters.dimension parameter) ((parameter : ℝ) ^ 2) (parameter : ℝ)
    (fixedPairedChartRaw cutoffScale parameter (beta parameter) charts ar cr queue profile) hmass
    fixedResponseEnergyConstant 409600 (law.l2Sq density)
    (by unfold fixedResponseEnergyConstant responseEnergyConstant; positivity) (by norm_num)
    (law.l2Sq_nonneg density) hx hs0 hs1 hs hfirst (fun degree _ _ => hhigher degree)
  change BlockProducts.taggedCoefficientEnergy _
    (fixedPairedChartRaw cutoffScale parameter (beta parameter) charts ar cr queue profile) _ _ ≤ _
  apply hh.trans_eq
  simp only [div_pow, Real.sq_sqrt primaryFockEnergyConstant_pos.le, ← pow_mul]
  rfl

end
end AFT.V7Calibration
