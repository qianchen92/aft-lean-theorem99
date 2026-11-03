import CurrentAFT.FixedPairedFirst
import CurrentAFT.IndependentPairedReference
import AFT.FiniteDisintegration
import CurrentAFT.PositiveFirstCoefficient
import CurrentAFT.NormalizedLocalPolynomial

/-! # The independent-root local law is the genuine mixture of fixed-root laws -/
namespace CurrentAFT.IndependentReferenceEnergy

open AFT DiffuseProfiles ProposalPrimary ActualControls FirstHistogram LocalReferenceEnergy
  PairedReferenceEnergy FixedPairedFirst IndependentPairedReference PhysicalSynthesis
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw

abbrev Palette (security : ℕ) := ActualControls.Palette security
abbrev Roots (security : ℕ) := FirstHistogram.Scalar security × (ActualSeed security × ActualSeed security)

def rootLaw (security : ℕ) : FiniteDist (Roots security) :=
  (scalarLaw security).prod ((actualSeedLaw security).prod (actualSeedLaw security))

theorem independentControlLaw_mixture (security : ℕ) (group : Group security)
    (value : (Fin 4 → Palette security) → ℝ) :
    (independentControlLaw security group).expectation value =
      (rootLaw security).expectation (fun roots =>
        (fixedControlLaw security (actualBlur security roots.2.1)
          (actualBlur security roots.2.2) roots.1 group).expectation value) := by
  unfold independentControlLaw
  rw [FiniteDist.expectation_mix]
  simp only [FiniteDist.expectation_map, Function.comp_apply, FiniteDist.expectation_prod]
  rw [reference_scalar_disintegration]
  simp only [compensatorBodyLaw, attachmentBlurAt, FiniteDist.expectation_map,
    FiniteDist.expectation_mix, Function.comp_def]
  unfold rootLaw
  rw [FiniteDist.expectation_prod]
  apply congrArg (scalarLaw security).expectation
  funext scalar
  rw [FiniteDist.expectation_prod]
  have hfirst := FiniteDist.expectation_comm (pairAt security group.1 scalar) (actualSeedLaw security)
    (fun pair compSeed => (actualSeedLaw security).expectation (fun attachSeed =>
      (safeLaw security).expectation (fun center =>
        value (PhysicalBlockTensors.quadrupleEquiv.symm
          (shiftEquiv security (actualBlur security compSeed) group.2,
            (pair, shiftEquiv security (actualBlur security attachSeed + scalar.val) center))))))
  rw [hfirst]
  apply congrArg (actualSeedLaw security).expectation
  funext compSeed
  rw [FiniteDist.expectation_comm (pairAt security group.1 scalar) (actualSeedLaw security)]
  apply congrArg (actualSeedLaw security).expectation
  funext attachSeed
  simp only [fixedControlLaw, FiniteDist.expectation_map, Function.comp_def,
    FiniteDist.expectation_prod, pointLaw, FiniteDist.expectation_const, attachmentAt]

theorem independentSigned_mixture_expectation (security : ℕ) (score : Palette security → ℝ)
    (value : (Fin 4 → Palette security) → ℝ) :
    (∑ word, independentSignedMass security score word * value word) =
      (rootLaw security).expectation (fun roots =>
        ∑ word, pairedMassAt security (actualBlur security roots.2.1)
          (actualBlur security roots.2.2) roots.1 score word * value word) := by
  rw [independentSigned_expectation]
  simp_rw [independentControlLaw_mixture]
  simp only [← FiniteDist.expectation_const_mul]
  rw [FiniteDist.expectation_comm]
  apply congrArg (rootLaw security).expectation
  funext roots
  simp only [FiniteDist.expectation_const_mul]
  exact (fixedMass_expectation security _ _ roots.1 score value).symm

theorem independentSigned_mixture (security : ℕ) (score : Palette security → ℝ)
    (word : Fin 4 → Palette security) :
    independentSignedMass security score word = (rootLaw security).expectation (fun roots =>
      pairedMassAt security (actualBlur security roots.2.1) (actualBlur security roots.2.2) roots.1 score word) := by
  have h := independentSigned_mixture_expectation security score (fun sample => if sample = word then 1 else 0)
  simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] using h

/-- Convex averaging preserves the full joint four-coordinate energy,
including every cancellation in the score and every retained root. -/
theorem independentSigned_energy (security : ℕ) (score : Palette security → ℝ) :
    profileSquareNorm (FiniteDist.independent (fun _ : Fin 4 => uniformReference security)).weight
      (independentSignedMass security score) ≤
        (4128 * pairBudget security) * (primaryLaw security).expectation (fun color => score color ^ 2) := by
  let reference := FiniteDist.independent (fun _ : Fin 4 => uniformReference security)
  have hequal : independentSignedMass security score = fun word =>
      ∑ roots, (rootLaw security).weight roots *
        pairedMassAt security (actualBlur security roots.2.1) (actualBlur security roots.2.2) roots.1 score word := by
    funext word
    exact independentSigned_mixture security score word
  rw [hequal]
  have havg := profileSquareNorm_average_le (rootLaw security) reference.weight reference.nonneg
    (fun roots => pairedMassAt security (actualBlur security roots.2.1) (actualBlur security roots.2.2) roots.1 score)
  apply havg.trans
  calc
    _ ≤ ∑ roots, (rootLaw security).weight roots * ((4128 * pairBudget security) *
        (primaryLaw security).expectation (fun color => score color ^ 2)) := by
      apply Finset.sum_le_sum
      intro roots _
      exact mul_le_mul_of_nonneg_left (pairedMassAt_energy security _ _ roots.1 score) ((rootLaw security).nonneg roots)
    _ = _ := by rw [← Finset.sum_mul, (rootLaw security).sum_one, one_mul]

theorem fixedPositive_control (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : FirstHistogram.Scalar security) (word : Fin 4 → Palette security) :
    (PositiveFirstCoefficient.positiveFourLaw security compensatorRoot attachmentRoot scalar).weight word =
      ∑ group, (groupLaw security).weight group *
        (fixedControlLaw security compensatorRoot attachmentRoot scalar group).weight word := by
  rw [PositiveFirstCoefficient.positiveFour_weight]
  unfold PhysicalBlockTensors.compensatedTripleMass tripleMassAt signedPairAt
  rw [compensatorAt_channel]
  simp only [groupLaw, FiniteDist.prod_weight, Fintype.sum_prod_type,
    fixedControlLaw_weight, controlMass, mul_one, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro primary _
  apply Finset.sum_congr rfl
  intro center _
  ring

theorem independentPositive_mixture_expectation (security : ℕ)
    (value : (Fin 4 → Palette security) → ℝ) :
    (NormalizedLocalPolynomial.independentPositiveLaw security).expectation value =
      (rootLaw security).expectation (fun roots =>
        (PositiveFirstCoefficient.positiveFourLaw security (actualBlur security roots.2.1)
          (actualBlur security roots.2.2) roots.1).expectation value) := by
  rw [NormalizedLocalPolynomial.independentPositiveLaw, FiniteDist.expectation_mix]
  simp_rw [independentControlLaw_mixture]
  rw [FiniteDist.expectation_comm]
  apply congrArg (rootLaw security).expectation
  funext roots
  simp only [FiniteDist.expectation, fixedPositive_control, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

theorem independentPositive_mixture (security : ℕ) (word : Fin 4 → Palette security) :
    (NormalizedLocalPolynomial.independentPositiveLaw security).weight word =
      (rootLaw security).expectation (fun roots =>
        (PositiveFirstCoefficient.positiveFourLaw security (actualBlur security roots.2.1)
          (actualBlur security roots.2.2) roots.1).weight word) := by
  have h := independentPositive_mixture_expectation security (fun sample => if sample = word then 1 else 0)
  simpa only [FiniteDist.expectation, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] using h

theorem fixedPositive_energy (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : FirstHistogram.Scalar security) :
    profileSquareNorm (FiniteDist.independent (fun _ : Fin 4 => uniformReference security)).weight
      (PositiveFirstCoefficient.positiveFourLaw security compensatorRoot attachmentRoot scalar).weight ≤
        16 * pairBudget security := by
  let reference := FiniteDist.independent (fun _ : Fin 4 => uniformReference security)
  have hmass : (PositiveFirstCoefficient.positiveFourLaw security compensatorRoot attachmentRoot scalar).weight =
      PhysicalBlockTensors.compensatedTripleMass (compensatorAt security compensatorRoot).weight
        (tripleMassAt security attachmentRoot scalar (fun _ => 1)) :=
    funext (PositiveFirstCoefficient.positiveFour_weight security compensatorRoot attachmentRoot scalar)
  have hfactor := PhysicalBlockTensors.compensated_triple_density_energy (uniformReference security)
    (compensatorAt security compensatorRoot).weight (tripleMassAt security attachmentRoot scalar (fun _ => 1))
  change densitySquareNorm reference.weight (fun word => PhysicalBlockTensors.compensatedTripleMass
    (compensatorAt security compensatorRoot).weight (tripleMassAt security attachmentRoot scalar (fun _ => 1)) word /
      reference.weight word) = _ at hfactor
  rw [densityScore_square] at hfactor
  rw [hmass, hfactor]
  have hcomp := compensatorAt_energy security compensatorRoot
  have htriple := tripleMassAt_energy security attachmentRoot scalar (fun _ => 1)
  simp only [one_pow, FiniteDist.expectation_const, mul_one] at htriple
  have hnonneg := profileSquareNorm_nonneg (uniformReference security).weight
    (compensatorAt security compensatorRoot).weight (uniformReference security).nonneg
  calc
    _ ≤ profileSquareNorm (uniformReference security).weight (compensatorAt security compensatorRoot).weight *
        (4 * pairBudget security) := mul_le_mul_of_nonneg_left htriple hnonneg
    _ ≤ 4 * (4 * pairBudget security) := mul_le_mul_of_nonneg_right hcomp
      (mul_nonneg (by norm_num) (pairBudget_nonneg security))
    _ = _ := by ring

theorem independentPositive_energy (security : ℕ) :
    profileSquareNorm (FiniteDist.independent (fun _ : Fin 4 => uniformReference security)).weight
      (NormalizedLocalPolynomial.independentPositiveLaw security).weight ≤ 16 * pairBudget security := by
  let reference := FiniteDist.independent (fun _ : Fin 4 => uniformReference security)
  have hequal : (NormalizedLocalPolynomial.independentPositiveLaw security).weight = fun word =>
      ∑ roots, (rootLaw security).weight roots *
        (PositiveFirstCoefficient.positiveFourLaw security (actualBlur security roots.2.1)
          (actualBlur security roots.2.2) roots.1).weight word := by
    funext word
    exact independentPositive_mixture security word
  rw [hequal]
  apply (profileSquareNorm_average_le (rootLaw security) reference.weight reference.nonneg _).trans
  calc
    _ ≤ ∑ roots, (rootLaw security).weight roots * (16 * pairBudget security) := by
      apply Finset.sum_le_sum
      intro roots _
      exact mul_le_mul_of_nonneg_left (fixedPositive_energy security _ _ roots.1) ((rootLaw security).nonneg roots)
    _ = _ := by rw [← Finset.sum_mul, (rootLaw security).sum_one, one_mul]

end
end CurrentAFT.IndependentReferenceEnergy
