import AFT.FixedPairedKernelProgram
import AFT.ActualCanonicalBasisProgram
import AFT.NumericalSelectedCoefficient
import AFT.PrimaryLawLower
import AFT.MixedAveraging

/-! # Rational entries of the actual signed paired-density channel -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators

def fixedPairedDensityProgram (constant n : ℕ) (beta : ℚ)
    (attachedRoot compensatorRoot queue : ℤ) (point : ℕ) (word : Fin 4 → ℕ) : ℚ :=
  ∑ mark∈Finset.range (ParameterProgram.modulus n).value,
    ∑ center∈Finset.range (ParameterProgram.modulus n).value,
      actualInputProbabilityProgram constant n beta true mark*
        actualInputProbabilityProgram constant n beta false center*
        actualPairedMatrixProgram constant n beta point mark center*
        fixedPairedKernelProgram constant n beta attachedRoot compensatorRoot queue mark center word

noncomputable section
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
local instance fixedPairedDensityProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def fixedPairedDensityColumn (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (attachedRoot compensatorRoot queue : ℤ) (point : Fin (Parameters.modulus n))
    (word : Fin 4 → Fin (Parameters.modulus n)) : ℝ :=
  ∑ input : Fin (Parameters.modulus n) × Fin (Parameters.modulus n),
    (actualPrimaryLaw C n beta).weight input.1*(actualBodyLaw C n beta).weight input.2*
      pairedPublicMatrix (actualPrimaryLaw C n beta) (actualBodyLaw C n beta)
        (fun color position => publicAnchorKernel (Parameters.modulus n) (Parameters.anchorWidth n) color position.val)
        (v7Activation C n) point input*
      fixedPairedKernel C n beta charts attachedRoot compensatorRoot queue input word

theorem fixedPairedDensityColumn_exact (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (attachedRoot compensatorRoot queue : ℤ) (point : Fin (Parameters.modulus n))
    (word : Fin 4 → Fin (Parameters.modulus n))
    (hp : ∀ color,(actualPrimaryLaw C n beta).weight color ≠ 0) :
    fixedPairedDensityColumn C n beta charts attachedRoot compensatorRoot queue point word=
      actualPairedDensityChannel C n beta charts attachedRoot compensatorRoot queue (Pi.single point 1) word := by
  have hs := congrFun (pairedPublicDensity_eq_lift (actualPrimaryLaw C n beta) (actualBodyLaw C n beta)
    (fun color position => publicAnchorKernel (Parameters.modulus n) (Parameters.anchorWidth n) color position.val)
    (v7Activation C n) (Pi.single point 1) hp)
  rw [pairedPublicDensity_single] at hs
  simp only [fixedPairedDensityColumn,Fintype.sum_prod_type,actualPairedDensityChannel_apply,
    fixedPairedChartRaw,fixedPairedKernel,hs]
  apply Finset.sum_congr rfl
  intro mark _
  apply Finset.sum_congr rfl
  intro center _
  ring

def fixedPairedDensityProgramError (n : ℕ) : ℝ :=
  (16*774^4 : ℝ)*(n : ℝ)^80*
    (actualInputProbabilityProgramError n+actualPairedMatrixProgramError n+fixedPairedKernelProgramError n)

theorem fixedPairedDensityProgramError_negligible : Negligible fixedPairedDensityProgramError := by
  convert (((actualInputProbabilityProgramError_negligible.add actualPairedMatrixProgramError_negligible).add
    fixedPairedKernelProgramError_negligible).mul_polynomial 80).const_mul (16*774^4) using 1
  funext n;unfold fixedPairedDensityProgramError;ring

theorem fixed_paired_density_column_program_eventually (constant : ℕ) (hc : 1 ≤ constant) (beta : ℕ → ℚ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ (beta n : ℝ) ∧
      (beta n : ℝ) ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily constant n mark,
    (∀ mark attached first second,publicChartRaw constant n mark (charts mark) attached first second=
      conditionalJointOutput constant n mark attached first second) →
    ∀ (attachedRoot compensatorRoot queue : ℤ), |attachedRoot| ≤ (v7RootCutoff n : ℤ) →
      |queue| ≤ (queueCutoff n : ℤ) →
    ∀ (point : Fin (Parameters.modulus n)) (word : Fin 4 → Fin (Parameters.modulus n)),
      |(fixedPairedDensityProgram constant n (beta n) attachedRoot compensatorRoot queue point.val
          (fun slot => (word slot).val) : ℝ)-
        fixedPairedDensityColumn constant n (beta n) charts attachedRoot compensatorRoot queue point word| ≤
          fixedPairedDensityProgramError n := by
  filter_upwards [actual_input_probability_program_eventually constant hc beta hbeta,
    actual_paired_matrix_program_eventually constant hc beta hbeta,
    actual_paired_matrix_program_bounds_eventually constant hc beta hbeta,
    fixed_paired_kernel_program_eventually constant hc beta hbeta,eventually_ge_atTop 2]
    with n hp hm hmb hk hn
  intro charts hcharts attachedRoot compensatorRoot queue hroot hqueue point word
  let p := actualPrimaryLaw (constant : ℝ) n (beta n)
  let body := actualBodyLaw (constant : ℝ) n (beta n)
  let trueFactors := fun input : Fin (Parameters.modulus n) × Fin (Parameters.modulus n) =>
    ![p.weight input.1,body.weight input.2,
      pairedPublicMatrix p body (fun color position => publicAnchorKernel (Parameters.modulus n)
        (Parameters.anchorWidth n) color position.val) (v7Activation constant n) point input,
      fixedPairedKernel constant n (beta n) charts attachedRoot compensatorRoot queue input word]
  let approximateFactors := fun input : Fin (Parameters.modulus n) × Fin (Parameters.modulus n) =>
    ![(actualInputProbabilityProgram constant n (beta n) true input.1.val : ℝ),
      (actualInputProbabilityProgram constant n (beta n) false input.2.val : ℝ),
      (actualPairedMatrixProgram constant n (beta n) point.val input.1.val input.2.val : ℝ),
      (fixedPairedKernelProgram constant n (beta n) attachedRoot compensatorRoot queue input.1.val input.2.val
        (fun slot => (word slot).val) : ℝ)]
  let error := actualInputProbabilityProgramError n+actualPairedMatrixProgramError n+fixedPairedKernelProgramError n
  have he0 : 0 ≤ actualInputProbabilityProgramError n := (abs_nonneg _).trans (hp true point)
  have he1 : 0 ≤ actualPairedMatrixProgramError n := (abs_nonneg _).trans (hm point point point)
  have he2 : 0 ≤ fixedPairedKernelProgramError n := (abs_nonneg _).trans
    (hk charts hcharts attachedRoot compensatorRoot queue hroot hqueue (point,point) word)
  have htrue (input : Fin (Parameters.modulus n) × Fin (Parameters.modulus n)) (slot : Fin 4) :
      |trueFactors input slot| ≤ 774 := by
    fin_cases slot
    · change |p.weight input.1| ≤ _
      rw [abs_of_nonneg (p.nonneg _)]
      exact (p.atom_le_one _).trans (by norm_num)
    · change |body.weight input.2| ≤ _
      rw [abs_of_nonneg (body.nonneg _)]
      exact (body.atom_le_one _).trans (by norm_num)
    · exact ((hmb point input.1 input.2).1).trans (by norm_num)
    · change |fixedPairedKernel _ _ _ _ _ _ _ _ _| ≤ _
      rw [abs_of_nonneg (fixedPairedKernel_nonneg _ _ _ _ _ _ _ _ _)]
      exact (fixedPairedKernel_le_one _ _ _ _ _ _ _ _ _).trans (by norm_num)
  have happrox (input : Fin (Parameters.modulus n) × Fin (Parameters.modulus n)) (slot : Fin 4) :
      |approximateFactors input slot| ≤ 774 := by
    fin_cases slot
    · change |(probabilityClamp _ : ℝ)| ≤ _
      rw [abs_of_nonneg (probabilityClamp_bounds _).1]
      exact (probabilityClamp_bounds _).2.trans (by norm_num)
    · change |(probabilityClamp _ : ℝ)| ≤ _
      rw [abs_of_nonneg (probabilityClamp_bounds _).1]
      exact (probabilityClamp_bounds _).2.trans (by norm_num)
    · exact (hmb point input.1 input.2).2
    · change |(probabilityClamp _ : ℝ)| ≤ _
      rw [abs_of_nonneg (probabilityClamp_bounds _).1]
      exact (probabilityClamp_bounds _).2.trans (by norm_num)
  have herror (input : Fin (Parameters.modulus n) × Fin (Parameters.modulus n)) (slot : Fin 4) :
      |approximateFactors input slot-trueFactors input slot| ≤ error := by
    fin_cases slot
    · exact (hp true input.1).trans (by dsimp only [error];linarith)
    · exact (hp false input.2).trans (by dsimp only [error];linarith)
    · exact (hm point input.1 input.2).trans (by dsimp only [error];linarith)
    · exact (hk charts hcharts attachedRoot compensatorRoot queue hroot hqueue input word).trans (by dsimp only [error];linarith)
  have hterm := finite_sum_product_perturbation (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
    trueFactors approximateFactors 774 1 error 0 (by norm_num) (by norm_num)
    (by dsimp only [error];linarith) (by norm_num) (fun _ => by norm_num) (fun _ => by simp) htrue happrox herror
  simp only [one_mul,zero_add,Fin.prod_univ_four,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul] at hterm
  norm_num only [Nat.cast_ofNat] at hterm
  have hcast : (fixedPairedDensityProgram constant n (beta n) attachedRoot compensatorRoot queue point.val
      (fun slot => (word slot).val) : ℝ)=
      ∑ input,approximateFactors input 0*approximateFactors input 1*approximateFactors input 2*approximateFactors input 3 := by
    simp only [fixedPairedDensityProgram,Rat.cast_sum,Rat.cast_mul,ParameterProgram.modulus_value,
      Fintype.sum_prod_type]
    rw [←Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro mark _
    rw [←Fin.sum_univ_eq_sum_range]
    rfl
  rw [hcast]
  apply hterm.trans
  have hq : (Parameters.modulus n : ℝ) ≤ 2*(n : ℝ)^40 := by
    have hh := (Parameters.modulus_bounds n).2
    rw [Parameters.security_eq n hn] at hh
    exact_mod_cast hh
  have he : 0 ≤ error := by dsimp only [error];linarith
  change (Parameters.modulus n : ℝ)*(Parameters.modulus n : ℝ)*(4*error)*358892053776 ≤ _
  calc
    _ ≤ (2*(n : ℝ)^40)*(2*(n : ℝ)^40)*(4*error)*358892053776 := by gcongr
    _ = fixedPairedDensityProgramError n := by norm_num [fixedPairedDensityProgramError,error];ring

/-- The actual public-input average retains the constant paired-score bound. -/
theorem fixedPairedDensityColumn_abs_le (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (attachedRoot compensatorRoot queue : ℤ) (point : Fin (Parameters.modulus n))
    (word : Fin 4 → Fin (Parameters.modulus n))
    (hm : ∀ mark center,|pairedPublicMatrix (actualPrimaryLaw C n beta) (actualBodyLaw C n beta)
      (fun color position => publicAnchorKernel (Parameters.modulus n) (Parameters.anchorWidth n) color position.val)
      (v7Activation C n) point (mark,center)| ≤ 773) :
    |fixedPairedDensityColumn C n beta charts attachedRoot compensatorRoot queue point word| ≤ 773 := by
  let matrix := pairedPublicMatrix (actualPrimaryLaw C n beta) (actualBodyLaw C n beta)
    (fun color position => publicAnchorKernel (Parameters.modulus n) (Parameters.anchorWidth n) color position.val)
    (v7Activation C n) point
  have hh := FiniteDist.abs_average_le_bound ((actualPrimaryLaw C n beta).prod (actualBodyLaw C n beta))
    (fun input => matrix input*fixedPairedKernel C n beta charts attachedRoot compensatorRoot queue input word) 773
    (fun input => by
      rw [abs_mul,abs_of_nonneg (fixedPairedKernel_nonneg _ _ _ _ _ _ _ _ _)]
      exact (mul_le_mul (hm input.1 input.2) (fixedPairedKernel_le_one _ _ _ _ _ _ _ _ _)
        (fixedPairedKernel_nonneg _ _ _ _ _ _ _ _ _) (by norm_num)).trans_eq (mul_one _))
  simpa only [fixedPairedDensityColumn,FiniteDist.prod_weight,mul_assoc] using hh

theorem fixed_paired_density_program_bounds_eventually (constant : ℕ) (hc : 1 ≤ constant) (beta : ℕ → ℚ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ (beta n : ℝ) ∧
      (beta n : ℝ) ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily constant n mark,
    (∀ mark attached first second,publicChartRaw constant n mark (charts mark) attached first second=
      conditionalJointOutput constant n mark attached first second) →
    ∀ (attachedRoot compensatorRoot queue : ℤ), |attachedRoot| ≤ (v7RootCutoff n : ℤ) →
      |queue| ≤ (queueCutoff n : ℤ) →
    ∀ (point : Fin (Parameters.modulus n)) (word : Fin 4 → Fin (Parameters.modulus n)),
      |fixedPairedDensityColumn constant n (beta n) charts attachedRoot compensatorRoot queue point word| ≤ 773 ∧
      |(fixedPairedDensityProgram constant n (beta n) attachedRoot compensatorRoot queue point.val
        (fun slot => (word slot).val) : ℝ)| ≤ 774 := by
  filter_upwards [fixed_paired_density_column_program_eventually constant hc beta hbeta,
    actual_paired_matrix_program_bounds_eventually constant hc beta hbeta,
    fixedPairedDensityProgramError_negligible 0] with n he hm hsmall
  intro charts hcharts attachedRoot compensatorRoot queue hroot hqueue point word
  have ht := fixedPairedDensityColumn_abs_le (constant : ℝ) n (beta n) charts attachedRoot compensatorRoot queue point word
    (fun mark center => (hm point mark center).1)
  refine ⟨ht,?_⟩
  have hh := he charts hcharts attachedRoot compensatorRoot queue hroot hqueue point word
  have ha := abs_sub_abs_le_abs_sub
    (fixedPairedDensityProgram constant n (beta n) attachedRoot compensatorRoot queue point.val (fun slot => (word slot).val) : ℝ)
    (fixedPairedDensityColumn constant n (beta n) charts attachedRoot compensatorRoot queue point word)
  norm_num only [Nat.cast_zero,pow_zero,one_div_one] at hsmall
  have hsmall' := (le_abs_self _).trans hsmall
  linarith

/-- Exact physical identification discharges positivity from the actual
calibration, rather than leaving it as a numerical-oracle premise. -/
theorem actual_paired_density_channel_program_eventually (constant : ℕ) (hc : 1 ≤ constant) (beta : ℕ → ℚ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ (beta n : ℝ) ∧
      (beta n : ℝ) ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily constant n mark,
    (∀ mark attached first second,publicChartRaw constant n mark (charts mark) attached first second=
      conditionalJointOutput constant n mark attached first second) →
    ∀ (attachedRoot compensatorRoot queue : ℤ), |attachedRoot| ≤ (v7RootCutoff n : ℤ) →
      |queue| ≤ (queueCutoff n : ℤ) →
    ∀ (point : Fin (Parameters.modulus n)) (word : Fin 4 → Fin (Parameters.modulus n)),
      |(fixedPairedDensityProgram constant n (beta n) attachedRoot compensatorRoot queue point.val
          (fun slot => (word slot).val) : ℝ)-
        actualPairedDensityChannel constant n (beta n) charts attachedRoot compensatorRoot queue
          (Pi.single point 1) word| ≤ fixedPairedDensityProgramError n := by
  filter_upwards [fixed_paired_density_column_program_eventually constant hc beta hbeta,
    actual_primary_law_quarter_lower_eventually (constant : ℝ) (by exact_mod_cast hc) (fun n => beta n) hbeta]
    with n hh hp
  intro charts hcharts attachedRoot compensatorRoot queue hroot hqueue point word
  have hp0 (color) : (actualPrimaryLaw constant n (beta n)).weight color ≠ 0 := by
    have hq : (0 : ℝ) < Parameters.modulus n := by exact_mod_cast (Parameters.modulus_prime n).pos
    exact (lt_of_lt_of_le (by positivity : (0 : ℝ) < 1/(4*Parameters.modulus n)) (hp color)).ne'
  rw [←fixedPairedDensityColumn_exact _ _ _ _ _ _ _ _ _ hp0]
  exact hh charts hcharts attachedRoot compensatorRoot queue hroot hqueue point word

end
end AFT.V7Calibration
