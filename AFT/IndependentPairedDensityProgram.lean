import AFT.FixedPairedDensityProgram
import AFT.ActualRootMarginalProgram
import AFT.IndependentRootBlock

/-! # Actual independent-root paired numerator entries are computable -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics FiniteConvolutionProgram Filter
open scoped BigOperators

def independentPairedDensityProgram (constant n : ℕ) (beta : ℚ) (point : ℕ) (word : Fin 4 → ℕ) : ℚ :=
  ∑ firstRoot : Window (3*n^2-1),∑ secondRoot : Window (3*n^2-1),
    probabilityClamp (actualRootMarginalProgram n firstRoot)*
      probabilityClamp (actualRootMarginalProgram n secondRoot)*
      fixedPairedDensityProgram constant n beta firstRoot secondRoot 0 point word

noncomputable section
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
local instance independentPairedDensityProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def independentPairedDensityProgramError (n : ℕ) : ℝ :=
  (108*774^3 : ℝ)*(n : ℝ)^4*(actualRootMarginalError n+fixedPairedDensityProgramError n)

theorem independentPairedDensityProgramError_negligible : Negligible independentPairedDensityProgramError := by
  convert ((actualRootMarginalError_negligible.add fixedPairedDensityProgramError_negligible).mul_polynomial 4).const_mul
    (108*774^3) using 1
  funext n;unfold independentPairedDensityProgramError;ring

/-- The true root marginal is computed by the proved finite convolution
program. No root-marginal query oracle remains in the paired numerator. -/
theorem independent_paired_density_program_eventually (constant : ℕ) (hc : 1 ≤ constant) (beta : ℕ → ℚ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ (beta n : ℝ) ∧
      (beta n : ℝ) ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily constant n mark,
    (∀ mark attached first second,publicChartRaw constant n mark (charts mark) attached first second=
      conditionalJointOutput constant n mark attached first second) →
    ∀ (point : Fin (Parameters.modulus n)) (word : Fin 4 → Fin (Parameters.modulus n)),
      |(independentPairedDensityProgram constant n (beta n) point.val (fun slot => (word slot).val) : ℝ)-
        independentPairedNumerator constant n (beta n) charts
          (fun color => (actualPrimaryLaw constant n (beta n)).weight color*(Pi.single point (1 : ℝ) : Fin (Parameters.modulus n) → ℝ) color) word| ≤
        independentPairedDensityProgramError n := by
  filter_upwards [actual_paired_density_channel_program_eventually constant hc beta hbeta,
    fixed_paired_density_program_bounds_eventually constant hc beta hbeta,
    actual_primary_law_quarter_lower_eventually (constant : ℝ) (by exact_mod_cast hc) (fun n => beta n) hbeta,
    actual_root_marginal_program_eventually,eventually_ge_atTop 2] with n hd hb hp hr hn
  intro charts hcharts point word
  let root := rootMarginal (v7RootWidth n) (v7RootCutoff n) (Parameters.bodies n) (Parameters.bodies_positive n)
  let trueFactors := fun roots : Window (v7RootCutoff n) × Window (v7RootCutoff n) =>
    ![root.weight roots.1,root.weight roots.2,
      fixedPairedDensityColumn constant n (beta n) charts roots.1 roots.2 0 point word]
  let approximateFactors := fun roots : Window (v7RootCutoff n) × Window (v7RootCutoff n) =>
    ![(probabilityClamp (actualRootMarginalProgram n roots.1) : ℝ),
      (probabilityClamp (actualRootMarginalProgram n roots.2) : ℝ),
      (fixedPairedDensityProgram constant n (beta n) roots.1 roots.2 0 point.val (fun slot => (word slot).val) : ℝ)]
  let error := actualRootMarginalError n+fixedPairedDensityProgramError n
  have hroot (point : Window (v7RootCutoff n)) : |(point : ℤ)| ≤ (v7RootCutoff n : ℤ) :=
    abs_le.mpr (Finset.mem_Icc.mp point.property)
  have hp0 (color) : (actualPrimaryLaw constant n (beta n)).weight color ≠ 0 := by
    have hq : (0 : ℝ) < Parameters.modulus n := by exact_mod_cast (Parameters.modulus_prime n).pos
    exact (lt_of_lt_of_le (by positivity : (0 : ℝ) < 1/(4*Parameters.modulus n)) (hp color)).ne'
  have hd' (roots : Window (v7RootCutoff n) × Window (v7RootCutoff n)) :
      |(fixedPairedDensityProgram constant n (beta n) roots.1 roots.2 0 point.val (fun slot => (word slot).val) : ℝ)-
        fixedPairedDensityColumn constant n (beta n) charts roots.1 roots.2 0 point word| ≤ fixedPairedDensityProgramError n := by
    rw [fixedPairedDensityColumn_exact _ _ _ _ _ _ _ _ _ hp0]
    exact hd charts hcharts roots.1 roots.2 0 (hroot roots.1) (by simp) point word
  have he0 : 0 ≤ actualRootMarginalError n := (abs_nonneg _).trans (hr (windowZero _))
  have he1 : 0 ≤ fixedPairedDensityProgramError n := (abs_nonneg _).trans (hd' (windowZero _,windowZero _))
  have hprob (point : Window (v7RootCutoff n)) : |root.weight point| ≤ 1 := by
    rw [abs_of_nonneg (root.nonneg _)]
    exact root.atom_le_one _
  have happ (point : Window (v7RootCutoff n)) : |(probabilityClamp (actualRootMarginalProgram n point) : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (probabilityClamp_bounds _).1]
    exact (probabilityClamp_bounds _).2
  have hre (point : Window (v7RootCutoff n)) :
      |(probabilityClamp (actualRootMarginalProgram n point) : ℝ)-root.weight point| ≤ actualRootMarginalError n :=
    (probabilityClamp_error _ _ (root.nonneg point) (root.atom_le_one point)).trans (hr point)
  have ht (roots : Window (v7RootCutoff n) × Window (v7RootCutoff n)) (slot : Fin 3) :
      |trueFactors roots slot| ≤ 774 := by
    fin_cases slot
    · exact (hprob roots.1).trans (by norm_num)
    · exact (hprob roots.2).trans (by norm_num)
    · exact ((hb charts hcharts roots.1 roots.2 0 (hroot roots.1) (by simp) point word).1).trans (by norm_num)
  have ha (roots : Window (v7RootCutoff n) × Window (v7RootCutoff n)) (slot : Fin 3) :
      |approximateFactors roots slot| ≤ 774 := by
    fin_cases slot
    · exact (happ roots.1).trans (by norm_num)
    · exact (happ roots.2).trans (by norm_num)
    · exact (hb charts hcharts roots.1 roots.2 0 (hroot roots.1) (by simp) point word).2
  have he (roots : Window (v7RootCutoff n) × Window (v7RootCutoff n)) (slot : Fin 3) :
      |approximateFactors roots slot-trueFactors roots slot| ≤ error := by
    fin_cases slot
    · exact (hre roots.1).trans (le_add_of_nonneg_right he1)
    · exact (hre roots.2).trans (le_add_of_nonneg_right he1)
    · exact (hd' roots).trans (le_add_of_nonneg_left he0)
  have hh := finite_sum_product_perturbation (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
    trueFactors approximateFactors 774 1 error 0 (by norm_num) (by norm_num) (add_nonneg he0 he1)
    (by norm_num) (fun _ => by norm_num) (fun _ => by simp) ht ha he
  simp only [Fin.prod_univ_three,one_mul,zero_add,Fintype.card_fin] at hh
  have hcast : (independentPairedDensityProgram constant n (beta n) point.val (fun slot => (word slot).val) : ℝ)=
      ∑ roots,approximateFactors roots 0*approximateFactors roots 1*approximateFactors roots 2 := by
    simp only [independentPairedDensityProgram,Rat.cast_sum,Rat.cast_mul,Fintype.sum_prod_type]
    rfl
  have hexact : independentPairedNumerator constant n (beta n) charts
      (fun color => (actualPrimaryLaw constant n (beta n)).weight color*(Pi.single point (1 : ℝ) : Fin (Parameters.modulus n) → ℝ) color) word=
      ∑ roots,trueFactors roots 0*trueFactors roots 1*trueFactors roots 2 := by
    simp only [independentPairedNumerator,actualJointPairedNumerator,pairedRootReference,FiniteDist.prod_weight]
    apply Finset.sum_congr rfl
    intro roots _
    rw [show trueFactors roots 2=fixedPairedDensityColumn constant n (beta n) charts roots.1 roots.2 0 point word from rfl,
      fixedPairedDensityColumn_exact _ _ _ _ _ _ _ _ _ hp0]
    rfl
  rw [hcast,hexact]
  apply hh.trans
  have hcard : (Fintype.card (Window (v7RootCutoff n)) : ℝ) ≤ 6*(n : ℝ)^2 := by
    rw [←Fintype.card_congr (windowIndexEquiv _),Fintype.card_fin]
    unfold v7RootCutoff
    have h : 2*(3*n^2-1)+1 ≤ 6*n^2 := by
      have : 4 ≤ n^2 := by nlinarith
      omega
    exact_mod_cast h
  simp only [Fintype.card_prod,Nat.cast_mul]
  change (Fintype.card (Window (v7RootCutoff n)) : ℝ)*(Fintype.card (Window (v7RootCutoff n)) : ℝ)*
    ((3 : ℕ)*error)*774^3 ≤ _
  calc
    _ ≤ (6*(n : ℝ)^2)*(6*(n : ℝ)^2)*((3 : ℕ)*error)*774^3 := by gcongr
    _ = independentPairedDensityProgramError n := by unfold independentPairedDensityProgramError;dsimp only [error];norm_num;ring

end
end AFT.V7Calibration
