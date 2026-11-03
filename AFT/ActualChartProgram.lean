import AFT.FiniteAffineChartSampler
import AFT.ActualLegCutoffProgram
import AFT.ParameterProgram

/-! # The executable F³ chart sampler at the actual V7 parameters -/
namespace AFT.BoundaryCalibration
open V7Calibration Filter
open scoped BigOperators

/-- Both parameters are produced by finite integer programs. -/
def chartProgramModulus (n : ℕ) : ℕ := (ParameterProgram.modulus n).value
def chartProgramCutoff (constant n : ℕ) : ℕ := actualLegCutoffProgram constant n-1

instance chartProgramModulusNeZero (n : ℕ) : NeZero (chartProgramModulus n) :=
  ⟨by rw [chartProgramModulus,ParameterProgram.modulus_value];exact (Parameters.modulus_prime n).ne_zero⟩
instance chartProgramModulusPrime (n : ℕ) : Fact (chartProgramModulus n).Prime :=
  ⟨by rw [chartProgramModulus,ParameterProgram.modulus_value];exact Parameters.modulus_prime n⟩

def actualFiniteAffineChartDraw (constant n : ℕ) (boundary baseline : ℤ)
    (mark : Fin (chartProgramModulus n)) (steps bits : ℕ)
    (word : Fin (bits+chartProgramModulus n*(chartProgramModulus n*chartProgramModulus n)+1) → Fin 2) :
    Fin (chartProgramModulus n*(chartProgramModulus n*chartProgramModulus n)) :=
  finiteAffineChartDraw (chartProgramCutoff constant n) (chartProgramModulus n) boundary baseline mark steps bits word

noncomputable section
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

/-- Exact support and marginal specification, plus the law of the actual fair-bit program. -/
def FiniteAffineSamplerExists (cutoff modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]
    (boundary baseline : ℤ) (mark : Fin modulus) : Prop :=
    ∃ law : FiniteDist (Fin (modulus*(modulus*modulus))),
      (∀ point, point∉finiteMarkedSafe (finiteProtectedFeatures cutoff modulus) (finiteAffineScale modulus)
        (finiteProtectedPalettes cutoff modulus boundary baseline) →
        point∉finiteMarkedFiber (finiteProtectedFeatures cutoff modulus) (finiteAffineScale modulus)
          (finiteProtectedPalettes cutoff modulus boundary baseline) (finiteProtectedMark cutoff) mark → law.weight point=0) ∧
      (∀ color, (law.map (finiteProtectedFeatures cutoff modulus (finiteProtectedMark cutoff))).weight color=
        (1-(finiteProtectedAtom cutoff : ℝ))*
          (if color∈finiteProtectedPalettes cutoff modulus boundary baseline (finiteProtectedMark cutoff) then
            ((finiteProtectedPalettes cutoff modulus boundary baseline (finiteProtectedMark cutoff)).card : ℝ)⁻¹ else 0)+
          (finiteProtectedAtom cutoff : ℝ)*(if color=mark then 1 else 0)) ∧
      (∀ i, i≠finiteProtectedMark cutoff → ∀ color, (law.map (finiteProtectedFeatures cutoff modulus i)).weight color=
        if color∈finiteProtectedPalettes cutoff modulus boundary baseline i then
          ((finiteProtectedPalettes cutoff modulus boundary baseline i).card : ℝ)⁻¹ else 0) ∧
      (∀ steps bits : ℕ, 1≤steps →
        (∑point,|((FiniteDist.independent (fun _ : Fin (bits+modulus*(modulus*modulus)+1) => FiniteDist.uniform (Fin 2))).map
          (finiteAffineChartDraw cutoff modulus boundary baseline mark steps bits)).weight point-law.weight point|)≤
            8*(1/4 : ℝ)^steps+1/(2 : ℝ)^bits)

private theorem protected_budget_congr (firstCutoff secondCutoff firstModulus secondModulus : ℕ)
    [NeZero firstModulus] [NeZero secondModulus] (boundary baseline : ℤ)
    (hc : firstCutoff=secondCutoff) (hq : firstModulus=secondModulus) :
    affineDeletionBudget (protectedPalettes firstCutoff firstModulus boundary baseline)=
      affineDeletionBudget (protectedPalettes secondCutoff secondModulus boundary baseline) := by
  subst secondCutoff
  subst secondModulus
  rfl

 theorem actual_finite_affine_chart_sampler_eventually (constant : ℕ) (hconstant : 1≤constant) :
    ∀ᶠ n : ℕ in atTop, ∀ boundary baseline : ℤ,
      0≤boundary → boundary≤Parameters.safeMargin n → |baseline|≤3*Parameters.anchorWidth n →
      ∀ mark : Fin (chartProgramModulus n),
        FiniteAffineSamplerExists (chartProgramCutoff constant n) (chartProgramModulus n) boundary baseline mark := by
  have hC : (1 : ℝ)≤constant := by exact_mod_cast hconstant
  have hclear := v7_primaryCalibration_clearance_eventually (constant : ℝ) hC
    (fun n => Parameters.safeMargin n)
    (Filter.Eventually.of_forall fun n => ⟨by positivity,le_rfl⟩)
  filter_upwards [v7_chart_budget_eventually (constant : ℝ) hC,hclear,eventually_ge_atTop 1] with n hbudget hclear hn
  intro boundary baseline hb0 hb1 hbase mark
  have hc := GaussianSource.legCutoff_positive (constant : ℝ) n hC hn
  have hi : 2*chartProgramCutoff constant n < chartProgramModulus n := by
    rw [chartProgramCutoff,actualLegCutoffProgram_eq,chartProgramModulus,ParameterProgram.modulus_value]
    omega
  apply finite_affine_chart_sampler _ _ boundary baseline mark hi
  have hb := hbudget boundary baseline hb0 hb1 hbase
  convert hb using 1
  congr 1
  · simp only [chartProgramCutoff,actualLegCutoffProgram_eq,protectedInputs_card,Nat.cast_pow,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    ring
  · letI : NeZero (ParameterProgram.modulus n).value := chartProgramModulusNeZero n
    unfold chartProgramCutoff chartProgramModulus v7ProtectedPalettes
    exact protected_budget_congr _ _ _ _ boundary baseline
      (congrArg (fun cutoff : ℕ => cutoff-1) (actualLegCutoffProgram_eq constant n)) (ParameterProgram.modulus_value n)

end
end AFT.BoundaryCalibration
