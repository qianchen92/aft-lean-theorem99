import AFT.FiniteChartPairOutput
import AFT.ActualChartProgramHeight

/-! # Actual legal public chart sampling with exact physical response and negligible finite-bit error -/
namespace AFT.BoundaryCalibration
open GaussianSource V7Calibration Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

 theorem actual_physical_chart_sampler_eventually (constant : ℕ) (hconstant : 1≤constant) :
    ∀ᶠ n : ℕ in atTop, ∀ boundary baseline : ℤ,
      0≤boundary → boundary≤Parameters.safeMargin n → |baseline|≤3*Parameters.anchorWidth n →
      ∀ mark : Fin (Parameters.modulus n),
      ∃ law : FiniteDist (Chart (ZMod (Parameters.modulus n))),
        ProtectedChartSupport (constant : ℝ) n boundary baseline mark law ∧
        (∀ input : V7Input (constant : ℝ) n,∀ first second : Fin (Parameters.modulus n),
          (chartPairOutput (constant : ℝ) n baseline law input).weight (first,second)=
            (1-if input=(windowZero _,windowZero _) then chartAtom (V7Input (constant : ℝ) n) else 0)*
              TrimmedSlice.orderedPairSlice (Parameters.modulus n) boundary (baseline-input.2) first second+
            (if input=(windowZero _,windowZero _) then chartAtom (V7Input (constant : ℝ) n) else 0)*(if first=mark then 1 else 0)*
              (if second=paletteEmbedding n ((Parameters.modulus n : ℤ)-1+baseline-input.2-mark.val) then 1 else 0)) ∧
        (∀ word : Fin (n+Parameters.modulus n*(Parameters.modulus n*Parameters.modulus n)+1) → Fin 2,
          let chart := actualPhysicalChartDraw constant n boundary baseline n n mark word
          chart.2.1≠0 ∧ ∀ input : V7Input (constant : ℝ) n,
            feature ((input.1 : ℤ) : ZMod (Parameters.modulus n)) ((input.2 : ℤ) : ZMod (Parameters.modulus n)) chart∈
              v7ProtectedPalettes (constant : ℝ) n boundary baseline input ∨
            (input=(windowZero _,windowZero _) ∧
              feature ((input.1 : ℤ) : ZMod (Parameters.modulus n)) ((input.2 : ℤ) : ZMod (Parameters.modulus n)) chart=
                (ZMod.finEquiv (Parameters.modulus n)) mark)) ∧
        (∑chart,|((FiniteDist.independent (fun _ : Fin (n+Parameters.modulus n*(Parameters.modulus n*Parameters.modulus n)+1) =>
          FiniteDist.uniform (Fin 2))).map (actualPhysicalChartDraw constant n boundary baseline n n mark)).weight chart-law.weight chart|)≤
            actualChartNumericalError n := by
  have hC : (1 : ℝ)≤constant := by exact_mod_cast hconstant
  have hclear := v7_primaryCalibration_clearance_eventually (constant : ℝ) hC (fun n => Parameters.safeMargin n)
    (Filter.Eventually.of_forall fun n => ⟨by positivity,le_rfl⟩)
  filter_upwards [v7_chart_budget_eventually (constant : ℝ) hC,hclear,eventually_ge_atTop 1] with n hbudget hclear hn
  intro boundary baseline hb0 hb1 hbase mark
  have hc := GaussianSource.legCutoff_positive (constant : ℝ) n hC hn
  have hi : 2*(legCutoff (constant : ℝ) n-1)<Parameters.modulus n := by omega
  have hb := hbudget boundary baseline hb0 hb1 hbase
  obtain ⟨law,hsupport,hmark,hother,herror⟩ :=
    finite_affine_chart_sampler (legCutoff (constant : ℝ) n-1) (Parameters.modulus n) boundary baseline mark hi (by
      simpa only [v7ProtectedPalettes,protectedInputs_card,pow_two,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using hb)
  have hs : ∀ point,point∉finiteAffineLegalSet (legCutoff (constant : ℝ) n-1) (Parameters.modulus n) boundary baseline mark → law.weight point=0 := by
    intro point hp
    exact hsupport point (fun hh => hp (Finset.mem_union_left _ hh)) (fun hh => hp (Finset.mem_union_right _ hh))
  have hlegal := finiteAffineChart_sampler_legal _ _ boundary baseline mark law hsupport
  refine ⟨law.map (finiteChartEquiv (Parameters.modulus n)),finiteChartLaw_protected _ _ _ _ mark law hs,?_,?_,?_⟩
  · exact finiteChartLaw_pair_output (constant : ℝ) n boundary baseline hb0 mark law hmark hother
  · intro word
    dsimp only
    rw [actualPhysicalChartDraw_eq]
    exact finiteAffineLegalSet_physical _ _ boundary baseline mark _ (hlegal.1 n n word)
  · have hsafebound := (hlegal.2 n n).trans ((herror n n hn).trans (finiteAffineChartDraw_error_diagonal n))
    have hmap := FiniteDist.l1_map_le
      ((FiniteDist.independent (fun _ : Fin (n+Parameters.modulus n*(Parameters.modulus n*Parameters.modulus n)+1) => FiniteDist.uniform (Fin 2))).map
        (safeFiniteAffineChartDraw (legCutoff (constant : ℝ) n-1) (Parameters.modulus n) boundary baseline mark n n)) law
      (finiteChartEquiv (Parameters.modulus n))
    have heq : (fun word => finiteChartEquiv (Parameters.modulus n)
        (safeFiniteAffineChartDraw (legCutoff (constant : ℝ) n-1) (Parameters.modulus n) boundary baseline mark n n word))=
        actualPhysicalChartDraw constant n boundary baseline n n mark := by
      funext word
      exact (actualPhysicalChartDraw_eq constant n boundary baseline n n mark word).symm
    rw [FiniteDist.map_map,heq] at hmap
    exact hmap.trans hsafebound

end
end AFT.BoundaryCalibration
