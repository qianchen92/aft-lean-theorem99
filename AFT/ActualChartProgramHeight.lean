import AFT.ActualChartProgram
import AFT.ChartProgramHeight

/-! # Concrete polynomial dimensions and operand heights of the actual chart program -/
namespace AFT.BoundaryCalibration
open RationalNumerics V7Calibration
open scoped BigOperators

 def actualChartCountBound (n : ℕ) : ℕ := 8*n^120
 def actualChartFeatureBound (constant n : ℕ) : ℕ := 9*(constant+1)^2*n^4
 def actualChartWeightHeight (constant n : ℕ) : ℕ :=
   chartWeightHeight (actualChartCountBound n) (2*n^40) (actualChartFeatureBound constant n)
     (100+actualChartFeatureBound constant n) n

 theorem finiteProtectedAtom_height (cutoff : ℕ) :
    HeightBound (finiteProtectedAtom cutoff) (100+(2*cutoff+1)*(2*cutoff+1)) := by
   have hh := HeightBound.one.div ((HeightBound.nat_coarse 100).mul (HeightBound.nat_coarse ((2*cutoff+1)*(2*cutoff+1))))
   simpa only [finiteProtectedAtom,Nat.cast_ofNat,Nat.zero_add] using hh

 theorem actual_chart_array_bounds (constant n : ℕ) (hn : 2≤n) :
    chartProgramModulus n≤2*n^40 ∧
    chartProgramModulus n*(chartProgramModulus n*chartProgramModulus n)≤actualChartCountBound n ∧
    (2*chartProgramCutoff constant n+1)*(2*chartProgramCutoff constant n+1)≤actualChartFeatureBound constant n := by
   have hq : chartProgramModulus n≤2*n^40 := by
     rw [chartProgramModulus,ParameterProgram.modulus_value]
     simpa only [Parameters.security_eq n hn] using (Parameters.modulus_bounds n).2
   have hc : chartProgramCutoff constant n≤constant*n^2 :=
     (Nat.sub_le _ _).trans (actualLegCutoffProgram_le constant n)
   have hn1 : 1≤n^2 := one_le_pow₀ (by omega : 1≤n)
   have ha : 2*chartProgramCutoff constant n+1≤3*(constant+1)*n^2 := by nlinarith
   refine ⟨hq,?_,?_⟩
   · calc
       _ ≤ (2*n^40)*((2*n^40)*(2*n^40)) := Nat.mul_le_mul hq (Nat.mul_le_mul hq hq)
       _ = _ := by unfold actualChartCountBound;ring
   · calc
       _ ≤ (3*(constant+1)*n^2)*(3*(constant+1)*n^2) := Nat.mul_le_mul ha ha
       _ = _ := by unfold actualChartFeatureBound;ring

 theorem chartWeightHeight_mono {charts charts' colors colors' features features' atomBits atomBits' steps steps' : ℕ}
    (hc : charts≤charts') (hq : colors≤colors') (hf : features≤features') (ha : atomBits≤atomBits') (hs : steps≤steps') :
    chartWeightHeight charts colors features atomBits steps≤chartWeightHeight charts' colors' features' atomBits' steps' := by
   unfold chartWeightHeight chartIterateHeight chartStoredHeight chartProjectionHeight chartFeatureHeight chartConditionalHeight chartExpectationHeight
   gcongr

 theorem actual_chart_raw_weight_height (constant n : ℕ) (hn : 2≤n)
    (boundary baseline : ℤ) (mark : Fin (chartProgramModulus n)) (steps : ℕ) (hsteps : steps≤n)
    (point : Fin (chartProgramModulus n*(chartProgramModulus n*chartProgramModulus n))) :
    let cutoff := chartProgramCutoff constant n
    let modulus := chartProgramModulus n
    let feature := finiteProtectedFeatures cutoff modulus
    let allowed := finiteProtectedPalettes cutoff modulus boundary baseline
    HeightBound ((markedChartWeightProgram (modulus*(modulus*modulus)) modulus ((2*cutoff+1)*(2*cutoff+1))
      feature allowed (finiteMarkedSafe feature (finiteAffineScale modulus) allowed)
      (finiteMarkedFiber feature (finiteAffineScale modulus) allowed (finiteProtectedMark cutoff) mark)
      (finiteProtectedMark cutoff) (finiteProtectedAtom cutoff) steps).get point) (actualChartWeightHeight constant n) := by
   dsimp only
   apply (markedChartWeightProgram_height _ _ _ _ steps _ _ _ _ _ _
     (finiteProtectedAtom_height (chartProgramCutoff constant n)) point).mono
   have hb := actual_chart_array_bounds constant n hn
   exact chartWeightHeight_mono hb.2.1 hb.1 hb.2.2 (Nat.add_le_add_left hb.2.2 100) hsteps

 theorem actual_chart_fair_bit_count (constant n : ℕ) (hn : 2≤n) :
    n+chartProgramModulus n*(chartProgramModulus n*chartProgramModulus n)+1≤10*n^120 := by
   have hh := (actual_chart_array_bounds constant n hn).2.1
   have hp : n≤n^120 := by simpa using Nat.pow_le_pow_right (by omega : 1≤n) (show 1≤120 by decide)
   have h1 : 1≤n^120 := one_le_pow₀ (by omega : 1≤n)
   unfold actualChartCountBound at hh
   omega

 theorem actual_chart_cached_iteration_work (constant n : ℕ) (hn : 2≤n) :
    2*cachedIterationWork (chartProgramModulus n*(chartProgramModulus n*chartProgramModulus n)) n≤272*n^241 := by
   have hh := (actual_chart_array_bounds constant n hn).2.1
   have hp : n^120≤n^240 := Nat.pow_le_pow_right (by omega : 1≤n) (show 120≤240 by decide)
   unfold cachedIterationWork
   calc
     _ ≤ 2*(n*(2*(8*n^120)^2+8*n^120)) := by unfold actualChartCountBound at hh;gcongr
     _ ≤ 2*(n*(128*n^240+8*n^240)) := by
       have he : 2*(8*n^120)^2=128*n^240 := by ring
       rw [he]
       gcongr
     _ = _ := by ring

end AFT.BoundaryCalibration
