import AFT.FiniteChartSemantics

/-! # Closed executable public chart draws decoded to the actual physical F³ alphabet -/
namespace AFT.BoundaryCalibration
open V7Calibration GaussianSource
open scoped BigOperators

def actualPhysicalChartDraw (constant n : ℕ) (boundary baseline : ℤ) (steps bits : ℕ) :
    Fin (Parameters.modulus n) →
      (Fin (bits+Parameters.modulus n*(Parameters.modulus n*Parameters.modulus n)+1) → Fin 2) →
        Chart (ZMod (Parameters.modulus n)) :=
  cast (congrArg (fun modulus => Fin modulus →
    (Fin (bits+modulus*(modulus*modulus)+1) → Fin 2) → Chart (ZMod modulus))
      (show chartProgramModulus n=Parameters.modulus n from ParameterProgram.modulus_value n))
    (fun mark word => finiteChartEquiv (chartProgramModulus n)
      (safeFiniteAffineChartDraw (chartProgramCutoff constant n) (chartProgramModulus n) boundary baseline mark steps bits word))

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

private theorem chartDraw_transport (cutoff cutoff' modulus modulus' : ℕ)
    [NeZero modulus] [Fact modulus.Prime] [NeZero modulus'] [Fact modulus'.Prime]
    (boundary baseline : ℤ) (steps bits : ℕ) (hc : cutoff=cutoff') (hq : modulus=modulus') :
    cast (congrArg (fun q => Fin q → (Fin (bits+q*(q*q)+1) → Fin 2) → Chart (ZMod q)) hq)
      (fun mark word => finiteChartEquiv modulus
        (safeFiniteAffineChartDraw cutoff modulus boundary baseline mark steps bits word))=
      (fun mark word => finiteChartEquiv modulus'
        (safeFiniteAffineChartDraw cutoff' modulus' boundary baseline mark steps bits word)) := by
  subst cutoff'
  subst modulus'
  rfl

 theorem actualPhysicalChartDraw_eq (constant n : ℕ) (boundary baseline : ℤ) (steps bits : ℕ)
    (mark : Fin (Parameters.modulus n))
    (word : Fin (bits+Parameters.modulus n*(Parameters.modulus n*Parameters.modulus n)+1) → Fin 2) :
    actualPhysicalChartDraw constant n boundary baseline steps bits mark word=
      finiteChartEquiv (Parameters.modulus n)
        (safeFiniteAffineChartDraw (legCutoff (constant : ℝ) n-1) (Parameters.modulus n) boundary baseline mark steps bits word) := by
  have hh := chartDraw_transport (chartProgramCutoff constant n) (legCutoff (constant : ℝ) n-1)
    (chartProgramModulus n) (Parameters.modulus n) boundary baseline steps bits
    (by unfold chartProgramCutoff;rw [actualLegCutoffProgram_eq]) (ParameterProgram.modulus_value n)
  exact congrFun (congrFun hh mark) word

end
end AFT.BoundaryCalibration
