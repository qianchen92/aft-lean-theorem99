import AFT.MarkedChartLaw
import AFT.BoundaryChartParameters
import AFT.RootConvolutionProgram

/-! # Explicit array indexing of the actual affine F³ chart and protected inputs -/
namespace AFT.BoundaryCalibration
open scoped BigOperators

/-- The order is base, scale, shear, as in the physical affine chart. -/
def finiteChartEquiv (modulus : ℕ) [NeZero modulus] :
    Fin (modulus*(modulus*modulus)) ≃ Chart (ZMod modulus) :=
  finProdFinEquiv.symm.trans ((ZMod.finEquiv modulus).toEquiv.prodCongr
    (finProdFinEquiv.symm.trans ((ZMod.finEquiv modulus).toEquiv.prodCongr (ZMod.finEquiv modulus).toEquiv)))

def finiteInputEquiv (cutoff : ℕ) :
    Fin ((2*cutoff+1)*(2*cutoff+1)) ≃ GaussianSource.Window cutoff × GaussianSource.Window cutoff :=
  finProdFinEquiv.symm.trans ((FiniteConvolutionProgram.windowIndexEquiv cutoff).prodCongr
    (FiniteConvolutionProgram.windowIndexEquiv cutoff))

def finiteAffineFeature (modulus : ℕ) [NeZero modulus] [Fact modulus.Prime] (first second : ZMod modulus)
    (chart : Fin (modulus*(modulus*modulus))) : Fin modulus :=
  (ZMod.finEquiv modulus).symm (feature first second (finiteChartEquiv modulus chart))

def finiteAffineScale (modulus : ℕ) [NeZero modulus]
    (chart : Fin (modulus*(modulus*modulus))) : Fin modulus :=
  (ZMod.finEquiv modulus).symm (finiteChartEquiv modulus chart).2.1

def finiteProtectedFeatures (cutoff modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]
    (index : Fin ((2*cutoff+1)*(2*cutoff+1))) : Fin (modulus*(modulus*modulus)) → Fin modulus :=
  finiteAffineFeature modulus ((finiteInputEquiv cutoff index).1 : ℤ) ((finiteInputEquiv cutoff index).2 : ℤ)

def finiteProtectedPalettes (cutoff modulus : ℕ) (boundary baseline : ℤ)
    (index : Fin ((2*cutoff+1)*(2*cutoff+1))) : Finset (Fin modulus) :=
  TrimmedSlice.paletteSlice modulus boundary (baseline-((finiteInputEquiv cutoff index).2 : ℤ))

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable (modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]

 theorem finiteAffineFeature_uniform (first second : ZMod modulus) :
    (FiniteDist.uniform (Fin (modulus*(modulus*modulus)))).map (finiteAffineFeature modulus first second)=
      FiniteDist.uniform (Fin modulus) := by
  calc
    _ = (((FiniteDist.uniform (Fin (modulus*(modulus*modulus)))).map (finiteChartEquiv modulus)).map
      (feature first second)).map (ZMod.finEquiv modulus).toEquiv.symm := by
      simp only [FiniteDist.map_map]
      rfl
    _ = _ := by
      rw [FiniteDist.uniform_map_equiv,feature_uniform]
      exact FiniteDist.uniform_map_equiv (ZMod.finEquiv modulus).toEquiv.symm

 theorem finiteAffineScale_uniform :
    (FiniteDist.uniform (Fin (modulus*(modulus*modulus)))).map (finiteAffineScale modulus)=
      FiniteDist.uniform (Fin modulus) := by
  calc
    _ = (((FiniteDist.uniform (Fin (modulus*(modulus*modulus)))).map (finiteChartEquiv modulus)).map
      (fun chart => chart.2.1)).map (ZMod.finEquiv modulus).toEquiv.symm := by
      simp only [FiniteDist.map_map]
      rfl
    _ = _ := by
      rw [FiniteDist.uniform_map_equiv,scale_uniform]
      exact FiniteDist.uniform_map_equiv (ZMod.finEquiv modulus).toEquiv.symm

 theorem finiteAffineFeature_pair_uniform (first second : ZMod modulus × ZMod modulus) (hne : first≠second) :
    (FiniteDist.uniform (Fin (modulus*(modulus*modulus)))).map
      (fun chart => (finiteAffineFeature modulus first.1 first.2 chart,finiteAffineFeature modulus second.1 second.2 chart))=
      (FiniteDist.uniform (Fin modulus)).prod (FiniteDist.uniform (Fin modulus)) := by
  calc
    _ = (((FiniteDist.uniform (Fin (modulus*(modulus*modulus)))).map (finiteChartEquiv modulus)).map
      (fun chart => (feature first.1 first.2 chart,feature second.1 second.2 chart))).map
        ((ZMod.finEquiv modulus).toEquiv.symm.prodCongr (ZMod.finEquiv modulus).toEquiv.symm) := by
      simp only [FiniteDist.map_map]
      rfl
    _ = _ := by
      rw [FiniteDist.uniform_map_equiv,feature_pair_uniform first second hne,FiniteDist.prod_map_equiv,
        FiniteDist.uniform_map_equiv]

 theorem finiteAffineFeature_scale_uniform (first second : ZMod modulus) :
    (FiniteDist.uniform (Fin (modulus*(modulus*modulus)))).map
      (fun chart => (finiteAffineFeature modulus first second chart,finiteAffineScale modulus chart))=
      (FiniteDist.uniform (Fin modulus)).prod (FiniteDist.uniform (Fin modulus)) := by
  calc
    _ = (((FiniteDist.uniform (Fin (modulus*(modulus*modulus)))).map (finiteChartEquiv modulus)).map
      (fun chart => (feature first second chart,chart.2.1))).map
        ((ZMod.finEquiv modulus).toEquiv.symm.prodCongr (ZMod.finEquiv modulus).toEquiv.symm) := by
      simp only [FiniteDist.map_map]
      rfl
    _ = _ := by
      rw [FiniteDist.uniform_map_equiv,feature_scale_uniform first second,FiniteDist.prod_map_equiv,
        FiniteDist.uniform_map_equiv]

 theorem finiteProtectedFeatures_pair_uniform (cutoff : ℕ) (hsize : 2*cutoff < modulus)
    (i j : Fin ((2*cutoff+1)*(2*cutoff+1))) (hij : i≠j) :
    (FiniteDist.uniform (Fin (modulus*(modulus*modulus)))).map
      (fun chart => (finiteProtectedFeatures cutoff modulus i chart,finiteProtectedFeatures cutoff modulus j chart))=
      (FiniteDist.uniform (Fin modulus)).prod (FiniteDist.uniform (Fin modulus)) := by
  apply finiteAffineFeature_pair_uniform modulus
    (protectedInputs cutoff modulus (finiteInputEquiv cutoff i))
    (protectedInputs cutoff modulus (finiteInputEquiv cutoff j))
  intro heq
  exact hij ((finiteInputEquiv cutoff).injective
    (protectedInputs_injective cutoff modulus hsize heq))

end
end AFT.BoundaryCalibration
