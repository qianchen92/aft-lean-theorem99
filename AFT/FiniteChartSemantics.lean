import AFT.ChartLegalize
import AFT.ChartSupport

/-! # The sampled finite chart arrays have the actual physical chart semantics -/
namespace AFT.BoundaryCalibration
open GaussianSource
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

 theorem finiteProtectedFeatures_field (cutoff modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]
    (input : Fin ((2*cutoff+1)*(2*cutoff+1))) (point : Fin (modulus*(modulus*modulus))) :
    (ZMod.finEquiv modulus) (finiteProtectedFeatures cutoff modulus input point)=
      feature (((finiteInputEquiv cutoff input).1 : ℤ) : ZMod modulus) (((finiteInputEquiv cutoff input).2 : ℤ) : ZMod modulus) (finiteChartEquiv modulus point) := by
   simp only [finiteProtectedFeatures,finiteAffineFeature,RingEquiv.apply_symm_apply]

 theorem finiteProtectedPalettes_field (cutoff modulus : ℕ) [NeZero modulus]
    (boundary baseline : ℤ) (input : Fin ((2*cutoff+1)*(2*cutoff+1))) (color : Fin modulus) :
    color∈finiteProtectedPalettes cutoff modulus boundary baseline input ↔
      (ZMod.finEquiv modulus) color∈protectedPalettes cutoff modulus boundary baseline (finiteInputEquiv cutoff input) := by
   simp only [finiteProtectedPalettes,protectedPalettes,fieldPalette,Finset.mem_map,Equiv.toEmbedding_apply]
   constructor
   · intro hc
     exact ⟨color,hc,rfl⟩
   · rintro ⟨other,ho,he⟩
     exact (ZMod.finEquiv modulus).injective he ▸ ho

 theorem finiteAffineLegalSet_physical (cutoff modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]
    (boundary baseline : ℤ) (mark : Fin modulus) (point : Fin (modulus*(modulus*modulus)))
    (hp : point∈finiteAffineLegalSet cutoff modulus boundary baseline mark) :
    (finiteChartEquiv modulus point).2.1≠0 ∧
      ∀ input : Window cutoff × Window cutoff,
        feature ((input.1 : ℤ) : ZMod modulus) ((input.2 : ℤ) : ZMod modulus) (finiteChartEquiv modulus point)∈
          protectedPalettes cutoff modulus boundary baseline input ∨
        (input=(windowZero cutoff,windowZero cutoff) ∧
          feature ((input.1 : ℤ) : ZMod modulus) ((input.2 : ℤ) : ZMod modulus) (finiteChartEquiv modulus point)=(ZMod.finEquiv modulus) mark) := by
   have hscale : finiteAffineScale modulus point≠0 → (finiteChartEquiv modulus point).2.1≠0 := by
     intro hs hz
     exact hs (by simp [finiteAffineScale,hz])
   rcases Finset.mem_union.mp hp with hs|hf
   · have hh := (Finset.mem_filter.mp hs).2
     refine ⟨hscale hh.1,?_⟩
     intro input
     have hi := hh.2 ((finiteInputEquiv cutoff).symm input)
     have hw := (finiteProtectedPalettes_field cutoff modulus boundary baseline _ _).mp hi
     rw [finiteProtectedFeatures_field] at hw
     simpa only [Equiv.apply_symm_apply] using Or.inl hw
   · have hh := (Finset.mem_filter.mp hf).2
     refine ⟨hscale hh.2.1,?_⟩
     intro input
     let index := (finiteInputEquiv cutoff).symm input
     by_cases hi : index=finiteProtectedMark cutoff
     · right
       have hin : input=(windowZero cutoff,windowZero cutoff) := by
         have he := congrArg (finiteInputEquiv cutoff) hi
         simpa only [index,finiteProtectedMark,Equiv.apply_symm_apply] using he
       refine ⟨hin,?_⟩
       have he := congrArg (ZMod.finEquiv modulus) hh.1
       rw [finiteProtectedFeatures_field] at he
       simpa only [finiteProtectedMark,Equiv.apply_symm_apply,hin] using he
     · have hmem := (finiteProtectedPalettes_field cutoff modulus boundary baseline index _).mp (hh.2.2 index hi)
       rw [finiteProtectedFeatures_field] at hmem
       simpa only [index,Equiv.apply_symm_apply] using Or.inl hmem

 theorem finiteChartLaw_protected (C : ℝ) (n : ℕ) (boundary baseline : ℤ)
    (mark : Fin (Parameters.modulus n))
    (law : FiniteDist (Fin (Parameters.modulus n*(Parameters.modulus n*Parameters.modulus n))))
    (hsupport : ∀ point, point∉finiteAffineLegalSet (legCutoff C n-1) (Parameters.modulus n) boundary baseline mark → law.weight point=0) :
    ProtectedChartSupport C n boundary baseline mark (law.map (finiteChartEquiv (Parameters.modulus n))) := by
   intro chart hc
   rw [FiniteDist.map_equiv_weight] at hc
   have hi : (finiteChartEquiv (Parameters.modulus n)).symm chart∈
       finiteAffineLegalSet (legCutoff C n-1) (Parameters.modulus n) boundary baseline mark := by
     by_contra hn
     exact hc (hsupport _ hn)
   have hh := finiteAffineLegalSet_physical (legCutoff C n-1) (Parameters.modulus n) boundary baseline mark _ hi
   simpa only [Equiv.apply_symm_apply,ProtectedChartSupport,v7ProtectedPalettes] using hh

 theorem finiteChartLaw_palette_marginal (C : ℝ) (n : ℕ)
    (law : FiniteDist (Fin (Parameters.modulus n*(Parameters.modulus n*Parameters.modulus n))))
    (input : V7Input C n) :
    (law.map (finiteChartEquiv (Parameters.modulus n))).map (chartPaletteFeature C n input)=
      law.map (finiteProtectedFeatures (legCutoff C n-1) (Parameters.modulus n)
        ((finiteInputEquiv (legCutoff C n-1)).symm input)) := by
   rw [FiniteDist.map_map]
   congr 1
   funext point
   simp only [chartPaletteFeature,finiteProtectedFeatures,finiteAffineFeature,Equiv.apply_symm_apply]

end
end AFT.BoundaryCalibration
