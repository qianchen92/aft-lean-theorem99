import AFT.FiniteAffineFeatures
import AFT.FiniteMarkedChart
import AFT.MarkedChartFinSampler

/-! # The executable chart sampler uses the actual F³ projection and palettes -/
namespace AFT.BoundaryCalibration
open scoped BigOperators

def finiteProtectedMark (cutoff : ℕ) : Fin ((2*cutoff+1)*(2*cutoff+1)) :=
  (finiteInputEquiv cutoff).symm (GaussianSource.windowZero cutoff,GaussianSource.windowZero cutoff)

def finiteProtectedAtom (cutoff : ℕ) : ℚ :=
  1/(100*(((2*cutoff+1)*(2*cutoff+1) : ℕ) : ℚ))

def finiteAffineChartDraw (cutoff modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]
    (boundary baseline : ℤ) (mark : Fin modulus) (steps bits : ℕ)
    (word : Fin (bits+modulus*(modulus*modulus)+1) → Fin 2) : Fin (modulus*(modulus*modulus)) :=
  let feature := finiteProtectedFeatures cutoff modulus
  let allowed := finiteProtectedPalettes cutoff modulus boundary baseline
  let auxiliary := finiteAffineScale modulus
  markedChartFinDraw (modulus*(modulus*modulus)) modulus ((2*cutoff+1)*(2*cutoff+1)) feature allowed
    (finiteMarkedSafe feature auxiliary allowed)
    (finiteMarkedFiber feature auxiliary allowed (finiteProtectedMark cutoff) mark)
    (finiteProtectedMark cutoff) (finiteProtectedAtom cutoff) steps bits word

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

 theorem finiteProtected_budget (cutoff modulus : ℕ) [NeZero modulus] (boundary baseline : ℤ) :
    affineDeletionBudget (finiteProtectedPalettes cutoff modulus boundary baseline)=
      affineDeletionBudget (protectedPalettes cutoff modulus boundary baseline) := by
  unfold affineDeletionBudget
  simp only [Fintype.card_fin,ZMod.card]
  congr 1
  have hh := (finiteInputEquiv cutoff).sum_comp (fun input =>
    (1 : ℝ)-(protectedPalettes cutoff modulus boundary baseline input).card/(modulus : ℝ))
  simpa only [finiteProtectedPalettes,protectedPalettes,fieldPalette,Finset.card_map] using hh

 theorem finiteProtectedAtom_cast (cutoff : ℕ) :
    (finiteProtectedAtom cutoff : ℝ)=chartAtom (Fin ((2*cutoff+1)*(2*cutoff+1))) := by
  simp [finiteProtectedAtom,chartAtom,div_eq_mul_inv]


 theorem finite_affine_chart_sampler
    (cutoff modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]
    (boundary baseline : ℤ) (mark : Fin modulus)
    (hsize : 2*cutoff < modulus)
    (hsmall : (2*((2*cutoff+1)*(2*cutoff+1)) + 1 : ℝ)*
      affineDeletionBudget (protectedPalettes cutoff modulus boundary baseline)≤1/4) :
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
            8*(1/4 : ℝ)^steps+1/(2 : ℝ)^bits) := by
  let feature := finiteProtectedFeatures cutoff modulus
  let allowed := finiteProtectedPalettes cutoff modulus boundary baseline
  let auxiliary := finiteAffineScale modulus
  let marked := finiteProtectedMark cutoff
  let atom : ℝ := finiteProtectedAtom cutoff
  have ha := chartAtom_bounds marked
  rw [←finiteProtectedAtom_cast] at ha
  simp only [Fintype.card_fin] at ha
  obtain ⟨hD,hquarter,hdefect,law,hlaw,hsupport,hmark,hother⟩ :=
    finite_marked_chart (modulus*(modulus*modulus)) modulus ((2*cutoff+1)*(2*cutoff+1)) feature auxiliary allowed marked mark
      (fun i => finiteAffineFeature_uniform modulus _ _)
      (finiteProtectedFeatures_pair_uniform modulus cutoff hsize)
      (finiteAffineScale_uniform modulus)
      (fun i => finiteAffineFeature_scale_uniform modulus _ _)
      (by simpa only [allowed,finiteProtected_budget,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat] using hsmall)
      atom ha.1 ha.2.1 ha.2.2
  refine ⟨law,hsupport,hmark,hother,?_⟩
  intro steps bits hsteps
  exact markedChartFinDraw_l1 _ _ _ feature allowed _ _ marked (finiteProtectedAtom cutoff)
    ha.1 (by linarith [ha.2.1]) hD hquarter hdefect law hlaw steps bits hsteps

end
end AFT.BoundaryCalibration
