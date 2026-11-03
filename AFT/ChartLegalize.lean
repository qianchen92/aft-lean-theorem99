import AFT.ActualChartProgram
import AFT.FiniteProductVariation
import AFT.BetaGridParameters

/-! # Support-preserving chart sampling with a finite legal fallback search -/
namespace AFT.BoundaryCalibration
open scoped BigOperators

/-- The search is over the finite array, with no selection oracle. -/
def legalChartIndex (charts : ℕ) [NeZero charts] (legal : Finset (Fin charts)) (point : Fin charts) : Fin charts :=
  if point∈legal then point else if h : legal.Nonempty then legal.min' h else 0

def finiteAffineLegalSet (cutoff modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]
    (boundary baseline : ℤ) (mark : Fin modulus) : Finset (Fin (modulus*(modulus*modulus))) :=
  finiteMarkedSafe (finiteProtectedFeatures cutoff modulus) (finiteAffineScale modulus)
    (finiteProtectedPalettes cutoff modulus boundary baseline) ∪
  finiteMarkedFiber (finiteProtectedFeatures cutoff modulus) (finiteAffineScale modulus)
    (finiteProtectedPalettes cutoff modulus boundary baseline) (finiteProtectedMark cutoff) mark

def safeFiniteAffineChartDraw (cutoff modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]
    (boundary baseline : ℤ) (mark : Fin modulus) (steps bits : ℕ)
    (word : Fin (bits+modulus*(modulus*modulus)+1) → Fin 2) : Fin (modulus*(modulus*modulus)) :=
  legalChartIndex _ (finiteAffineLegalSet cutoff modulus boundary baseline mark)
    (finiteAffineChartDraw cutoff modulus boundary baseline mark steps bits word)

noncomputable section
open scoped Classical Topology
open Filter V7Calibration
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

 theorem legalChartIndex_mem (charts : ℕ) [NeZero charts] (legal : Finset (Fin charts))
    (hlegal : legal.Nonempty) (point : Fin charts) : legalChartIndex charts legal point∈legal := by
  unfold legalChartIndex
  split_ifs with hp
  · exact hp
  · exact legal.min'_mem hlegal

 theorem supported_set_nonempty {charts : ℕ} (law : FiniteDist (Fin charts)) (legal : Finset (Fin charts))
    (hsupport : ∀ point, point∉legal → law.weight point=0) : legal.Nonempty := by
  by_contra hn
  have hz : ∀ point,law.weight point=0 := fun point => hsupport point (by simpa only [Finset.not_nonempty_iff_eq_empty.mp hn] using (Finset.notMem_empty point))
  have hh := law.sum_one
  simp only [hz,Finset.sum_const_zero] at hh
  norm_num at hh

 theorem legalChartIndex_preserves (charts : ℕ) [NeZero charts] (legal : Finset (Fin charts))
    (law : FiniteDist (Fin charts)) (hsupport : ∀ point, point∉legal → law.weight point=0) :
    law.map (legalChartIndex charts legal)=law := by
  ext point
  rw [FiniteDist.map_weight]
  calc
    _ = ∑ input,if input=point then law.weight input else 0 := by
      apply Finset.sum_congr rfl
      intro input _
      by_cases hi : input∈legal
      · simp only [legalChartIndex,if_pos hi]
      · simp only [hsupport input hi,ite_self]
    _ = _ := by simp

 theorem legalChartIndex_l1 (charts : ℕ) [NeZero charts] (legal : Finset (Fin charts))
    (approx reference : FiniteDist (Fin charts)) (hsupport : ∀ point, point∉legal → reference.weight point=0) :
    (∑point,|((approx.map (legalChartIndex charts legal)).weight point)-reference.weight point|)≤
      ∑point,|approx.weight point-reference.weight point| := by
  have hh := FiniteDist.l1_map_le approx reference (legalChartIndex charts legal)
  rwa [legalChartIndex_preserves charts legal reference hsupport] at hh

 def actualChartNumericalError (n : ℕ) : ℝ := 9/(2 : ℝ)^n

 theorem actualChartNumericalError_negligible : Negligible actualChartNumericalError := by
  convert (betaGridMesh_negligible.const_mul 9) using 1
  funext n
  simp only [actualChartNumericalError,betaGridMesh,Nat.cast_pow,Nat.cast_ofNat]
  ring

 theorem finiteAffineChartDraw_error_diagonal (n : ℕ) : 8*(1/4 : ℝ)^n+1/(2 : ℝ)^n≤actualChartNumericalError n := by
  have hp : (1/4 : ℝ)^n≤(1/2 : ℝ)^n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
  simp only [div_pow,one_pow] at hp
  unfold actualChartNumericalError
  simp only [div_pow,one_pow]
  calc
    _ ≤ 8*(1/(2 : ℝ)^n)+1/(2 : ℝ)^n := add_le_add (mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ)≤8)) le_rfl
    _ = _ := by ring

 theorem finiteAffineChart_sampler_legal
    (cutoff modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]
    (boundary baseline : ℤ) (mark : Fin modulus)
    (law : FiniteDist (Fin (modulus*(modulus*modulus))))
    (hsupport : ∀ point, point∉finiteMarkedSafe (finiteProtectedFeatures cutoff modulus) (finiteAffineScale modulus)
      (finiteProtectedPalettes cutoff modulus boundary baseline) →
      point∉finiteMarkedFiber (finiteProtectedFeatures cutoff modulus) (finiteAffineScale modulus)
        (finiteProtectedPalettes cutoff modulus boundary baseline) (finiteProtectedMark cutoff) mark → law.weight point=0) :
    (∀ steps bits word,safeFiniteAffineChartDraw cutoff modulus boundary baseline mark steps bits word∈
      finiteAffineLegalSet cutoff modulus boundary baseline mark) ∧
    (∀ steps bits, (∑point,|((FiniteDist.independent (fun _ : Fin (bits+modulus*(modulus*modulus)+1) => FiniteDist.uniform (Fin 2))).map
      (safeFiniteAffineChartDraw cutoff modulus boundary baseline mark steps bits)).weight point-law.weight point|)≤
      ∑point,|((FiniteDist.independent (fun _ : Fin (bits+modulus*(modulus*modulus)+1) => FiniteDist.uniform (Fin 2))).map
        (finiteAffineChartDraw cutoff modulus boundary baseline mark steps bits)).weight point-law.weight point|) := by
  have hs : ∀ point, point∉finiteAffineLegalSet cutoff modulus boundary baseline mark → law.weight point=0 := by
    intro point hp
    exact hsupport point (fun hh => hp (Finset.mem_union_left _ hh)) (fun hh => hp (Finset.mem_union_right _ hh))
  have hne := supported_set_nonempty law _ hs
  constructor
  · intro steps bits word
    exact legalChartIndex_mem _ _ hne _
  · intro steps bits
    have hh := legalChartIndex_l1 _ _
      ((FiniteDist.independent (fun _ : Fin (bits+modulus*(modulus*modulus)+1) => FiniteDist.uniform (Fin 2))).map
        (finiteAffineChartDraw cutoff modulus boundary baseline mark steps bits)) law hs
    simpa only [FiniteDist.map_map,Function.comp_def,safeFiniteAffineChartDraw] using hh

end
end AFT.BoundaryCalibration
