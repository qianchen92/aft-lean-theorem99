import CurrentAFT.BinarySparseCycleEvaluation

/-! The executed touched-edge Gaussian sum is exactly the manuscript's sparse
cycle evaluator, for arbitrary joint tests and every root-placement pattern. -/
namespace CurrentAFT.BinarySparseCycleSemantic
open AFT GaussianSource RationalNumerics BinaryArithmetic
open BinaryTouchedCycle BinaryTouchedCycleBuffer BinaryTouchedCycleRanks
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false


def coordinates {body count : ℕ} (cutoff : ℕ) (hb : 0 < body) (sites : Vector (Fin body) count) :
    (Fin (prepare hb sites).value.length → Fin (2*cutoff+1)) ≃
      (CyclePatternProgram.touched sites.get → Window cutoff) :=
  Equiv.arrowCongr (edgeEquiv hb sites) (FiniteConvolutionProgram.windowIndexEquiv cutoff)

 theorem coordinates_apply {body count : ℕ} (cutoff : ℕ) (hb : 0 < body) (sites : Vector (Fin body) count)
    (word : Fin (prepare hb sites).value.length → Fin (2*cutoff+1)) (edge : Fin (prepare hb sites).value.length) :
    coordinates cutoff hb sites word (edgeEquiv hb sites edge) = FiniteConvolutionProgram.windowIndexEquiv cutoff (word edge) := by
  simp only [coordinates,Equiv.arrowCongr_apply,Function.comp_def,Equiv.symm_apply_apply]

 theorem roots_coordinates {body count : ℕ} (cutoff : ℕ) (hb : 0 < body) (sites : Vector (Fin body) count)
    (word : Fin (prepare hb sites).value.length → Fin (2*cutoff+1)) :
    CyclePatternProgram.roots sites.get (fun value : Window cutoff => value.val) (coordinates cutoff hb sites word) =
      fun slot => ((word (((positions hb sites).value.get slot).1)).val : ℤ) -
        (word (((positions hb sites).value.get slot).2)).val := by
  funext slot
  have hcurrent : edgeEquiv hb sites ((positions hb sites).value.get slot).1 = CyclePatternProgram.currentEdge sites.get slot := by
    apply Subtype.ext
    exact (positions_value hb sites slot).1
  have hprevious : edgeEquiv hb sites ((positions hb sites).value.get slot).2 = CyclePatternProgram.previousEdge sites.get slot := by
    apply Subtype.ext
    exact (positions_value hb sites slot).2
  change ((coordinates cutoff hb sites word) (CyclePatternProgram.currentEdge sites.get slot)).val -
    ((coordinates cutoff hb sites word) (CyclePatternProgram.previousEdge sites.get slot)).val = _
  rw [←hcurrent,←hprevious,coordinates_apply,coordinates_apply]
  change (((word (((positions hb sites).value.get slot).1)).val : ℤ) - cutoff) -
    (((word (((positions hb sites).value.get slot).2)).val : ℤ) - cutoff) = _
  ring

 theorem product_coordinates {body count : ℕ} (security cutoff bits : ℕ) (hb : 0 < body) (sites : Vector (Fin body) count)
    (word : Fin (prepare hb sites).value.length → Fin (2*cutoff+1)) :
    (∏ edge, windowGaussianWeights (WindowGaussianSampler.squaredWidth security) cutoff bits (word edge)) =
      ∏ edge, windowApproxWeight (WindowGaussianSampler.squaredWidth security) cutoff bits (coordinates cutoff hb sites word edge) := by
  have h := (edgeEquiv hb sites).prod_comp (fun edge =>
    windowApproxWeight (WindowGaussianSampler.squaredWidth security) cutoff bits (coordinates cutoff hb sites word edge))
  simpa only [coordinates_apply,windowGaussianWeights] using h

 theorem current_value {body count : ℕ} (security cutoff bits : ℕ) (hb : 0 < body) (sites : Vector (Fin body) count)
    (test : Vector IntegerBits count → RationalResult) (ideal : (Fin count → ℤ) → ℚ)
    (htest : ∀ rootWord, (test rootWord).data.decode = ideal (fun slot => (rootWord.get slot).decode)) :
    (BinarySparseCycleEvaluation.current security cutoff bits hb sites test).data.decode =
      CyclePatternProgram.gaussianEvaluate security cutoff bits sites.get ideal := by
  rw [BinarySparseCycleEvaluation.current_tuple_value security cutoff bits hb sites test ideal htest]
  unfold CyclePatternProgram.gaussianEvaluate CyclePatternProgram.evaluate
  calc
    _ = ∑ word : Fin (prepare hb sites).value.length → Fin (2*cutoff+1),
      (∏ edge, windowApproxWeight (WindowGaussianSampler.squaredWidth security) cutoff bits (coordinates cutoff hb sites word edge)) *
        ideal (CyclePatternProgram.roots sites.get (fun value : Window cutoff => value.val) (coordinates cutoff hb sites word)) := by
      apply Finset.sum_congr rfl
      intro word _
      rw [product_coordinates,roots_coordinates]
    _ = _ := (coordinates cutoff hb sites).sum_comp (fun latent : CyclePatternProgram.touched sites.get → Window cutoff =>
      (∏ edge, windowApproxWeight (WindowGaussianSampler.squaredWidth security) cutoff bits (latent edge)) *
        ideal (CyclePatternProgram.roots sites.get (fun value : Window cutoff => value.val) latent))

end
end CurrentAFT.BinarySparseCycleSemantic
