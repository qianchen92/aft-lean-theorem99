import AFT.ActualPhysicalChartProgram

/-! # The decoded rational chart target gives the same exact physical pair output -/
namespace AFT.BoundaryCalibration
open GaussianSource
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

 theorem finiteProtectedAtom_actual (C : ℝ) (n : ℕ) :
    (finiteProtectedAtom (legCutoff C n-1) : ℝ)=chartAtom (V7Input C n) := by
  rw [finiteProtectedAtom_cast]
  simp only [chartAtom,Fintype.card_fin,protectedInputs_card,pow_two]

 theorem finiteChartLaw_pair_output (C : ℝ) (n : ℕ) (boundary baseline : ℤ)
    (hb : 0≤boundary) (mark : Fin (Parameters.modulus n))
    (law : FiniteDist (Fin (Parameters.modulus n*(Parameters.modulus n*Parameters.modulus n))))
    (hmark : ∀ color,(law.map (finiteProtectedFeatures (legCutoff C n-1) (Parameters.modulus n)
      (finiteProtectedMark (legCutoff C n-1)))).weight color=
      (1-(finiteProtectedAtom (legCutoff C n-1) : ℝ))*
        (if color∈finiteProtectedPalettes (legCutoff C n-1) (Parameters.modulus n) boundary baseline (finiteProtectedMark (legCutoff C n-1)) then
          ((finiteProtectedPalettes (legCutoff C n-1) (Parameters.modulus n) boundary baseline (finiteProtectedMark (legCutoff C n-1))).card : ℝ)⁻¹ else 0)+
        (finiteProtectedAtom (legCutoff C n-1) : ℝ)*(if color=mark then 1 else 0))
    (hother : ∀ i,i≠finiteProtectedMark (legCutoff C n-1) → ∀ color,
      (law.map (finiteProtectedFeatures (legCutoff C n-1) (Parameters.modulus n) i)).weight color=
        if color∈finiteProtectedPalettes (legCutoff C n-1) (Parameters.modulus n) boundary baseline i then
          ((finiteProtectedPalettes (legCutoff C n-1) (Parameters.modulus n) boundary baseline i).card : ℝ)⁻¹ else 0)
    (input : V7Input C n) (first second : Fin (Parameters.modulus n)) :
    (chartPairOutput C n baseline (law.map (finiteChartEquiv (Parameters.modulus n))) input).weight (first,second)=
      (1-if input=(windowZero _,windowZero _) then chartAtom (V7Input C n) else 0)*
        TrimmedSlice.orderedPairSlice (Parameters.modulus n) boundary (baseline-input.2) first second+
      (if input=(windowZero _,windowZero _) then chartAtom (V7Input C n) else 0)*(if first=mark then 1 else 0)*
        (if second=paletteEmbedding n ((Parameters.modulus n : ℤ)-1+baseline-input.2-mark.val) then 1 else 0) := by
  let index := (finiteInputEquiv (legCutoff C n-1)).symm input
  have hindex : index=finiteProtectedMark (legCutoff C n-1) ↔ input=(windowZero _,windowZero _) := by
    exact (finiteInputEquiv (legCutoff C n-1)).symm.injective.eq_iff
  have hunif : (if first∈finiteProtectedPalettes (legCutoff C n-1) (Parameters.modulus n) boundary baseline index then
      ((finiteProtectedPalettes (legCutoff C n-1) (Parameters.modulus n) boundary baseline index).card : ℝ)⁻¹ else 0)=
      TrimmedSlice.law (Parameters.modulus n) boundary (baseline-input.2) first.val := by
    simp only [finiteProtectedPalettes,index,Equiv.apply_symm_apply]
    rw [TrimmedSlice.paletteSlice_card _ _ _ hb]
    simp only [TrimmedSlice.paletteSlice,Finset.mem_filter,Finset.mem_univ,true_and,TrimmedSlice.law,TrimmedSlice.slice_card]
  have hmarg : ((law.map (finiteChartEquiv (Parameters.modulus n))).map (chartPaletteFeature C n input)).weight first=
      (1-if input=(windowZero _,windowZero _) then chartAtom (V7Input C n) else 0)*
        TrimmedSlice.law (Parameters.modulus n) boundary (baseline-input.2) first.val+
      (if input=(windowZero _,windowZero _) then chartAtom (V7Input C n) else 0)*(if first=mark then 1 else 0) := by
    rw [finiteChartLaw_palette_marginal]
    change (law.map (finiteProtectedFeatures (legCutoff C n-1) (Parameters.modulus n) index)).weight first=_
    by_cases hi : input=(windowZero _,windowZero _)
    · rw [←hindex] at hi
      rw [hi,hmark,finiteProtectedAtom_actual]
      rw [hi] at hunif
      rw [hunif,if_pos (hindex.mp hi)]
    · rw [hother index (fun hh => hi (hindex.mp hh)),hunif,if_neg hi]
      ring
  rw [chartPairOutput,FiniteDist.graph_weight,hmarg]
  have hshift : (Parameters.modulus n : ℤ)-1+baseline-input.2-first.val=
      (Parameters.modulus n : ℤ)-1+(baseline-input.2)-first.val := by ring
  rw [add_mul,mul_assoc]
  apply congrArg₂ (fun a b : ℝ => a+b)
  · apply congrArg (fun value : ℝ => (1-if input=(windowZero _,windowZero _) then chartAtom (V7Input C n) else 0)*value)
    have hh := slice_companion_graph n boundary (baseline-input.2) hb first second
    convert hh using 1
    rw [hshift]
  · by_cases hf : first=mark
    · subst first
      split_ifs <;> rfl
    · simp only [if_neg hf,mul_zero,zero_mul]


end
end AFT.BoundaryCalibration
