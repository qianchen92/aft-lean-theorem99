import AFT.RationalPaletteSampler
import AFT.ActualBodyBlurProgram
import AFT.ActualResponseProgramHeight
import AFT.FiniteProductVariation

/-! # An explicit finite-array sampler for the actual public body blur -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics RationalPaletteSampler FiniteConvolutionProgram Filter
open scoped BigOperators

 def actualBodySampleCount (constant n : ℕ) : ℕ :=
  (2*(3*n^2-1)+1)*((2*(actualLegCutoffProgram constant n-1)+1+1)*(2*(n^2-1)+1+1))

 def actualBodySampleIndexEquiv (constant n : ℕ) :
    Fin (actualBodySampleCount constant n)≃ActualBodyProgramSample constant n :=
  finProdFinEquiv.symm.trans ((windowIndexEquiv (3*n^2-1)).prodCongr
    (finProdFinEquiv.symm.trans
      (((finSuccEquiv (2*(actualLegCutoffProgram constant n-1)+1)).trans
        (Equiv.optionCongr (windowIndexEquiv (actualLegCutoffProgram constant n-1)))).prodCongr
      ((finSuccEquiv (2*(n^2-1)+1)).trans (Equiv.optionCongr (windowIndexEquiv (n^2-1)))))))

 theorem actualBodySampleCount_pos (constant n : ℕ) : 0<actualBodySampleCount constant n := by
   unfold actualBodySampleCount;positivity

 def actualBodyProgramDecode (constant n : ℕ) (point : ActualBodyProgramSample constant n) : bodySample (constant : ℝ) n :=
  (point.1,Option.map (fun z => (⟨z.val,by rw [←actualLegCutoffProgram_eq];exact z.property⟩ : Window (legCutoff (constant : ℝ) n-1))) point.2.1,point.2.2)

 def actualBodySampleDraw (constant n : ℕ) (bits : ℕ)
    (word : Fin (bits+actualBodySampleCount constant n+1) → Fin 2) : bodySample (constant : ℝ) n :=
  actualBodyProgramDecode constant n (actualBodySampleIndexEquiv constant n
    (draw (actualBodySampleCount constant n) (actualBodySampleCount_pos constant n)
      (fun index => actualBodyBlurProgram constant n (actualBodySampleIndexEquiv constant n index)) bits word))

noncomputable section
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

 theorem actualBodyProgramDecode_eq (constant n : ℕ) : actualBodyProgramDecode constant n=actualBodyProgramEquiv constant n := by
  funext point
  rcases point with ⟨root,leg,queue⟩
  cases leg <;> rfl

 def actualBodySamplePhysicalEquiv (constant n : ℕ) : Fin (actualBodySampleCount constant n)≃bodySample (constant : ℝ) n :=
   (actualBodySampleIndexEquiv constant n).trans (actualBodyProgramEquiv constant n)

 def actualBodySampleError (n : ℕ) : ℝ := 1/(2 : ℝ)^n+4*actualBodyBlurProgramError n

 theorem actualBodySampleError_negligible : Negligible actualBodySampleError := by
   have hg : Negligible (fun n : ℕ => 1/(2 : ℝ)^n) := by
     convert betaGridMesh_negligible using 1
     funext n;simp only [betaGridMesh,Nat.cast_pow,Nat.cast_ofNat]
   exact hg.add (actualBodyBlurProgramError_negligible.const_mul 4)

 theorem actual_body_sample_program_eventually (constant : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (∑ sample,|((FiniteDist.independent (fun _ : Fin (n+actualBodySampleCount constant n+1) => FiniteDist.uniform (Fin 2))).map
        (actualBodySampleDraw constant n n)).weight sample-(bodyBlur (constant : ℝ) n).weight sample|)≤actualBodySampleError n := by
  have hs := actualBodyBlurProgramError_negligible.tendsto_zero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/2))
  filter_upwards [actual_body_blur_program_eventually constant,hs] with n he hs
  let reference := (bodyBlur (constant : ℝ) n).map (actualBodySamplePhysicalEquiv constant n).symm
  have herr : (∑ index : Fin (actualBodySampleCount constant n),
      |(actualBodyBlurProgram constant n (actualBodySampleIndexEquiv constant n index) : ℝ)-reference.weight index|)≤actualBodyBlurProgramError n := by
    simp only [reference,FiniteDist.map_equiv_weight,Equiv.symm_symm,actualBodySamplePhysicalEquiv,Equiv.trans_apply]
    calc
      _ = ∑ point : ActualBodyProgramSample constant n,
          |(actualBodyBlurProgram constant n point : ℝ)-(bodyBlur (constant : ℝ) n).weight (actualBodyProgramEquiv constant n point)| :=
        (actualBodySampleIndexEquiv constant n).sum_comp _
      _ ≤ _ := he
  have hd := draw_l1 (actualBodySampleCount constant n) (actualBodySampleCount_pos constant n)
    (fun index => actualBodyBlurProgram constant n (actualBodySampleIndexEquiv constant n index)) n reference
    (actualBodyBlurProgramError n) herr hs.le
  rw [←FiniteTicketSampler.independent_fair_bits_uniform] at hd
  have hm := FiniteDist.l1_map_le
    ((FiniteDist.independent (fun _ : Fin (n+actualBodySampleCount constant n+1) => FiniteDist.uniform (Fin 2))).map
      (draw (actualBodySampleCount constant n) (actualBodySampleCount_pos constant n)
        (fun index => actualBodyBlurProgram constant n (actualBodySampleIndexEquiv constant n index)) n)) reference
    (actualBodySamplePhysicalEquiv constant n)
  have hr : reference.map (actualBodySamplePhysicalEquiv constant n)=bodyBlur (constant : ℝ) n := by
    simp only [reference,FiniteDist.map_map,Equiv.apply_symm_apply]
    ext point
    simp [FiniteDist.map_weight]
  rw [hr,FiniteDist.map_map] at hm
  have hf : (fun word => actualBodySamplePhysicalEquiv constant n
      (draw (actualBodySampleCount constant n) (actualBodySampleCount_pos constant n)
        (fun index => actualBodyBlurProgram constant n (actualBodySampleIndexEquiv constant n index)) n word))=
      actualBodySampleDraw constant n n := by
    funext word
    simp only [actualBodySampleDraw,actualBodyProgramDecode_eq,actualBodySamplePhysicalEquiv,Equiv.trans_apply]
  rw [hf] at hm
  exact hm.trans hd

 theorem actualBodySampleCount_bound (constant n : ℕ) (hn : 2≤n) :
    actualBodySampleCount constant n≤96*(constant+1)*n^6 := by
  have hc := actualLegCutoffProgram_le constant n
  have h1 : 1≤n^2 := one_le_pow₀ (by omega : 1≤n)
  have hr : 2*(3*n^2-1)+1≤6*n^2 := by omega
  have hl : 2*(actualLegCutoffProgram constant n-1)+1+1≤4*(constant+1)*n^2 := by nlinarith [Nat.sub_le (actualLegCutoffProgram constant n) 1]
  have hq : 2*(n^2-1)+1+1≤4*n^2 := by omega
  unfold actualBodySampleCount
  calc
    _≤(6*n^2)*((4*(constant+1)*n^2)*(4*n^2)) := Nat.mul_le_mul hr (Nat.mul_le_mul hl hq)
    _=_ := by ring

end
end AFT.V7Calibration
