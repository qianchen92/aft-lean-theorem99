import AFT.FiniteConvolutionProgram
import AFT.RootWindow

/-! # The actual integer-window root probabilities are convolution-array entries -/
namespace AFT.FiniteConvolutionProgram
open GaussianSource
open scoped BigOperators

/-- Explicit increasing indexing of the complete protected integer window. -/
def windowIndexEquiv (cutoff : ℕ) : Fin (2*cutoff+1) ≃ Window cutoff where
  toFun index := ⟨(index.val : ℤ)-(cutoff : ℤ),Finset.mem_Icc.mpr (by have hi := index.isLt; constructor <;> omega)⟩
  invFun point := ⟨(point.val+(cutoff : ℤ)).toNat,by
    obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp point.property
    omega⟩
  left_inv index := by apply Fin.ext; simp
  right_inv point := by
    apply Subtype.ext
    obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp point.property
    dsimp only
    rw [Int.toNat_of_nonneg (by omega)]
    omega

/-- An integer target is shifted to the nonnegative coefficient index.
An impossible target below the entire support returns zero directly. -/
def integerLookup {R : Type*} [Zero R] (data : Array R) (radius : ℕ) (target : ℤ) : R :=
  if 0 ≤ target+(radius : ℤ) then lookup data (target+(radius : ℤ)).toNat else 0

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local instance rootConvolutionProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

theorem windowIndexEquiv_sum (cutoff count : ℕ) (word : Fin count → Fin (2*cutoff+1)) :
    (∑ i,(windowIndexEquiv cutoff (word i) : ℤ))=
      ((∑ i,(word i).val : ℕ) : ℤ)-(cutoff*count : ℕ) := by
  simp only [windowIndexEquiv,Equiv.coe_fn_mk,Finset.sum_sub_distrib,Nat.cast_sum,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul]
  ring

/-- This equality is for the exact existing root-slice probability, with
no Gaussian approximation or source-word independence premise supplied. -/
theorem integerLookup_run_probability (cutoff : ℕ) (source : FiniteDist (Window cutoff))
    (count : ℕ) (target : ℤ) :
    integerLookup (run (2*cutoff) (fun index => source.weight (windowIndexEquiv cutoff index)) count).data
      (cutoff*count) target=
      RootSlice.sumProbability source (fun point => (point : ℤ)) count target := by
  let e : (Fin count → Fin (2*cutoff+1)) ≃ (Fin count → Window cutoff) :=
    Equiv.piCongrRight (fun _ => windowIndexEquiv cutoff)
  have he := e.sum_comp (fun word : Fin count → Window cutoff =>
    if (∑ i,(word i : ℤ))=target then ∏ i,source.weight (word i) else 0)
  change (∑ word : Fin count → Fin (2*cutoff+1),
    if (∑ i,(windowIndexEquiv cutoff (word i) : ℤ))=target then
      ∏ i,source.weight (windowIndexEquiv cutoff (word i)) else 0)=_ at he
  have hprob : RootSlice.sumProbability source (fun point => (point : ℤ)) count target=
      ∑ word : Fin count → Window cutoff,if (∑ i,(word i : ℤ))=target then ∏ i,source.weight (word i) else 0 := by
    unfold RootSlice.sumProbability RootSlice.probability RootSlice.integerSum FiniteDist.eventMass FiniteDist.independent
    apply Finset.sum_congr (by ext; simp)
    intro word _
    split_ifs <;> rfl
  rw [hprob,← he]
  unfold integerLookup
  split_ifs with ht
  · rw [run_correct]
    unfold wordCoefficient
    apply Finset.sum_congr (by ext; simp)
    intro word _
    rw [windowIndexEquiv_sum]
    have hnat := Int.toNat_of_nonneg ht
    have hc : ((∑ i,(word i).val : ℕ) : ℤ)-(cutoff*count : ℕ)=target ↔
        (∑ i,(word i).val)=(target+(cutoff*count : ℕ)).toNat := by omega
    simp only [hc]
  · symm
    apply Finset.sum_eq_zero
    intro word _
    rw [windowIndexEquiv_sum]
    rw [if_neg (by have hs : (0 : ℤ) ≤ (∑ i,(word i).val : ℕ) := Int.natCast_nonneg _; omega)]

/-- In particular, the true Gaussian root law uses the same materialized
finite program, with its actual protected one-coordinate masses as input. -/
theorem integerLookup_run_gaussian (width : ℝ) (cutoff count : ℕ) (target : ℤ) :
    integerLookup (run (2*cutoff)
      (fun index => (windowGaussian width cutoff).weight (windowIndexEquiv cutoff index)) count).data
      (cutoff*count) target=
      RootSlice.sumProbability (windowGaussian width cutoff) (fun point => (point : ℤ)) count target :=
  integerLookup_run_probability cutoff (windowGaussian width cutoff) count target

/-- The true one-root marginal is obtained from two entries of the same
convolution program. No sum over complete population words remains. -/
theorem rootMarginal_via_program (width : ℝ) (cutoff population : ℕ)
    (hn : 0 < population) (point : Window cutoff) :
    (rootMarginal width cutoff population hn).weight point=
      (windowGaussian width cutoff).weight point*
        integerLookup (run (2*cutoff)
          (fun index => (windowGaussian width cutoff).weight (windowIndexEquiv cutoff index)) (population-1)).data
          (cutoff*(population-1)) (-(point : ℤ)) /
        integerLookup (run (2*cutoff)
          (fun index => (windowGaussian width cutoff).weight (windowIndexEquiv cutoff index)) population).data
          (cutoff*population) 0 := by
  rw [integerLookup_run_gaussian,integerLookup_run_gaussian]
  exact RootSlice.marginalLaw_weight _ _ _ _ _ _

/-- Casting the executable rational convolution result agrees exactly with
performing the same finite calculation in the reals. -/
theorem run_rat_cast (alphabet : ℕ) (weight : Fin (alphabet+1) → ℚ) (count target : ℕ) :
    ((lookup (run alphabet weight count).data target : ℚ) : ℝ)=
      lookup (run alphabet (fun index => (weight index : ℝ)) count).data target := by
  rw [run_correct,run_correct]
  unfold wordCoefficient
  push_cast
  apply Finset.sum_congr (by ext; simp)
  intro word _
  split_ifs <;> simp only [Rat.cast_prod,Rat.cast_zero]

end
end AFT.FiniteConvolutionProgram
