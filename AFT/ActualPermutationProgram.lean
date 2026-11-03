import AFT.PermutationProgramCost
import AFT.ParameterProgram
import AFT.BetaGridParameters

/-! # Fair-bit public permutations at the actual V7 population sizes -/
namespace AFT.PermutationProgram
open Filter FiniteDist
open scoped Topology

/-- The runtime dimension uses the bounded integer prime-search program. -/
def vertexCount (n : ℕ) : ℕ := (ParameterProgram.modulus n).value*(max 2 n)^20
def bodyCount (n : ℕ) : ℕ := vertexCount n-2*(max 2 n)^30

theorem vertexCount_eq (n : ℕ) : vertexCount n=Parameters.dimension n := by
  simp only [vertexCount,ParameterProgram.modulus_value,Parameters.dimension,Parameters.meanDensity,Parameters.security]

theorem bodyCount_eq (n : ℕ) : bodyCount n=Parameters.bodies n := by
  simp only [bodyCount,vertexCount_eq,Parameters.bodies,Parameters.legs,Parameters.security]

def vertexDraw (n : ℕ) : (Fin (vertexCount n*n) → Fin 2) → Equiv.Perm (Fin (vertexCount n)) := draw (vertexCount n) n
def bodyDraw (n : ℕ) : (Fin (bodyCount n*n) → Fin 2) → Equiv.Perm (Fin (bodyCount n)) := draw (bodyCount n) n

noncomputable section

theorem vertexDraw_tv (n : ℕ) :
    TVBound ((uniform (Fin (vertexCount n*n) → Fin 2)).map (vertexDraw n))
      (uniform (Equiv.Perm (Fin (vertexCount n)))) ((vertexCount n : ℝ)^2/(2 : ℝ)^n) := by
  rw [vertexDraw,draw_law]
  exact permutationLaw_tv _ _

theorem bodyDraw_tv (n : ℕ) :
    TVBound ((uniform (Fin (bodyCount n*n) → Fin 2)).map (bodyDraw n))
      (uniform (Equiv.Perm (Fin (bodyCount n)))) ((bodyCount n : ℝ)^2/(2 : ℝ)^n) := by
  rw [bodyDraw,draw_law]
  exact permutationLaw_tv _ _

theorem population_bound (n : ℕ) (hn : 2≤n) : vertexCount n≤2*n^60 ∧ bodyCount n≤2*n^60 := by
  have hv := (Parameters.dimension_bounds n).2
  rw [Parameters.security_eq n hn,← vertexCount_eq] at hv
  exact ⟨hv,(Nat.sub_le _ _).trans hv⟩

/-- Both public permutations together have negligible error. -/
theorem actualPermutationError_negligible :
    Negligible (fun n => ((vertexCount n : ℝ)^2+(bodyCount n : ℝ)^2)/(2 : ℝ)^n) := by
  have hm : Negligible (fun n : ℕ => 1/(2 : ℝ)^n) := by
    convert V7Calibration.betaGridMesh_negligible using 1
    funext n
    simp only [V7Calibration.betaGridMesh,Nat.cast_pow,Nat.cast_ofNat]
  apply ((hm.mul_polynomial 120).const_mul 8).of_eventually_le
  filter_upwards [eventually_ge_atTop 2] with n hn
  rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
  have hv : (vertexCount n : ℝ)≤2*(n : ℝ)^60 := by exact_mod_cast (population_bound n hn).1
  have hb : (bodyCount n : ℝ)≤2*(n : ℝ)^60 := by exact_mod_cast (population_bound n hn).2
  have hv2 := pow_le_pow_left₀ (Nat.cast_nonneg (vertexCount n)) hv 2
  have hb2 := pow_le_pow_left₀ (Nat.cast_nonneg (bodyCount n)) hb 2
  rw [mul_pow,← pow_mul] at hv2 hb2
  change _≤8*((n : ℝ)^120*(1/(2 : ℝ)^n))
  rw [show 8*((n : ℝ)^120*(1/(2 : ℝ)^n))=8*(n : ℝ)^120/(2 : ℝ)^n by ring]
  apply div_le_div_of_nonneg_right _ (by positivity)
  norm_num at hv2 hb2
  linarith

/-- The actual permutation tape lengths are polynomial even though the
space of possible permutations has factorial cardinality. -/
theorem actualPermutationBits_bound (n : ℕ) (hn : 2≤n) :
    vertexCount n*n+bodyCount n*n≤4*n^61 := by
  have hs := Nat.add_le_add (Nat.mul_le_mul_right n (population_bound n hn).1)
    (Nat.mul_le_mul_right n (population_bound n hn).2)
  apply hs.trans_eq
  rw [show n^61=n^60*n by rw [show 61=60+1 by omega,pow_succ]]
  ring

/-- A bound for all insertion arithmetic, including uniform-choice table
construction and binary-ticket evaluation. Public parameter search has its
separate checked bound in ParameterProgram.modulus_work_le. -/
theorem actualPermutationWork_bound (n count : ℕ) (hn : 2≤n) (hc : count≤2*n^60)
    (word : Fin count → Fin n → Fin 2) :
    (countedRows n count word).work≤40*n^120 := by
  have hsmall : n≤n^60 := le_self_pow₀ (by omega) (by omega)
  have hone : 1≤n^60 := Nat.one_le_pow _ _ (by omega)
  have hfactor : 3*n+5*count+4≤20*n^60 := by omega
  have hh := (countedRows_work count n word).trans (Nat.mul_le_mul hc hfactor)
  apply hh.trans_eq
  rw [show n^120=n^60*n^60 by rw [← pow_add]]
  ring

end
end AFT.PermutationProgram
