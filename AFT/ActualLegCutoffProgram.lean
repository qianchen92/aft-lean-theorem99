import AFT.ActivationParameters

/-! # The actual leg cutoff is computable by finite integer comparisons

For every natural cutoff constant, the program computes exactly the real
ceiling in the V7 source definition. No real-floor or real-power oracle is
used by the executable definition.
-/
namespace AFT.V7Calibration
open GaussianSource

/-- Count the natural numbers strictly below the positive eighth root of
`constant^8 * n^9`, within a proved quadratic search range. -/
def actualLegCutoffProgram (constant n : ℕ) : ℕ :=
  ((Finset.range (constant*n^2+1)).filter (fun index => index^8<constant^8*n^9)).card

noncomputable section

private theorem leg_scale_power (constant n : ℕ) :
    ((constant : ℝ)*(n : ℝ)^(9/8 : ℝ))^8=(constant^8*n^9 : ℕ) := by
  have hp : ((n : ℝ)^(9/8 : ℝ))^(8 : ℕ)=(n : ℝ)^(9 : ℕ) := by
    calc
      _ = (n : ℝ)^((9/8 : ℝ)*(8 : ℕ)) := (Real.rpow_mul_natCast (Nat.cast_nonneg n) (9/8) 8).symm
      _ = (n : ℝ)^(9 : ℝ) := congrArg (fun exponent : ℝ => (n : ℝ)^exponent) (by norm_num)
      _ = _ := Real.rpow_natCast _ 9
  rw [mul_pow,hp]
  push_cast
  rfl

private theorem leg_scale_upper (constant n : ℕ) :
    (constant : ℝ)*(n : ℝ)^(9/8 : ℝ)≤(constant*n^2 : ℕ) := by
  by_cases hn : n=0
  · subst n
    norm_num
  have hn1 : (1 : ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hp := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (9/8 : ℝ)≤2)
  norm_num only [Real.rpow_ofNat] at hp
  push_cast
  exact mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg constant)

/-- The pure integer program agrees exactly with the actual real-valued
source cutoff, for every natural security parameter and cutoff constant. -/
theorem actualLegCutoffProgram_eq (constant n : ℕ) :
    actualLegCutoffProgram constant n=legCutoff (constant : ℝ) n := by
  let value : ℝ := (constant : ℝ)*(n : ℝ)^(9/8 : ℝ)
  have hvalue : 0≤value := by dsimp [value]; positivity
  have hpow : value^8=(constant^8*n^9 : ℕ) := leg_scale_power constant n
  have hupper : value≤(constant*n^2 : ℕ) := leg_scale_upper constant n
  have hpred (index : ℕ) : index^8<constant^8*n^9 ↔ (index : ℝ)<value := by
    rw [← pow_lt_pow_iff_left₀ (Nat.cast_nonneg index) hvalue (by decide : (8 : ℕ)≠0)]
    rw [hpow]
    exact_mod_cast (Iff.rfl : index^8<constant^8*n^9 ↔ index^8<constant^8*n^9)
  have hset : (Finset.range (constant*n^2+1)).filter (fun index => index^8<constant^8*n^9)=
      Finset.range ⌈value⌉₊ := by
    ext index
    simp only [Finset.mem_filter,Finset.mem_range,hpred,Nat.lt_ceil]
    constructor
    · exact And.right
    · intro hi
      refine ⟨?_,hi⟩
      have hh : (index : ℝ)<(constant*n^2 : ℕ)+1 := by linarith
      exact_mod_cast hh
  unfold actualLegCutoffProgram legCutoff
  rw [hset,Finset.card_range]

/-- The search range has polynomial length for each fixed cutoff constant. -/
theorem actualLegCutoffProgram_le (constant n : ℕ) :
    actualLegCutoffProgram constant n≤constant*n^2 := by
  rw [actualLegCutoffProgram_eq]
  exact Nat.ceil_le.mpr (leg_scale_upper constant n)

end
end AFT.V7Calibration
