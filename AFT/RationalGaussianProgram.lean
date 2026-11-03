import AFT.RationalExpProgram
import AFT.GaussianSource

/-! # Executable rational Gaussian weights at rational squared widths -/
namespace AFT.RationalNumerics

/-- Squared width avoids an unnecessary square-root computation. -/
def gaussianRatio (squaredWidth : ℚ) (point : ℤ) : ℚ := (point : ℚ)^2/squaredWidth

def gaussianGuard (squaredWidth : ℚ) (point : ℤ) : ℕ := ⌈gaussianRatio squaredWidth point⌉₊

def gaussianApprox (squaredWidth : ℚ) (point : ℤ) (bits : ℕ) : ℚ :=
  expNegApprox (piApprox (bits+gaussianGuard squaredWidth point+1)*gaussianRatio squaredWidth point) (bits+1)

noncomputable section

/-- The finite pi and exponential programs together approximate the actual
Gaussian exponential; all precision guard digits are computed rationally. -/
theorem gaussianApprox_error (squaredWidth : ℚ) (point : ℤ) (bits : ℕ)
    (hwidth : 0 < squaredWidth) :
    |(gaussianApprox squaredWidth point bits : ℝ)-
      Real.exp (-Real.pi*(point : ℝ)^2/(squaredWidth : ℝ))| ≤ 1/(2 : ℝ)^bits := by
  let ratio := gaussianRatio squaredWidth point
  let guard := gaussianGuard squaredWidth point
  let argument := piApprox (bits+guard+1)*ratio
  have hr0 : (0 : ℚ) ≤ ratio := div_nonneg (sq_nonneg _) hwidth.le
  have hr : (0 : ℝ) ≤ ratio := by exact_mod_cast hr0
  have hguard : (ratio : ℝ) ≤ (guard : ℝ) := by exact_mod_cast Nat.le_ceil ratio
  have hguardpow : (guard : ℝ) ≤ (2 : ℝ)^guard := by exact_mod_cast (Nat.lt_two_pow_self (n:=guard)).le
  have hpi := piApprox_error (bits+guard+1)
  have harg : |(argument : ℝ)-Real.pi*(ratio : ℝ)| ≤ 1/(2 : ℝ)^(bits+1) := by
    have he : (argument : ℝ)-Real.pi*(ratio : ℝ)=((piApprox (bits+guard+1) : ℝ)-Real.pi)*(ratio : ℝ) := by
      dsimp [argument]
      push_cast
      ring
    rw [he,abs_mul,abs_of_nonneg hr]
    calc
      _ ≤ (1/(2 : ℝ)^(bits+guard+1))*(2 : ℝ)^guard :=
        mul_le_mul hpi (hguard.trans hguardpow) hr (by positivity)
      _ = _ := by rw [pow_add,pow_add,pow_add]; field_simp
  have ht : 0 ≤ Real.pi*(ratio : ℝ) := mul_nonneg Real.pi_pos.le hr
  have hclip : |max (argument : ℝ) 0-Real.pi*(ratio : ℝ)| ≤ 1/(2 : ℝ)^(bits+1) := by
    have hh := abs_max_sub_max_le_abs (argument : ℝ) (Real.pi*(ratio : ℝ)) 0
    rw [max_eq_left ht] at hh
    exact hh.trans harg
  have he := expNegApprox_error argument (bits+1)
  have hl := exp_neg_lipschitz (max (argument : ℝ) 0) (Real.pi*(ratio : ℝ)) (le_max_right _ _) ht
  have htarget : -Real.pi*(point : ℝ)^2/(squaredWidth : ℝ) = -(Real.pi*(ratio : ℝ)) := by
    dsimp [ratio,gaussianRatio]
    push_cast
    ring
  rw [htarget]
  calc
    _ ≤ |(expNegApprox argument (bits+1) : ℝ)-Real.exp (-max (argument : ℝ) 0)|+
        |Real.exp (-max (argument : ℝ) 0)-Real.exp (-(Real.pi*(ratio : ℝ)))| := abs_sub_le _ _ _
    _ ≤ 1/(2 : ℝ)^(bits+1)+1/(2 : ℝ)^(bits+1) := add_le_add he (hl.trans hclip)
    _ = _ := by rw [pow_succ]; field_simp; norm_num

theorem gaussianApprox_positive (squaredWidth : ℚ) (point : ℤ) (bits : ℕ) :
    0 < gaussianApprox squaredWidth point bits := expNegApprox_positive _ _

/-- This exact special value keeps both the true and approximate Gaussian
normalizers at least one on every symmetric integer window. -/
theorem gaussianApprox_zero (squaredWidth : ℚ) (bits : ℕ) : gaussianApprox squaredWidth 0 bits=1 := by
  have hz (terms : ℕ) (ht : 0 < terms) : expSum 0 terms=1 := by
    unfold expSum
    rw [Finset.sum_eq_single 0]
    · simp
    · intro index hi hn
      simp [hn]
    · simp [Finset.mem_range.mpr ht]
  simp only [gaussianApprox,gaussianRatio,Int.cast_zero,zero_pow (by decide : 2 ≠ 0),zero_div,mul_zero,
    expNegApprox,max_self,expNegScaled,zero_div]
  rw [hz _ (by omega)]
  simp

/-- Exact connection to the Gaussian weight definition used by V7. -/
theorem gaussianApprox_weight_error (squaredWidth : ℚ) (width : ℝ) (point : ℤ) (bits : ℕ)
    (hwidth : 0 < squaredWidth) (hsquare : width^2=(squaredWidth : ℝ)) :
    |(gaussianApprox squaredWidth point bits : ℝ)-GaussianSource.weight width point| ≤ 1/(2 : ℝ)^bits := by
  convert gaussianApprox_error squaredWidth point bits hwidth using 1
  unfold GaussianSource.weight
  rw [hsquare]
  have h : -(Real.pi / (squaredWidth : ℝ)) * (point : ℝ)^2 =
      -Real.pi * (point : ℝ)^2 / (squaredWidth : ℝ) := by ring
  rw [h]

end
end AFT.RationalNumerics
