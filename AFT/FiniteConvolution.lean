import AFT.InverseMixedActivity

/-!
# Concrete finite convolution operators and palette-independent Hilbert bounds
-/

namespace AFT.SafeConvolution

open scoped BigOperators

variable {G : Type*} [Fintype G] [AddCommGroup G]

noncomputable def kernelL1 (kernel : G → ℝ) : ℝ := ∑ shift, |kernel shift|
noncomputable def countingL2 (profile : G → ℝ) : ℝ := Real.sqrt (∑ color, profile color ^ 2)

noncomputable def convolution (kernel : G → ℝ) : Module.End ℝ (G → ℝ) where
  toFun profile output := ∑ shift, kernel shift * profile (output - shift)
  map_add' first second := by ext output; simp [mul_add, Finset.sum_add_distrib]
  map_smul' scalar profile := by ext output; simp [← Finset.mul_sum, mul_left_comm]

@[simp] theorem convolution_apply (kernel profile : G → ℝ) (output : G) :
    convolution kernel profile output = ∑ shift, kernel shift * profile (output - shift) := rfl

omit [AddCommGroup G] in
theorem kernelL1_nonneg (kernel : G → ℝ) : 0 ≤ kernelL1 kernel :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

omit [AddCommGroup G] in
theorem countingL2_nonneg (profile : G → ℝ) : 0 ≤ countingL2 profile := Real.sqrt_nonneg _

omit [AddCommGroup G] in
theorem countingL2_add (first second : G → ℝ) :
    countingL2 (first + second) ≤ countingL2 first + countingL2 second := by
  simpa only [countingL2, profileSquareNorm, div_one] using
    profileSquareNorm_sqrt_add_le (fun _ : G => (1 : ℝ)) first second (by intro; norm_num)

omit [AddCommGroup G] in
theorem countingL2_smul (scalar : ℝ) (profile : G → ℝ) :
    countingL2 (scalar • profile) = |scalar| * countingL2 profile := by
  unfold countingL2
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum,
    Real.sqrt_mul (sq_nonneg scalar), Real.sqrt_sq_eq_abs]

omit [AddCommGroup G] in
theorem countingL2_neg (profile : G → ℝ) : countingL2 (-profile) = countingL2 profile := by
  simp only [countingL2, Pi.neg_apply, neg_sq]

theorem translated_sum (profile : G → ℝ) (shift : G) :
    (∑ color, profile (color - shift)) = ∑ color, profile color :=
  Equiv.sum_comp (Equiv.subRight shift) profile

theorem convolution_mass (kernel profile : G → ℝ) :
    (∑ color, convolution kernel profile color) = (∑ shift, kernel shift) * ∑ color, profile color := by
  simp only [convolution_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, translated_sum]
  rw [← Finset.sum_mul]

/-- Signed Young inequality proved from the actual finite kernel entries. -/
theorem convolution_square_le (kernel profile : G → ℝ) :
    (∑ color, convolution kernel profile color ^ 2) ≤ kernelL1 kernel ^ 2 * ∑ color, profile color ^ 2 := by
  have hpoint (color : G) : convolution kernel profile color ^ 2 ≤
      kernelL1 kernel * ∑ shift, |kernel shift| * profile (color - shift) ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    · intro shift _
      exact abs_nonneg _
    · intro shift _
      exact mul_nonneg (abs_nonneg _) (sq_nonneg _)
    · intro shift _
      rw [mul_pow]
      nlinarith [sq_abs (kernel shift)]
  calc
    _ ≤ ∑ color, kernelL1 kernel * ∑ shift, |kernel shift| * profile (color - shift) ^ 2 :=
      Finset.sum_le_sum fun color _ => hpoint color
    _ = kernelL1 kernel * ∑ shift, |kernel shift| * ∑ color, profile (color - shift) ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by
      simp_rw [translated_sum (fun color => profile color ^ 2)]
      rw [← Finset.sum_mul]
      dsimp [kernelL1]
      ring

theorem convolution_L2_le (kernel profile : G → ℝ) :
    countingL2 (convolution kernel profile) ≤ kernelL1 kernel * countingL2 profile := by
  exact (Real.sqrt_le_sqrt (convolution_square_le kernel profile)).trans_eq (by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (kernelL1_nonneg kernel)]
    rfl)

theorem probability_convolution_L2_le (source : FiniteDist G) (profile : G → ℝ) :
    countingL2 (convolution source.weight profile) ≤ countingL2 profile := by
  have hmass : kernelL1 source.weight = 1 := by simp only [kernelL1, abs_of_nonneg (source.nonneg _), source.sum_one]
  simpa only [hmass, one_mul] using convolution_L2_le source.weight profile

theorem convolution_add_kernel (first second : G → ℝ) :
    convolution (first + second) = convolution first + convolution second := by
  ext profile output
  simp [convolution_apply, add_mul, Finset.sum_add_distrib]

theorem convolution_sub_kernel (first second : G → ℝ) :
    convolution (first - second) = convolution first - convolution second := by
  ext profile output
  simp [convolution_apply, sub_mul, Finset.sum_sub_distrib]

/-- Actual finite convolution operators commute because the source shifts
add in the same abelian output palette. -/
theorem convolution_commute (first second : G → ℝ) :
    Commute (convolution first) (convolution second) := by
  apply LinearMap.ext
  intro profile
  funext output
  simp only [Module.End.mul_apply, convolution_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have heq : output - b - a = output - a - b := by abel
  rw [heq]
  ring

theorem convolution_convolution (first second : G → ℝ) :
    convolution (convolution first second) = convolution first * convolution second := by
  ext profile output
  simp only [convolution_apply, Module.End.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  have heq : (∑ shift, first a * second (shift - a) * profile (output - shift)) =
      ∑ shift, first a * second shift * profile (output - (shift + a)) := by
    symm
    simpa only [Equiv.coe_addRight, add_sub_cancel_right] using
      Equiv.sum_comp (Equiv.addRight a)
        (fun shift => first a * second (shift - a) * profile (output - shift))
  rw [heq]
  apply Finset.sum_congr rfl
  intro b _
  have hx : output - (b + a) = output - a - b := by abel
  rw [hx]
  ring

omit [AddCommGroup G] in
/-- Pushforward of a genuine signed finite kernel contracts L1. -/
theorem pushforward_L1_le {α : Type*} [Fintype α] [DecidableEq G]
    (map : α → G) (kernel : α → ℝ) :
    kernelL1 (fun color => ∑ source, if map source = color then kernel source else 0) ≤ ∑ source, |kernel source| := by
  calc
    _ ≤ ∑ color : G, ∑ source : α, |if map source = color then kernel source else 0| :=
      Finset.sum_le_sum fun color _ => Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro source _
      simp only [apply_ite abs, abs_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end AFT.SafeConvolution
