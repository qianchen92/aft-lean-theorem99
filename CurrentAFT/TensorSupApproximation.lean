import CurrentAFT.PhysicalSynthesis

/-! # Uniform approximation of tensor channels on arbitrary joint kernels

The input kernel is kept joint. Local operator errors accumulate only over
its fixed number of slots, before averaging distinct public group choices.
-/
namespace CurrentAFT.TensorSupApproximation
open AFT
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {Input Output : Type*}

theorem tensor_bound (channel : (Input → ℝ) →ₗ[ℝ] (Output → ℝ)) (factor : ℝ) (hf : 0 ≤ factor)
    (hchannel : ∀ (score : Input → ℝ) (bound : ℝ), 0 ≤ bound →
      (∀ input, |score input| ≤ bound) → ∀ output, |channel score output| ≤ factor * bound)
    (count : ℕ) (kernel : (Fin count → Input) → ℝ) (bound : ℝ) (hb : 0 ≤ bound)
    (hkernel : ∀ word, |kernel word| ≤ bound) (output : Fin count → Output) :
    |TensorChannel.apply count (fun _ => channel) kernel output| ≤ factor^count * bound := by
  induction count with
  | zero => simpa only [TensorChannel.apply, pow_zero, one_mul] using hkernel Fin.elim0
  | succ count ih =>
      change |channel (fun first => TensorChannel.apply count (fun _ => channel)
        (fun rest => kernel (Fin.cons first rest)) (fun index => output index.succ)) (output 0)| ≤ _
      apply (hchannel _ (factor^count * bound) (by positivity)
        (fun first => ih _ (fun rest => hkernel (Fin.cons first rest)) _) _).trans_eq
      rw [pow_succ]
      ring

theorem tensor_difference (first second : (Input → ℝ) →ₗ[ℝ] (Output → ℝ))
    (factor error : ℝ) (hf : 1 ≤ factor) (he : 0 ≤ error)
    (hfirst : ∀ (score : Input → ℝ) (bound : ℝ), 0 ≤ bound →
      (∀ input, |score input| ≤ bound) → ∀ output, |first score output| ≤ factor * bound)
    (hsecond : ∀ (score : Input → ℝ) (bound : ℝ), 0 ≤ bound →
      (∀ input, |score input| ≤ bound) → ∀ output, |second score output| ≤ factor * bound)
    (hdifference : ∀ (score : Input → ℝ) (bound : ℝ), 0 ≤ bound →
      (∀ input, |score input| ≤ bound) → ∀ output,
        |second score output - first score output| ≤ error * bound)
    (count : ℕ) (kernel : (Fin count → Input) → ℝ) (bound : ℝ) (hb : 0 ≤ bound)
    (hkernel : ∀ word, |kernel word| ≤ bound) (output : Fin count → Output) :
    |TensorChannel.apply count (fun _ => second) kernel output -
      TensorChannel.apply count (fun _ => first) kernel output| ≤
        count * error * factor^count * bound := by
  induction count with
  | zero => simp only [TensorChannel.apply, sub_self, abs_zero, Nat.cast_zero, zero_mul, le_refl]
  | succ count ih =>
      let left (input : Input) := TensorChannel.apply count (fun _ => first)
        (fun rest => kernel (Fin.cons input rest)) (fun index => output index.succ)
      let right (input : Input) := TensorChannel.apply count (fun _ => second)
        (fun rest => kernel (Fin.cons input rest)) (fun index => output index.succ)
      have hleft (input : Input) : |left input| ≤ factor^count * bound :=
        tensor_bound first factor (by linarith) hfirst count _ bound hb (fun rest => hkernel (Fin.cons input rest)) _
      have hdiff (input : Input) : |(right - left) input| ≤ count * error * factor^count * bound :=
        ih _ (fun rest => hkernel (Fin.cons input rest)) _
      have hlocal := hdifference left (factor^count * bound) (by positivity) hleft (output 0)
      have hrest := hsecond (right - left) (count * error * factor^count * bound) (by positivity) hdiff (output 0)
      have hsplit : second right (output 0) - first left (output 0) =
          second (right - left) (output 0) + (second left (output 0) - first left (output 0)) := by
        rw [map_sub, Pi.sub_apply]
        ring
      change |second right (output 0) - first left (output 0)| ≤ _
      rw [hsplit]
      apply (abs_add_le _ _).trans ((add_le_add hrest hlocal).trans ?_)
      have hp : factor^count ≤ factor^(count + 1) := pow_le_pow_right₀ hf (by omega)
      have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp he) hb
      simp only [Nat.cast_add, Nat.cast_one, pow_succ] at hm ⊢
      nlinarith only [hm]

end
end CurrentAFT.TensorSupApproximation
