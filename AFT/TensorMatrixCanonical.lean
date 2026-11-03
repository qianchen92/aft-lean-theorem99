import AFT.TensorMixedSchur

/-! # Actual canonicality is preserved by finite mean-preserving matrix channels -/
namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Input Output : Type*} [Fintype Slot] [DecidableEq Slot]
  [Fintype Input] [Fintype Output]

omit [Fintype Output] in
private theorem centered_sum_product_zero (reference : Slot → FiniteDist Input)
    (kernel : (Slot → Input) → ℝ) (hc : Hoeffding.Canonical reference Finset.univ kernel)
    (slot : Slot) (factors : Slot → Input → ℝ) :
    (∑ word, (reference slot).weight (word slot) * kernel word *
      ∏ other ∈ Finset.univ.erase slot, factors other (word other)) = 0 := by
  cases Subsingleton.elim (inferInstance : DecidableEq Slot) (Classical.decEq Slot)
  haveI : Nonempty Input := by
    by_contra hh
    haveI : IsEmpty Input := not_nonempty_iff.mp hh
    have hm := (reference slot).sum_one
    simp at hm
  rw [← (Equiv.funSplitAt slot Input).symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro rest _
  let base := (Equiv.funSplitAt slot Input).symm (Classical.arbitrary Input, rest)
  have hu (point : Input) : (Equiv.funSplitAt slot Input).symm (point, rest) = Function.update base slot point := by
    funext other
    by_cases ho : other = slot
    · subst other; simp [base, Equiv.funSplitAt, Equiv.piSplitAt]
    · simp [base, Equiv.funSplitAt, Equiv.piSplitAt, ho]
  have hf (point : Input) : (∏ other ∈ Finset.univ.erase slot,
      factors other (Function.update base slot point other)) =
      ∏ other ∈ Finset.univ.erase slot, factors other (base other) := by
    apply Finset.prod_congr rfl
    intro other ho
    rw [Function.update_of_ne (Finset.mem_erase.mp ho).1]
  simp only [hu, Function.update_self, hf, ← Finset.sum_mul, hc.2 slot (Finset.mem_univ slot) base, zero_mul]

/-- A scalar expectation identity suffices to preserve every conditional
zero-mean input direction in the full tensor channel. -/
theorem matrixApply_canonical (input : Slot → FiniteDist Input)
    (output : Slot → FiniteDist Output) (matrix : Slot → Input → Output → ℝ)
    (scalar : Slot → ℝ)
    (hmean : ∀ slot point, (output slot).expectation (matrix slot point) = scalar slot * (input slot).weight point)
    (kernel : (Slot → Input) → ℝ) (hc : Hoeffding.Canonical input Finset.univ kernel) :
    Hoeffding.Canonical output Finset.univ (matrixApply matrix kernel) := by
  cases Subsingleton.elim (inferInstance : DecidableEq Slot) (Classical.decEq Slot)
  constructor
  · intro first second hh
    have he : first = second := funext fun slot => hh slot (Finset.mem_univ slot)
    rw [he]
  · intro slot _ values
    have hlocal (word : Slot → Input) :
        (∑ value, (output slot).weight value * ∏ other, matrix other (word other) (Function.update values slot value other)) =
        (scalar slot * (input slot).weight (word slot)) *
          ∏ other ∈ Finset.univ.erase slot, matrix other (word other) (values other) := by
      have he (value : Output) : (∏ other, matrix other (word other) (Function.update values slot value other)) =
          matrix slot (word slot) value * ∏ other ∈ Finset.univ.erase slot, matrix other (word other) (values other) := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ slot), Function.update_self]
        congr 1
        apply Finset.prod_congr rfl
        intro other ho
        rw [Function.update_of_ne (Finset.mem_erase.mp ho).1]
      simp only [he, ← mul_assoc, ← Finset.sum_mul]
      rw [show (∑ value, (output slot).weight value * matrix slot (word slot) value) =
        scalar slot * (input slot).weight (word slot) from hmean slot (word slot)]
    change (∑ value, (output slot).weight value * ∑ word,
      kernel word * ∏ other, matrix other (word other) (Function.update values slot value other)) = 0
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have he : (∑ word, ∑ value, (output slot).weight value *
        (kernel word * ∏ other, matrix other (word other) (Function.update values slot value other))) =
        scalar slot * ∑ word, (input slot).weight (word slot) * kernel word *
          ∏ other ∈ Finset.univ.erase slot, matrix other (word other) (values other) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro word _
      calc
        _ = kernel word * ∑ value, (output slot).weight value *
            ∏ other, matrix other (word other) (Function.update values slot value other) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro value _
          ring
        _ = _ := by rw [hlocal]; ring
    rw [he, centered_sum_product_zero input kernel hc slot (fun other point => matrix other point (values other)), mul_zero]
/-- A single mean-preserving coordinate is sufficient for conditional
centering, regardless of the laws at all remaining output coordinates. -/
theorem matrixApply_centered_at (input : Slot → FiniteDist Input)
    (matrix : Slot → Input → Output → ℝ) (slot : Slot)
    (output : FiniteDist Output) (scalar : ℝ)
    (hmean : ∀ point, output.expectation (matrix slot point) = scalar * (input slot).weight point)
    (kernel : (Slot → Input) → ℝ) (hc : Hoeffding.Canonical input Finset.univ kernel)
    (values : Slot → Output) :
    (∑ value, output.weight value * matrixApply matrix kernel (Function.update values slot value)) = 0 := by
  cases Subsingleton.elim (inferInstance : DecidableEq Slot) (Classical.decEq Slot)
  have hlocal (word : Slot → Input) :
      (∑ value, output.weight value * ∏ other, matrix other (word other) (Function.update values slot value other)) =
      (scalar * (input slot).weight (word slot)) *
        ∏ other ∈ Finset.univ.erase slot, matrix other (word other) (values other) := by
    have he (value : Output) : (∏ other, matrix other (word other) (Function.update values slot value other)) =
        matrix slot (word slot) value * ∏ other ∈ Finset.univ.erase slot, matrix other (word other) (values other) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ slot), Function.update_self]
      congr 1
      apply Finset.prod_congr rfl
      intro other ho
      rw [Function.update_of_ne (Finset.mem_erase.mp ho).1]
    simp only [he, ← mul_assoc, ← Finset.sum_mul]
    rw [show (∑ value, output.weight value * matrix slot (word slot) value) =
      scalar * (input slot).weight (word slot) from hmean (word slot)]
  change (∑ value, output.weight value * ∑ word,
    kernel word * ∏ other, matrix other (word other) (Function.update values slot value other)) = 0
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have he : (∑ word, ∑ value, output.weight value *
      (kernel word * ∏ other, matrix other (word other) (Function.update values slot value other))) =
      scalar * ∑ word, (input slot).weight (word slot) * kernel word *
        ∏ other ∈ Finset.univ.erase slot, matrix other (word other) (values other) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro word _
    calc
      _ = kernel word * ∑ value, output.weight value *
          ∏ other, matrix other (word other) (Function.update values slot value other) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro value _
        ring
      _ = _ := by rw [hlocal]; ring
  rw [he, centered_sum_product_zero input kernel hc slot (fun other point => matrix other point (values other)), mul_zero]

end
end AFT.MixedKernel
