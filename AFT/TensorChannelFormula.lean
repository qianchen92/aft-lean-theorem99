import AFT.ChannelCentering

/-! # The tensor operator is the literal finite signed joint response -/

namespace AFT.TensorChannel
open scoped BigOperators Classical
noncomputable section
variable {Input Output : Type*} [Fintype Input]

/-- A local linear response is the sum of its responses to the actual input
coordinate vectors. This does not impose any separability on joint inputs. -/
theorem channel_sum_single (channel : (Input → ℝ) →ₗ[ℝ] (Output → ℝ))
    (kernel : Input → ℝ) (output : Output) :
    channel kernel output = ∑ point, kernel point * channel (Pi.single point 1) output := by
  have heq : kernel = ∑ point, kernel point • (Pi.single point (1 : ℝ) : Input → ℝ) := by
    funext point
    simp [Pi.single_apply]
  conv_lhs => rw [heq, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- The actual finite tensor response is a single signed sum over the full
joint input word, rather than a rank-one representation of the kernel. -/
theorem apply_formula (count : ℕ)
    (channel : Fin count → (Input → ℝ) →ₗ[ℝ] (Output → ℝ))
    (kernel : (Fin count → Input) → ℝ) (output : Fin count → Output) :
    apply count channel kernel output =
      ∑ point, kernel point * ∏ index, channel index (Pi.single (point index) 1) (output index) := by
  induction count with
  | zero =>
    simp only [apply, Fin.prod_univ_zero, mul_one, Fintype.sum_unique]
    congr 1
  | succ count ih =>
    rw [show apply (count + 1) channel kernel output = channel 0
      (fun first => apply count (fun index => channel index.succ)
        (fun rest => kernel (Fin.cons first rest)) (fun index => output index.succ)) (output 0) from rfl]
    rw [channel_sum_single]
    simp only [ih, Finset.sum_mul]
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (count + 1) => Input)), Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro first _
    apply Finset.sum_congr rfl
    intro rest _
    change (kernel (Fin.cons first rest) * ∏ x, channel x.succ (Pi.single (rest x) 1) (output x.succ)) *
      channel 0 (Pi.single first 1) (output 0) = _
    simp only [Fin.prod_univ_succ, Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, Fin.cons_succ]
    ring

/-- The exact finite formula is independent of the chosen decidable equality
on its finite coordinate set. -/
theorem apply_formula_instance (count : ℕ) [decision : DecidableEq (Fin count)]
    (channel : Fin count → (Input → ℝ) →ₗ[ℝ] (Output → ℝ))
    (kernel : (Fin count → Input) → ℝ) (output : Fin count → Output) :
    apply count channel kernel output =
      ∑ point, kernel point * ∏ index, channel index (Pi.single (point index) 1) (output index) := by
  have hd : decision = instDecidableEqFin count := Subsingleton.elim _ _
  cases hd
  exact apply_formula count channel kernel output

/-- Instance-independent tensor bound for the original physical response of
an arbitrary canonical joint kernel. -/
theorem canonical_energy_counting_le_instance [Fintype Output] [Nonempty Input]
    (count : ℕ) [decision : DecidableEq (Fin count)] (input : Fin count → FiniteDist Input)
    (channel : Fin count → (Input → ℝ) →ₗ[ℝ] (Output → ℝ)) (bound : Fin count → ℝ)
    (hchannel : ∀ index kernel, (input index).expectation kernel = 0 →
      (∑ output, channel index kernel output ^ 2) ≤ bound index ^ 2 * (input index).l2Sq kernel)
    (kernel : (Fin count → Input) → ℝ) (hcanonical : Hoeffding.Canonical input Finset.univ kernel) :
    (∑ output, apply count channel kernel output ^ 2) ≤
      (∏ index, bound index ^ 2) * (FiniteDist.independent input).l2Sq kernel := by
  have hd : decision = instDecidableEqFin count := Subsingleton.elim _ _
  cases hd
  exact canonical_energy_counting_le count input channel bound hchannel kernel hcanonical

end
end AFT.TensorChannel
