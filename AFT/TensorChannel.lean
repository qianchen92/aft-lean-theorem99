import AFT.FiniteConcentration
import AFT.FiniteExpectationAlgebra

/-! # Tensor Hilbert operator bounds for arbitrary joint finite kernels -/

namespace AFT.TensorChannel

open scoped BigOperators Classical
noncomputable section

variable {Input Output : Type*} [Fintype Input] [Fintype Output]

/-- Apply finite local linear channels to all coordinates of one arbitrary
joint kernel. No product decomposition of that kernel is used. -/
def apply : (count : ℕ) →
    (Fin count → (Input → ℝ) →ₗ[ℝ] (Output → ℝ)) →
    ((Fin count → Input) → ℝ) → (Fin count → Output) → ℝ
  | 0, _, kernel, _ => kernel Fin.elim0
  | count + 1, channel, kernel, output =>
      channel 0 (fun first => apply count (fun index => channel index.succ)
        (fun rest => kernel (Fin.cons first rest)) (fun index => output index.succ)) (output 0)

omit [Fintype Input] [Fintype Output] in
@[simp] theorem apply_cons (count : ℕ)
    (channel : Fin (count + 1) → (Input → ℝ) →ₗ[ℝ] (Output → ℝ))
    (kernel : (Fin (count + 1) → Input) → ℝ) (first : Output) (rest : Fin count → Output) :
    apply (count + 1) channel kernel (Fin.cons first rest) =
      channel 0 (fun input => apply count (fun index => channel index.succ)
        (fun tail => kernel (Fin.cons input tail)) rest) first := by
  simp only [apply, Fin.cons_zero, Fin.cons_succ]

private theorem expectation_mono {Sample : Type*} [Fintype Sample]
    (law : FiniteDist Sample) {first second : Sample → ℝ} (h : ∀ point, first point ≤ second point) :
    law.expectation first ≤ law.expectation second :=
  Finset.sum_le_sum fun point _ => mul_le_mul_of_nonneg_left (h point) (law.nonneg point)

/-- The Hilbert norm of the complete tensor channel is the product of its
local bounds. This applies to every joint kernel, including nonseparable
kernels with arbitrary dependencies among the distinguished coordinates. -/
theorem energy_le (count : ℕ) (input : Fin count → FiniteDist Input)
    (output : Fin count → FiniteDist Output)
    (channel : Fin count → (Input → ℝ) →ₗ[ℝ] (Output → ℝ))
    (bound : Fin count → ℝ)
    (hchannel : ∀ index kernel, (output index).l2Sq (channel index kernel) ≤
      bound index ^ 2 * (input index).l2Sq kernel)
    (kernel : (Fin count → Input) → ℝ) :
    (FiniteDist.independent output).l2Sq (apply count channel kernel) ≤
      (∏ index, bound index ^ 2) * (FiniteDist.independent input).l2Sq kernel := by
  induction count with
  | zero =>
    have hconstant : kernel = fun _ => kernel Fin.elim0 := by
      funext word
      congr 1
      funext index
      exact Fin.elim0 index
    rw [hconstant]
    simp only [apply, FiniteDist.l2Sq, FiniteDist.expectation_const, Fin.prod_univ_zero, one_mul]
    exact le_rfl
  | succ count ih =>
    let tailInput := FiniteDist.independent (fun index : Fin count => input index.succ)
    let tailOutput := FiniteDist.independent (fun index : Fin count => output index.succ)
    let tailValue := fun first rest => apply count (fun index => channel index.succ)
      (fun tail => kernel (Fin.cons first tail)) rest
    have htail (first : Input) : tailOutput.l2Sq (tailValue first) ≤
        (∏ index : Fin count, bound index.succ ^ 2) * tailInput.l2Sq (fun rest => kernel (Fin.cons first rest)) :=
      ih (fun index => input index.succ) (fun index => output index.succ)
        (fun index => channel index.succ) (fun index => bound index.succ)
        (fun index => hchannel index.succ) _
    have hsplit : (FiniteDist.independent output).l2Sq (apply (count + 1) channel kernel) =
        tailOutput.expectation (fun rest => (output 0).l2Sq (channel 0 (fun first => tailValue first rest))) := by
      unfold FiniteDist.l2Sq
      rw [FiniteConcentration.expectation_cons]
      simp only [apply_cons]
      exact FiniteDist.expectation_comm _ _ _
    rw [hsplit]
    calc
      _ ≤ tailOutput.expectation (fun rest => bound 0 ^ 2 * (input 0).l2Sq (fun first => tailValue first rest)) :=
        expectation_mono tailOutput (fun rest => hchannel 0 _)
      _ = bound 0 ^ 2 * (input 0).expectation (fun first => tailOutput.l2Sq (tailValue first)) := by
        rw [FiniteDist.expectation_const_mul]
        congr 1
        exact FiniteDist.expectation_comm _ _ _
      _ ≤ bound 0 ^ 2 * (input 0).expectation (fun first =>
          (∏ index : Fin count, bound index.succ ^ 2) * tailInput.l2Sq (fun rest => kernel (Fin.cons first rest))) :=
        mul_le_mul_of_nonneg_left (expectation_mono (input 0) htail) (sq_nonneg _)
      _ = _ := by
        rw [FiniteDist.expectation_const_mul, Fin.prod_univ_succ]
        rw [mul_assoc]
        congr 2
        unfold FiniteDist.l2Sq
        exact (FiniteConcentration.expectation_cons count input (fun word => kernel word ^ 2)).symm


/-- The same tensor estimate with counting measure on the coefficient
coordinates. This is the form used by finite Gaussian/Fock coefficient
spaces; no output-alphabet cardinality factor is introduced. -/
theorem energy_counting_le (count : ℕ) (input : Fin count → FiniteDist Input)
    (channel : Fin count → (Input → ℝ) →ₗ[ℝ] (Output → ℝ))
    (bound : Fin count → ℝ)
    (hchannel : ∀ index kernel, (∑ output, (channel index kernel output) ^ 2) ≤
      bound index ^ 2 * (input index).l2Sq kernel)
    (kernel : (Fin count → Input) → ℝ) :
    (∑ output, apply count channel kernel output ^ 2) ≤
      (∏ index, bound index ^ 2) * (FiniteDist.independent input).l2Sq kernel := by
  induction count with
  | zero =>
    have hconstant : kernel = fun _ => kernel Fin.elim0 := by
      funext word
      congr 1
      funext index
      exact Fin.elim0 index
    rw [hconstant]
    simp only [apply, FiniteDist.l2Sq, FiniteDist.expectation_const, Fin.prod_univ_zero, one_mul,
      Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, pow_zero, Nat.cast_one, nsmul_eq_mul]
    exact le_rfl
  | succ count ih =>
    let tailInput := FiniteDist.independent (fun index : Fin count => input index.succ)
    let tailValue := fun first rest => apply count (fun index => channel index.succ)
      (fun tail => kernel (Fin.cons first tail)) rest
    have htail (first : Input) : (∑ rest, tailValue first rest ^ 2) ≤
        (∏ index : Fin count, bound index.succ ^ 2) * tailInput.l2Sq (fun rest => kernel (Fin.cons first rest)) :=
      ih (fun index => input index.succ) (fun index => channel index.succ)
        (fun index => bound index.succ) (fun index => hchannel index.succ) _
    have hsplit : (∑ output, apply (count + 1) channel kernel output ^ 2) =
        ∑ rest : Fin count → Output, ∑ output, (channel 0 (fun first => tailValue first rest) output) ^ 2 := by
      rw [← (Fin.consEquiv (fun _ : Fin (count + 1) => Output)).sum_comp]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      rfl
    rw [hsplit]
    calc
      _ ≤ ∑ rest : Fin count → Output, bound 0 ^ 2 * (input 0).l2Sq (fun first => tailValue first rest) :=
        Finset.sum_le_sum fun rest _ => hchannel 0 _
      _ = bound 0 ^ 2 * (input 0).expectation (fun first => ∑ rest, tailValue first rest ^ 2) := by
        rw [← Finset.mul_sum]
        congr 1
        unfold FiniteDist.l2Sq FiniteDist.expectation
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
      _ ≤ bound 0 ^ 2 * (input 0).expectation (fun first =>
          (∏ index : Fin count, bound index.succ ^ 2) * tailInput.l2Sq (fun rest => kernel (Fin.cons first rest))) :=
        mul_le_mul_of_nonneg_left (expectation_mono (input 0) htail) (sq_nonneg _)
      _ = _ := by
        rw [FiniteDist.expectation_const_mul, Fin.prod_univ_succ, mul_assoc]
        congr 2
        unfold FiniteDist.l2Sq
        exact (FiniteConcentration.expectation_cons count input (fun word => kernel word ^ 2)).symm

/-- A literal finite signed channel, with the actual input weights included. -/
def ofKernel (input : FiniteDist Input) (matrix : Input → Output → ℝ) :
    (Input → ℝ) →ₗ[ℝ] (Output → ℝ) where
  toFun kernel := fun output => input.expectation (fun point => matrix point output * kernel point)
  map_add' first second := by
    funext output
    simp only [Pi.add_apply, mul_add, FiniteDist.expectation_add]
  map_smul' scalar kernel := by
    funext output
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, FiniteDist.expectation, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro point _
    ring

omit [Fintype Output] in
/-- The tensor operator is exactly the joint signed pushforward through the
local channels, with one expectation over the original joint input kernel. -/
theorem apply_ofKernel (count : ℕ) (input : Fin count → FiniteDist Input)
    (matrix : Fin count → Input → Output → ℝ) (kernel : (Fin count → Input) → ℝ)
    (output : Fin count → Output) :
    apply count (fun index => ofKernel (input index) (matrix index)) kernel output =
      (FiniteDist.independent input).expectation (fun point => kernel point * ∏ index, matrix index (point index) (output index)) := by
  induction count with
  | zero =>
    have hpoint (point : Fin 0 → Input) : point = Fin.elim0 := funext fun index => Fin.elim0 index
    simp only [apply, Fin.prod_univ_zero, mul_one, hpoint, FiniteDist.expectation_const]
  | succ count ih =>
    rw [FiniteConcentration.expectation_cons]
    change (input 0).expectation (fun first => matrix 0 first (output 0) *
      apply count (fun index => ofKernel (input index.succ) (matrix index.succ))
        (fun rest => kernel (Fin.cons first rest)) (fun index => output index.succ)) = _
    simp only [ih, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    unfold FiniteDist.expectation
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro first _
    apply Finset.sum_congr rfl
    intro rest _
    ring

end
end AFT.TensorChannel
