import AFT.TensorChannelFormula

/-! # Tensor contraction with different finite alphabets in each coordinate -/

namespace AFT
open scoped BigOperators Classical
noncomputable section

namespace FiniteDist
/-- A finite product law with genuinely dependent coordinate alphabets. -/
def dependentIndependent {Index : Type*} [Fintype Index] [DecidableEq Index]
    {Color : Index → Type*} [∀ i, Fintype (Color i)]
    (law : ∀ i, FiniteDist (Color i)) : FiniteDist ((i : Index) → Color i) where
  weight word := ∏ i, (law i).weight (word i)
  nonneg word := Finset.prod_nonneg fun i _ => (law i).nonneg (word i)
  sum_one := by
    rw [← Fintype.prod_sum]
    simp only [sum_one, Finset.prod_const_one]

@[simp] theorem dependentIndependent_weight {Index : Type*} [Fintype Index] [DecidableEq Index]
    {Color : Index → Type*} [∀ i, Fintype (Color i)]
    (law : ∀ i, FiniteDist (Color i)) (word : ∀ i, Color i) :
    (dependentIndependent law).weight word = ∏ i, (law i).weight (word i) := rfl
end FiniteDist

namespace DependentTensorChannel
set_option backward.isDefEq.respectTransparency false

private theorem expectation_cons (count : ℕ) {Color : Fin (count + 1) → Type*}
    [∀ i, Fintype (Color i)] (law : ∀ i, FiniteDist (Color i))
    (value : ((i : Fin (count + 1)) → Color i) → ℝ) :
    (FiniteDist.dependentIndependent law).expectation value =
      (law 0).expectation (fun first =>
        (FiniteDist.dependentIndependent (fun index => law index.succ)).expectation
          (fun rest => value (Fin.cons first rest))) := by
  unfold FiniteDist.expectation FiniteDist.dependentIndependent
  rw [← Equiv.sum_comp (Fin.consEquiv Color), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro first _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rest _
  change (∏ index, (law index).weight ((Fin.cons first rest : ∀ i, Color i) index)) * value (Fin.cons first rest) = _
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  ring

/-- Successive contraction of dependent local channels. -/
def applyFin : (count : ℕ) → {Input Output : Fin count → Type*} →
    (∀ i, (Input i → ℝ) →ₗ[ℝ] (Output i → ℝ)) →
    (((i : Fin count) → Input i) → ℝ) → ((i : Fin count) → Output i) → ℝ
  | 0, _, _, _, kernel, _ => kernel (fun i => Fin.elim0 i)
  | count + 1, _, _, channel, kernel, output =>
      channel 0 (fun first => applyFin count (fun index => channel index.succ)
        (fun rest => kernel (Fin.cons first rest)) (fun index => output index.succ)) (output 0)

@[simp] theorem applyFin_cons (count : ℕ) {Input Output : Fin (count + 1) → Type*}
    (channel : ∀ i, (Input i → ℝ) →ₗ[ℝ] (Output i → ℝ))
    (kernel : ((i : Fin (count + 1)) → Input i) → ℝ)
    (first : Output 0) (rest : ∀ i : Fin count, Output i.succ) :
    applyFin (count + 1) channel kernel (Fin.cons first rest) =
      channel 0 (fun input => applyFin count (fun index => channel index.succ)
        (fun tail => kernel (Fin.cons input tail)) rest) first := by
  simp only [applyFin, Fin.cons_zero, Fin.cons_succ]

private theorem expectation_mono {Sample : Type*} [Fintype Sample]
    (law : FiniteDist Sample) {first second : Sample → ℝ} (h : ∀ point, first point ≤ second point) :
    law.expectation first ≤ law.expectation second :=
  Finset.sum_le_sum fun point _ => mul_le_mul_of_nonneg_left (h point) (law.nonneg point)

/-- The Hilbert norm of the complete tensor channel is the product of its
local bounds. This applies to every joint kernel, including nonseparable
kernels with arbitrary dependencies among the distinguished coordinates. -/
theorem energy_fin_le (count : ℕ)
    (Input Output : Fin count → Type*) [∀ i, Fintype (Input i)] [∀ i, Fintype (Output i)]
    (input : ∀ i, FiniteDist (Input i)) (output : ∀ i, FiniteDist (Output i))
    (channel : ∀ i, (Input i → ℝ) →ₗ[ℝ] (Output i → ℝ))
    (bound : Fin count → ℝ)
    (hchannel : ∀ index kernel, (output index).l2Sq (channel index kernel) ≤
      bound index ^ 2 * (input index).l2Sq kernel)
    (kernel : ((i : Fin count) → Input i) → ℝ) :
    (FiniteDist.dependentIndependent output).l2Sq (applyFin count channel kernel) ≤
      (∏ index, bound index ^ 2) * (FiniteDist.dependentIndependent input).l2Sq kernel := by
  induction count with
  | zero =>
    have hconstant : kernel = fun _ => kernel (fun i => Fin.elim0 i) := by
      funext word
      congr 1
      funext index
      exact Fin.elim0 index
    rw [hconstant]
    simp only [applyFin, FiniteDist.l2Sq, FiniteDist.expectation_const, Fin.prod_univ_zero, one_mul]
    exact le_rfl
  | succ count ih =>
    let tailInput := FiniteDist.dependentIndependent (fun index : Fin count => input index.succ)
    let tailOutput := FiniteDist.dependentIndependent (fun index : Fin count => output index.succ)
    let tailValue := fun first rest => applyFin count (fun index => channel index.succ)
      (fun tail => kernel (Fin.cons first tail)) rest
    have htail (first : Input 0) : tailOutput.l2Sq (tailValue first) ≤
        (∏ index : Fin count, bound index.succ ^ 2) * tailInput.l2Sq (fun rest => kernel (Fin.cons first rest)) :=
      ih (fun index => Input index.succ) (fun index => Output index.succ) (fun index => input index.succ) (fun index => output index.succ)
        (fun index => channel index.succ) (fun index => bound index.succ)
        (fun index => hchannel index.succ) _
    have hsplit : (FiniteDist.dependentIndependent output).l2Sq (applyFin (count + 1) channel kernel) =
        tailOutput.expectation (fun rest => (output 0).l2Sq (channel 0 (fun first => tailValue first rest))) := by
      unfold FiniteDist.l2Sq
      rw [expectation_cons]
      simp only [applyFin_cons]
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
        exact (expectation_cons count input (fun word => kernel word ^ 2)).symm


/-- The recursive tensor is the literal full joint signed response. -/
theorem applyFin_formula (count : ℕ) {Input Output : Fin count → Type*}
    [∀ i, Fintype (Input i)]
    (channel : ∀ i, (Input i → ℝ) →ₗ[ℝ] (Output i → ℝ))
    (kernel : ((i : Fin count) → Input i) → ℝ) (output : ∀ i, Output i) :
    applyFin count channel kernel output =
      ∑ point, kernel point * ∏ index, channel index (Pi.single (point index) 1) (output index) := by
  induction count with
  | zero =>
    simp only [applyFin, Fin.prod_univ_zero, mul_one, Fintype.sum_unique]
    congr 1
  | succ count ih =>
    rw [show applyFin (count + 1) channel kernel output = channel 0
      (fun first => applyFin count (fun index => channel index.succ)
        (fun rest => kernel (Fin.cons first rest)) (fun index => output index.succ)) (output 0) from rfl]
    rw [TensorChannel.channel_sum_single]
    simp only [ih, Finset.sum_mul]
    rw [← Equiv.sum_comp (Fin.consEquiv Input), Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro first _
    apply Finset.sum_congr rfl
    intro rest _
    change (kernel (Fin.cons first rest) * ∏ x, channel x.succ (Pi.single (rest x) 1) (output x.succ)) *
      channel 0 (Pi.single first 1) (output 0) = _
    simp only [Fin.prod_univ_succ, Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, Fin.cons_succ]
    ring

variable {Index : Type*} [Fintype Index] [DecidableEq Index]
    {Input Output : Index → Type*} [∀ i, Fintype (Input i)] [∀ i, Fintype (Output i)]

/-- Simultaneous local linear channels acting on a genuinely joint input. -/
def apply (channel : ∀ i, (Input i → ℝ) →ₗ[ℝ] (Output i → ℝ))
    (kernel : ((i : Index) → Input i) → ℝ) (output : ∀ i, Output i) : ℝ :=
  ∑ point, kernel point * ∏ index, channel index (Pi.single (point index) 1) (output index)

omit [∀ i, Fintype (Output i)] in
private theorem apply_reindex {Index' : Type*} [Fintype Index'] [DecidableEq Index']
    (e : Index' ≃ Index) (channel : ∀ i, (Input i → ℝ) →ₗ[ℝ] (Output i → ℝ))
    (kernel : ((i : Index) → Input i) → ℝ) (output : ∀ i, Output i) :
    (∑ point : (i : Index') → Input (e i), kernel ((Equiv.piCongrLeft Input e) point) *
      ∏ i, channel (e i) (Pi.single (point i) 1) (output (e i))) = apply channel kernel output := by
  unfold apply
  rw [← (Equiv.piCongrLeft Input e).sum_comp]
  apply Finset.sum_congr rfl
  intro point _
  congr 1
  rw [← e.prod_comp]
  simp only [Equiv.piCongrLeft_apply_apply]

private theorem energy_reindex {Index' : Type*} [Fintype Index'] [DecidableEq Index']
    {Color : Index → Type*} [∀ i, Fintype (Color i)]
    (e : Index' ≃ Index) (law : ∀ i, FiniteDist (Color i))
    (kernel : ((i : Index) → Color i) → ℝ) :
    (FiniteDist.dependentIndependent (fun i => law (e i))).l2Sq
        (fun point => kernel ((Equiv.piCongrLeft Color e) point)) =
      (FiniteDist.dependentIndependent law).l2Sq kernel := by
  unfold FiniteDist.l2Sq FiniteDist.expectation
  rw [← (Equiv.piCongrLeft Color e).sum_comp]
  apply Finset.sum_congr rfl
  intro point _
  simp only [FiniteDist.dependentIndependent_weight]
  congr 1
  rw [← e.prod_comp]
  simp only [Equiv.piCongrLeft_apply_apply]

/-- The dependent tensor contraction has exactly the product of the local
Hilbert bounds, without a dimension factor or separability assumption. -/
theorem energy_le (input : ∀ i, FiniteDist (Input i)) (output : ∀ i, FiniteDist (Output i))
    (channel : ∀ i, (Input i → ℝ) →ₗ[ℝ] (Output i → ℝ)) (bound : Index → ℝ)
    (hchannel : ∀ index kernel, (output index).l2Sq (channel index kernel) ≤
      bound index ^ 2 * (input index).l2Sq kernel)
    (kernel : ((i : Index) → Input i) → ℝ) :
    (FiniteDist.dependentIndependent output).l2Sq (apply channel kernel) ≤
      (∏ index, bound index ^ 2) * (FiniteDist.dependentIndependent input).l2Sq kernel := by
  let e : Fin (Fintype.card Index) ≃ Index := (Fintype.equivFin Index).symm
  have hh := energy_fin_le (Fintype.card Index) (fun i => Input (e i)) (fun i => Output (e i))
    (fun i => input (e i)) (fun i => output (e i)) (fun i => channel (e i))
    (fun i => bound (e i)) (fun i => hchannel (e i))
    (fun word => kernel ((Equiv.piCongrLeft Input e) word))
  have heq : applyFin (Fintype.card Index) (fun i => channel (e i))
        (fun word => kernel ((Equiv.piCongrLeft Input e) word)) =
      fun word => apply channel kernel ((Equiv.piCongrLeft Output e) word) := by
    funext word
    rw [applyFin_formula]
    simpa only [Equiv.piCongrLeft_apply_apply] using
      apply_reindex e channel kernel ((Equiv.piCongrLeft Output e) word)
  rw [heq, energy_reindex, energy_reindex] at hh
  rw [e.prod_comp (fun i => bound i ^ 2)] at hh
  exact hh

end DependentTensorChannel
end
end AFT
