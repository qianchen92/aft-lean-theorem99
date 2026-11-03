import AFT.MixedCoordinateOperator

/-! # Literal coordinate composition and finite tensor inverse iteration -/

namespace AFT.MixedKernel

open scoped BigOperators Classical

noncomputable section

variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

/-- The actual coordinate operation is linear on the complete joint kernel. -/
def partialInputLinear (slot : Slot) (operator : Module.End ℝ (Color → ℝ))
    (primary : Color → ℝ) : Module.End ℝ ((Slot → Color) → ℝ) where
  toFun := partialInputOperator slot operator primary
  map_add' first second := by
    funext word
    unfold partialInputOperator
    have heq : (fun input => primary input * (first + second) (Function.update word slot input)) =
        (fun input => primary input * first (Function.update word slot input)) +
        (fun input => primary input * second (Function.update word slot input)) := by funext input; simp [mul_add]
    rw [heq, map_add]
    simp only [Pi.add_apply, add_div]
  map_smul' scalar kernel := by
    funext word
    unfold partialInputOperator
    have heq : (fun input => primary input * (scalar • kernel) (Function.update word slot input)) =
        scalar • (fun input => primary input * kernel (Function.update word slot input)) := by funext input; simp [mul_left_comm]
    rw [heq, map_smul]
    simp only [Pi.smul_apply, smul_eq_mul, mul_div_assoc, RingHom.id_apply]

omit [Fintype Slot] [Fintype Color] in
@[simp] theorem partialInputOperator_id (slot : Slot) (primary : Color → ℝ)
    (hprimary : ∀ color, primary color ≠ 0) (kernel : (Slot → Color) → ℝ) :
    partialInputOperator slot LinearMap.id primary kernel = kernel := by
  funext word
  simp only [partialInputOperator, LinearMap.id_apply, Function.update_eq_self]
  exact mul_div_cancel_left₀ _ (hprimary _)

omit [Fintype Slot] [Fintype Color] in
/-- Composition uses the actual profiles and cancels their exact reference
weights. No quotient by an output image is involved. -/
theorem partialInputOperator_comp (slot : Slot) (first second : Module.End ℝ (Color → ℝ))
    (primary : Color → ℝ) (hprimary : ∀ color, primary color ≠ 0)
    (kernel : (Slot → Color) → ℝ) :
    partialInputOperator slot first primary (partialInputOperator slot second primary kernel) =
      partialInputOperator slot (first.comp second) primary kernel := by
  funext word
  unfold partialInputOperator
  have heq : (fun input => primary input *
      (second (fun inner => primary inner * kernel (Function.update (Function.update word slot input) slot inner))
        ((Function.update word slot input) slot) / primary ((Function.update word slot input) slot))) =
      second (fun input => primary input * kernel (Function.update word slot input)) := by
    funext input
    simp only [Function.update_self, Function.update_idem]
    exact mul_div_cancel₀ _ (hprimary input)
  rw [heq]
  rfl

omit [Fintype Slot] [Fintype Color] in
/-- The finite profile inverse is also an exact inverse on every joint input. -/
theorem partialInputOperator_inverse (slot : Slot) (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ))
    (primary : Color → ℝ) (hprimary : ∀ color, primary color ≠ 0)
    (kernel : (Slot → Color) → ℝ) :
    partialInputOperator slot operator.toLinearMap primary
      (partialInputOperator slot operator.symm.toLinearMap primary kernel) = kernel := by
  rw [partialInputOperator_comp slot _ _ _ hprimary]
  have heq : operator.toLinearMap.comp operator.symm.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro profile
    exact operator.apply_symm_apply profile
  rw [heq, partialInputOperator_id slot primary hprimary]

/-- A specified ordered finite list retains all coordinate actions literally. -/
def inputIteration (coordinates : List Slot) (operator : Slot → Module.End ℝ (Color → ℝ))
    (reference : Slot → FiniteDist Color) : Module.End ℝ ((Slot → Color) → ℝ) :=
  coordinates.foldr (fun slot accumulated => (partialInputLinear slot (operator slot) (reference slot).weight).comp accumulated)
    LinearMap.id

omit [Fintype Slot] in
@[simp] theorem inputIteration_nil (operator : Slot → Module.End ℝ (Color → ℝ))
    (reference : Slot → FiniteDist Color) : inputIteration [] operator reference = LinearMap.id := rfl

omit [Fintype Slot] in
@[simp] theorem inputIteration_cons (slot : Slot) (coordinates : List Slot)
    (operator : Slot → Module.End ℝ (Color → ℝ)) (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) :
    inputIteration (slot :: coordinates) operator reference kernel =
      partialInputOperator slot (operator slot) (reference slot).weight
        (inputIteration coordinates operator reference kernel) := rfl

/-- Tensorizing a uniform one-coordinate activity bound incurs only its
fixed-order power, with every mixed input fiber included. -/
theorem inputIteration_activity_le (coordinates : List Slot)
    (operator : Slot → Module.End ℝ (Color → ℝ)) (reference : Slot → FiniteDist Color)
    (rates : Slot → ℝ) (constant : ℝ) (hconstant : 0 ≤ constant)
    (hoperator : ∀ slot ∈ coordinates, ∀ kernel : (Slot → Color) → ℝ,
      activity rates reference (partialInputOperator slot (operator slot) (reference slot).weight kernel) ≤
        constant * activity rates reference kernel)
    (kernel : (Slot → Color) → ℝ) :
    activity rates reference (inputIteration coordinates operator reference kernel) ≤
      constant ^ coordinates.length * activity rates reference kernel := by
  induction coordinates with
  | nil => simp [inputIteration]
  | cons slot coordinates ih =>
    rw [inputIteration_cons, List.length_cons, pow_succ']
    apply (hoperator slot (List.mem_cons_self ..) _).trans
    have hh := ih (fun other hmem => hoperator other (List.mem_cons_of_mem _ hmem))
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh hconstant

end
end AFT.MixedKernel
