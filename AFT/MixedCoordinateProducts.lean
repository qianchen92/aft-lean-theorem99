import AFT.MixedCoordinateIteration

/-! # Exact action of coordinate profile operators on a spanning product family -/

namespace AFT.MixedKernel

open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

def productKernel (functions : Slot → Color → ℝ) (word : Slot → Color) : ℝ :=
  ∏ slot, functions slot (word slot)

def densityConjugate (operator : Module.End ℝ (Color → ℝ)) (reference : Color → ℝ) :
    Module.End ℝ (Color → ℝ) where
  toFun kernel := fun color => operator (fun input => reference input * kernel input) color / reference color
  map_add' first second := by
    have heq : (fun color => reference color * (first + second) color) =
        (fun color => reference color * first color) + (fun color => reference color * second color) := by
      funext color; simp [mul_add]
    funext color
    change operator (fun input => reference input * (first + second) input) color / reference color = _
    rw [heq, map_add]
    simp only [Pi.add_apply, add_div]
  map_smul' scalar kernel := by
    have heq : (fun color => reference color * (scalar • kernel) color) =
        scalar • (fun color => reference color * kernel color) := by
      funext color; simp [mul_left_comm]
    funext color
    change operator (fun input => reference input * (scalar • kernel) input) color / reference color = _
    rw [heq, map_smul]
    simp only [Pi.smul_apply, smul_eq_mul, mul_div_assoc, RingHom.id_apply]

omit [Fintype Color] in
theorem productKernel_update_word (functions : Slot → Color → ℝ) (word : Slot → Color)
    (slot : Slot) (color : Color) :
    productKernel functions (Function.update word slot color) =
      functions slot color * ∏ other ∈ Finset.univ.erase slot, functions other (word other) := by
  unfold productKernel
  rw [← Finset.mul_prod_erase Finset.univ (fun other => functions other ((Function.update word slot color) other))
    (Finset.mem_univ slot)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro other ho
  rw [Function.update_of_ne (Finset.mem_erase.mp ho).1]

omit [Fintype Color] in
theorem productKernel_update_function (functions : Slot → Color → ℝ) (word : Slot → Color)
    (slot : Slot) (function : Color → ℝ) :
    productKernel (Function.update functions slot function) word =
      function (word slot) * ∏ other ∈ Finset.univ.erase slot, functions other (word other) := by
  unfold productKernel
  rw [← Finset.mul_prod_erase Finset.univ (fun other => (Function.update functions slot function) other (word other))
    (Finset.mem_univ slot)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro other ho
  rw [Function.update_of_ne (Finset.mem_erase.mp ho).1]

omit [Fintype Color] in
theorem partialInputOperator_product (slot : Slot) (operator : Module.End ℝ (Color → ℝ))
    (reference : Color → ℝ) (functions : Slot → Color → ℝ) :
    partialInputOperator slot operator reference (productKernel functions) =
      productKernel (Function.update functions slot (densityConjugate operator reference (functions slot))) := by
  funext word
  rw [productKernel_update_function]
  simp only [partialInputOperator, productKernel_update_word]
  have heq : (fun color => reference color *
      (functions slot color * ∏ other ∈ Finset.univ.erase slot, functions other (word other))) =
      (∏ other ∈ Finset.univ.erase slot, functions other (word other)) •
        (fun color => reference color * functions slot color) := by
    funext color
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [heq, map_smul]
  simp only [Pi.smul_apply, smul_eq_mul, densityConjugate, LinearMap.coe_mk, AddHom.coe_mk]
  ring

/-- Distinct coordinate operations act on the corresponding product
factors. This is later extended linearly to every joint input kernel. -/
theorem inputIteration_product (coordinates : List Slot) (hnodup : coordinates.Nodup)
    (operator : Slot → Module.End ℝ (Color → ℝ)) (reference : Slot → FiniteDist Color)
    (functions : Slot → Color → ℝ) :
    inputIteration coordinates operator reference (productKernel functions) =
      productKernel (fun slot => if slot ∈ coordinates then
        densityConjugate (operator slot) (reference slot).weight (functions slot) else functions slot) := by
  induction coordinates with
  | nil => simp only [inputIteration_nil, LinearMap.id_apply, List.not_mem_nil, if_false]
  | cons slot tail ih =>
    rw [List.nodup_cons] at hnodup
    rw [inputIteration_cons, ih hnodup.2, partialInputOperator_product]
    congr 1
    funext other
    by_cases heq : other = slot
    · subst other
      simp only [Function.update_self, if_neg hnodup.1, List.mem_cons_self, if_true]
    · simp only [Function.update_of_ne heq, List.mem_cons, heq, false_or]

/-- The product indicator family spans every finite joint table exactly. -/
theorem kernel_product_expansion (kernel : (Slot → Color) → ℝ) :
    kernel = ∑ point : Slot → Color, kernel point •
      productKernel (fun slot color => if color = point slot then 1 else 0) := by
  funext word
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, productKernel]
  have heq (point : Slot → Color) :
      (∏ slot : Slot, if word slot = point slot then (1 : ℝ) else 0) = if word = point then 1 else 0 := by
    by_cases hp : word = point
    · simp [hp]
    · have hd : ∃ slot, word slot ≠ point slot := by
        by_contra hn
        push_neg at hn
        exact hp (funext hn)
      obtain ⟨slot, hs⟩ := hd
      rw [if_neg hp]
      exact Finset.prod_eq_zero (Finset.mem_univ slot) (if_neg hs)
  simp only [heq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem densityConjugate_indicator (operator : Module.End ℝ (Color → ℝ)) (reference : Color → ℝ)
    (point output : Color) :
    densityConjugate operator reference (fun color => if color = point then 1 else 0) output =
      reference point * LinearMap.toMatrix' operator output point / reference output := by
  change operator (fun color => reference color * (if color = point then 1 else 0)) output / reference output = _
  rw [← LinearMap.toMatrix'_mulVec]
  simp only [Matrix.mulVec, dotProduct, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- The full coordinate operation is the actual tensor matrix contraction,
proved by an exact finite spanning expansion of an arbitrary joint kernel. -/
theorem inputIteration_matrix (coordinates : List Slot) (hnodup : coordinates.Nodup)
    (hcomplete : ∀ slot, slot ∈ coordinates)
    (operator : Slot → Module.End ℝ (Color → ℝ)) (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (output : Slot → Color) :
    inputIteration coordinates operator reference kernel output =
      ∑ point : Slot → Color, kernel point * ∏ slot,
        ((reference slot).weight (point slot) * LinearMap.toMatrix' (operator slot) (output slot) (point slot) /
          (reference slot).weight (output slot)) := by
  have hh := congrArg (fun table => inputIteration coordinates operator reference table output)
    (kernel_product_expansion kernel)
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro point _
  rw [inputIteration_product coordinates hnodup]
  simp only [if_pos (hcomplete _), productKernel, densityConjugate_indicator]

theorem weighted_inputIteration_matrix (coordinates : List Slot) (hnodup : coordinates.Nodup)
    (hcomplete : ∀ slot, slot ∈ coordinates)
    (operator : Slot → Module.End ℝ (Color → ℝ)) (reference : Slot → FiniteDist Color)
    (hpositive : ∀ slot color, (reference slot).weight color ≠ 0)
    (kernel : (Slot → Color) → ℝ) (output : Slot → Color) :
    (∏ slot, (reference slot).weight (output slot)) *
        inputIteration coordinates operator reference kernel output =
      ∑ point : Slot → Color,
        (kernel point * ∏ slot, (reference slot).weight (point slot)) *
          ∏ slot, LinearMap.toMatrix' (operator slot) (output slot) (point slot) := by
  rw [inputIteration_matrix coordinates hnodup hcomplete, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro point _
  have heq : (∏ slot, (reference slot).weight (output slot)) *
      (∏ slot, (reference slot).weight (point slot) * LinearMap.toMatrix' (operator slot) (output slot) (point slot) /
        (reference slot).weight (output slot)) =
      (∏ slot, (reference slot).weight (point slot)) *
        ∏ slot, LinearMap.toMatrix' (operator slot) (output slot) (point slot) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro slot _
    field_simp [hpositive slot (output slot)]
  calc
    _ = kernel point * ((∏ slot, (reference slot).weight (output slot)) *
      (∏ slot, (reference slot).weight (point slot) * LinearMap.toMatrix' (operator slot) (output slot) (point slot) /
        (reference slot).weight (output slot))) := by ring
    _ = _ := by rw [heq]; ring

end
end AFT.MixedKernel
