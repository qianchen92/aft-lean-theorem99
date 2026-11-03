import AFT.FiniteSeedOutput
import AFT.CoordinateInverseKernel

/-! # Exact new-coordinate inversion inside arbitrary joint leading outputs -/
namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Rest Color : Type*} [Fintype Slot] [DecidableEq Slot]
  [Fintype Rest] [DecidableEq Rest] [Fintype Color]

omit [Fintype Slot] [Fintype Rest] in
theorem inputIteration_inl_slice (coordinates : List Slot)
    (operator : Slot → Module.End ℝ (Color → ℝ))
    (reference : Slot → FiniteDist Color) (other : Rest → FiniteDist Color)
    (kernel : (Slot ⊕ Rest → Color) → ℝ) (rest : Rest → Color) :
    (fun word => inputIteration (coordinates.map Sum.inl)
      (Sum.elim operator (fun _ : Rest => LinearMap.id)) (Sum.elim reference other) kernel (Sum.elim word rest)) =
      inputIteration coordinates operator reference (fun word => kernel (Sum.elim word rest)) := by
  induction coordinates with
  | nil => rfl
  | cons slot coordinates ih =>
    funext word
    simp only [List.map_cons,inputIteration_cons,partialInputOperator,Sum.elim_inl]
    have he (color : Color) : Function.update (Sum.elim word rest) (Sum.inl slot) color =
        Sum.elim (Function.update word slot color) rest := by
      funext index
      cases index with
      | inl index =>
        by_cases h : index=slot
        · subst index; simp
        · simp [h]
      | inr index => simp
    simp_rw [he]
    have hi (point : Slot → Color) := congrFun ih point
    simp_rw [hi]

omit [Fintype Slot] [Fintype Rest] in
theorem coordinateInverseKernel_inl_slice (coordinates : List Slot)
    (reference : Slot → FiniteDist Color) (other : Rest → FiniteDist Color)
    (rho : ℝ) (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ))
    (kernel : (Slot ⊕ Rest → Color) → ℝ) (rest : Rest → Color) :
    (fun word => coordinateInverseKernel (coordinates.map Sum.inl) (Sum.elim reference other)
      rho operator kernel (Sum.elim word rest)) =
      coordinateInverseKernel coordinates reference rho operator (fun word => kernel (Sum.elim word rest)) := by
  have hg : inputIteration (coordinates.map Sum.inl) (fun _ : Slot ⊕ Rest => operator.symm.toLinearMap)
      (Sum.elim reference other) =
      inputIteration (coordinates.map Sum.inl)
        (Sum.elim (fun _ : Slot => operator.symm.toLinearMap) (fun _ : Rest => LinearMap.id))
        (Sum.elim reference other) := by
    induction coordinates with
    | nil => rfl
    | cons slot coordinates ih =>
      apply LinearMap.ext
      intro kernel
      funext word
      simp only [List.map_cons,inputIteration_cons,Sum.elim_inl]
      rw [ih]
  funext word
  simp only [coordinateInverseKernel,LinearMap.smul_apply,Pi.smul_apply,smul_eq_mul,List.length_map,hg]
  exact congrArg (fun value : (Slot → Color) → ℝ => (rho⁻¹)^coordinates.length*value word)
    (inputIteration_inl_slice coordinates (fun _ => operator.symm.toLinearMap) reference other kernel rest)

end
end AFT.MixedKernel

namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
open MixedKernel
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

theorem indexedOutput_eq_mass (reference : Slot → FiniteDist Color)
    (channel : Slot → Color → Color → ℝ) (kernel : (Slot → Color) → ℝ) :
    indexedOutput reference channel kernel =
      ∑ output : Slot → Color,MvPolynomial.C (∑ point : Slot → Color,(kernel point*∏ slot,(reference slot).weight (point slot))*
        ∏ slot,channel slot (point slot) (output slot))*∏ slot,MvPolynomial.X (output slot) := by
  cases Subsingleton.elim (inferInstance : DecidableEq Slot) (Classical.decEq Slot)
  simp only [indexedOutput,channelForm,Fintype.prod_sum,Finset.prod_mul_distrib,← map_prod]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro output _
  simp only [map_sum,Finset.sum_mul,← mul_assoc,← map_mul]

/-- Exact cancellation is performed on the true matrix contraction; the
kernel may be an arbitrary fixed slice of all remaining input coordinates. -/
theorem indexedOutput_coordinateInverse (reference : Slot → FiniteDist Color)
    (rho : ℝ) (hrho : rho ≠ 0) (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ))
    (hp : ∀ slot color,(reference slot).weight color ≠ 0) (kernel : (Slot → Color) → ℝ) :
    indexedOutput reference (fun _ input output => rho*LinearMap.toMatrix' operator.toLinearMap output input)
      (coordinateInverseKernel allCoordinates reference rho operator kernel) =
      ∑ output : Slot → Color,MvPolynomial.C (kernel output*∏ slot,(reference slot).weight (output slot))*
        ∏ slot,MvPolynomial.X (output slot) := by
  rw [indexedOutput_eq_mass]
  apply Finset.sum_congr rfl
  intro output _
  congr 2
  have hm := weighted_inputIteration_matrix (allCoordinates (Slot := Slot)).reverse
    (List.nodup_reverse.mpr (Finset.nodup_toList _)) (fun slot => by simp [allCoordinates]) (fun _ => operator.toLinearMap)
    reference hp (coordinateInverseKernel allCoordinates reference rho operator kernel) output
  have he := congrFun (coordinateInverseKernel_exact (allCoordinates (Slot := Slot)) reference rho hrho
    operator (fun slot _ => hp slot) kernel) output
  simp only [Pi.smul_apply,smul_eq_mul,allCoordinates_length] at he
  simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
  calc
    _ = rho^Fintype.card Slot *
        ∑ point,(coordinateInverseKernel allCoordinates reference rho operator kernel point*
          ∏ slot,(reference slot).weight (point slot))*
            ∏ slot,LinearMap.toMatrix' operator.toLinearMap (output slot) (point slot) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro point _
      ring
    _ = rho^Fintype.card Slot*((∏ slot,(reference slot).weight (output slot))*
      inputIteration (allCoordinates (Slot := Slot)).reverse (fun _ => operator.toLinearMap) reference
        (coordinateInverseKernel allCoordinates reference rho operator kernel) output) := by rw [hm]
    _ = _ := by rw [mul_left_comm,he]; ring

variable {Rest : Type*} [Fintype Rest] [DecidableEq Rest]

/-- Only the new block is inverted. Every old coordinate retains its
reference law and its original physical output channel. -/
theorem indexedOutput_new_inverse (reference : Slot → FiniteDist Color)
    (other : Rest → FiniteDist Color) (otherChannel : Rest → Color → Color → ℝ)
    (rho : ℝ) (hrho : rho ≠ 0) (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ))
    (hp : ∀ slot color,(reference slot).weight color ≠ 0)
    (kernel : (Slot ⊕ Rest → Color) → ℝ) :
    indexedOutput (Sum.elim reference other)
      (Sum.elim (fun _ input output => rho*LinearMap.toMatrix' operator.toLinearMap output input) otherChannel)
      (coordinateInverseKernel ((allCoordinates (Slot := Slot)).map Sum.inl)
        (Sum.elim reference other) rho operator kernel) =
      ∑ rest : Rest → Color,MvPolynomial.C (∏ slot,(other slot).weight (rest slot))*
        (∑ word : Slot → Color,MvPolynomial.C (kernel (Sum.elim word rest)*∏ slot,(reference slot).weight (word slot))*
          ∏ slot,MvPolynomial.X (word slot))*∏ slot,channelForm (otherChannel slot) (rest slot) := by
  cases Subsingleton.elim (inferInstance : DecidableEq Slot) (Classical.decEq Slot)
  cases Subsingleton.elim (inferInstance : DecidableEq Rest) (Classical.decEq Rest)
  rw [indexedOutput_sum]
  apply Finset.sum_congr rfl
  intro rest _
  rw [coordinateInverseKernel_inl_slice,indexedOutput_coordinateInverse reference rho hrho operator hp]

end
end AFT.RepresentedPolynomial
