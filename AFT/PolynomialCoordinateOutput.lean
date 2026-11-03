import AFT.MixedMonomialSeed
import AFT.CoordinateSliceOutput

/-! # Exact coordinate operations with arbitrary polynomial remaining channels -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Other Color Output : Type*} [Fintype Slot] [Fintype Other]
  [DecidableEq Slot] [DecidableEq Other] [Fintype Color]

theorem jointChannelPolynomial_equiv (equiv : Slot ≃ Other)
    (reference : Slot → FiniteDist Color) (forms : Slot → Color → Table Output)
    (kernel : (Slot → Color) → ℝ) :
    jointChannelPolynomial (fun slot => reference (equiv.symm slot))
      (fun slot => forms (equiv.symm slot)) (fun word => kernel (word ∘ equiv)) =
      jointChannelPolynomial reference forms kernel := by
  have hh := (HistogramNormalization.renameWord (Color := Color) equiv).symm.sum_comp
    (fun word : Slot → Color => MvPolynomial.C (kernel word*∏ slot,(reference slot).weight (word slot))*
      ∏ slot,forms slot (word slot))
  apply Eq.trans ?_ hh
  unfold jointChannelPolynomial
  apply Finset.sum_congr (by ext word; simp)
  intro word _
  have hp := equiv.prod_comp (fun slot => (reference (equiv.symm slot)).weight (word slot))
  have hx := equiv.prod_comp (fun slot => forms (equiv.symm slot) (word slot))
  simp only [Equiv.symm_apply_apply] at hp hx
  simp only [HistogramNormalization.renameWord,Equiv.coe_fn_symm_mk,Function.comp_def,hp,hx]

theorem jointChannelPolynomial_sum (reference : Slot → FiniteDist Color) (other : Other → FiniteDist Color)
    (forms : Slot → Color → Table Output) (otherForms : Other → Color → Table Output)
    (kernel : (Slot ⊕ Other → Color) → ℝ) :
    jointChannelPolynomial (Sum.elim reference other) (Sum.elim forms otherForms) kernel =
      ∑ rest,MvPolynomial.C (∏ slot,(other slot).weight (rest slot))*
        jointChannelPolynomial reference forms (fun word => kernel (Sum.elim word rest))*
        ∏ slot,otherForms slot (rest slot) := by
  unfold jointChannelPolynomial
  have he := (Equiv.sumArrowEquivProdArrow Slot Other Color).symm.sum_comp
    (fun word : Slot ⊕ Other → Color =>
      MvPolynomial.C (kernel word*∏ slot,(Sum.elim reference other slot).weight (word slot))*
        ∏ slot,Sum.elim forms otherForms slot (word slot))
  have hs : (∑ word : Slot ⊕ Other → Color,
      MvPolynomial.C (kernel word*∏ slot,(Sum.elim reference other slot).weight (word slot))*
        ∏ slot,Sum.elim forms otherForms slot (word slot))=
      ∑ pair : (Slot → Color)×(Other → Color),MvPolynomial.C (kernel (Sum.elim pair.1 pair.2)*
        ∏ slot,(Sum.elim reference other slot).weight (Sum.elim pair.1 pair.2 slot))*
          ∏ slot,Sum.elim forms otherForms slot (Sum.elim pair.1 pair.2 slot) := he.symm
  rw [hs,Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro rest _
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro word _
  simp only [Fintype.prod_sum_type,Sum.elim_inl,Sum.elim_inr,map_mul]
  ring

/-- Polynomial factors at old coordinates are retained, so successive old
coordinates can be replaced without treating new outputs as new inputs. -/
theorem jointChannelPolynomial_new_inverse (reference : Slot → FiniteDist Color) (other : Other → FiniteDist Color)
    (otherForms : Other → Color → Table Color) (rho : ℝ) (hrho : rho ≠ 0)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ))
    (hp : ∀ slot color,(reference slot).weight color ≠ 0) (kernel : (Slot ⊕ Other → Color) → ℝ) :
    jointChannelPolynomial (Sum.elim reference other)
      (Sum.elim (fun _ => channelForm (fun input output => rho*LinearMap.toMatrix' operator.toLinearMap output input)) otherForms)
      (MixedKernel.coordinateInverseKernel ((MixedKernel.allCoordinates (Slot := Slot)).map Sum.inl)
        (Sum.elim reference other) rho operator kernel) =
      ∑ rest,MvPolynomial.C (∏ slot,(other slot).weight (rest slot))*
        (∑ word : Slot → Color,MvPolynomial.C (kernel (Sum.elim word rest)*∏ slot,(reference slot).weight (word slot))*
          ∏ slot,MvPolynomial.X (word slot)) * ∏ slot,otherForms slot (rest slot) := by
  rw [jointChannelPolynomial_sum]
  apply Finset.sum_congr rfl
  intro rest _
  rw [MixedKernel.coordinateInverseKernel_inl_slice]
  congr 2
  rw [← indexedOutput_joint,indexedOutput_coordinateInverse reference rho hrho operator hp]

end
end AFT.RepresentedPolynomial
