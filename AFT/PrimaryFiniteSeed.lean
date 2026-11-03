import AFT.MixedReindex
import AFT.CovarianceOutput
import AFT.PrimarySeedCanonical

/-! # Literal primary input seeds indexed by an arbitrary finite set -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

def primaryFiniteSeed (kernel : (Slot → Color) → ℝ) : InputSeed Color where
  primaryOrder := Fintype.card Slot
  bodyOrder := 0
  kernel := fun word => kernel (word ∘ Fintype.equivFin Slot)

omit [DecidableEq Slot] in
theorem primaryFiniteSeed_reference (primary body : FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (slot : Fin (Fintype.card Slot)) :
    inputReference primary body (primaryFiniteSeed kernel) slot = primary :=
  all_primary_reference primary body (primaryFiniteSeed kernel) rfl slot

omit [Fintype Color] [DecidableEq Slot] in
theorem primaryFiniteSeed_rate (primaryPool bodyPool : ℝ)
    (kernel : (Slot → Color) → ℝ) (slot : Fin (Fintype.card Slot)) :
    inputRate primaryPool bodyPool (primaryFiniteSeed kernel) slot = (Real.sqrt primaryPool)⁻¹ :=
  primaryCoordinates_rate primaryPool bodyPool (primaryFiniteSeed kernel) slot
    (primaryCoordinates_complete (primaryFiniteSeed kernel) rfl slot)

/-- The seed is a renaming of the entire joint kernel, with every mixed
fiber preserved exactly. -/
theorem primaryFiniteSeed_weight (primary body : FiniteDist Color)
    (primaryPool bodyPool radius : ℝ) (kernel : (Slot → Color) → ℝ) :
    inputWeight primary body primaryPool bodyPool radius (primaryFiniteSeed kernel) =
      MixedKernel.activity (fun _ : Slot => (Real.sqrt primaryPool)⁻¹) (fun _ : Slot => primary) kernel := by
  change radius^0 * MixedKernel.activity
    (inputRate primaryPool bodyPool (primaryFiniteSeed kernel))
    (inputReference primary body (primaryFiniteSeed kernel)) (primaryFiniteSeed kernel).kernel = _
  rw [pow_zero,one_mul,funext (primaryFiniteSeed_rate primaryPool bodyPool kernel),
    funext (primaryFiniteSeed_reference primary body kernel)]
  exact MixedKernel.CoordinateTransport.activity_equiv (Fintype.equivFin Slot)
    (fun _ : Slot => (Real.sqrt primaryPool)⁻¹) (fun _ : Slot => primary) kernel

omit [DecidableEq Slot] in
theorem primaryFiniteSeed_canonical (primary body : FiniteDist Color)
    (kernel : (Slot → Color) → ℝ)
    (hc : Hoeffding.Canonical (fun _ : Slot => primary) Finset.univ kernel) :
    Hoeffding.Canonical (inputReference primary body (primaryFiniteSeed kernel)) Finset.univ
      (primaryFiniteSeed kernel).kernel := by
  have hh := MixedKernel.CoordinateTransport.canonical_equiv (Fintype.equivFin Slot)
    (fun _ : Slot => primary) kernel hc
  convert hh using 1
  exact funext (primaryFiniteSeed_reference primary body kernel)


/-- Evaluation keeps the complete joint coefficient, after merely renaming
its finite selected coordinate set. -/
theorem primaryFiniteSeed_form (primary : FiniteDist Color) (kernel : (Slot → Color) → ℝ) :
    jointPrimaryForm primary (primaryFiniteSeed kernel) =
      ∑ word : Slot → Color,MvPolynomial.C (kernel word*∏ slot,primary.weight (word slot))*
        ∏ slot,MvPolynomial.X (word slot) := by
  let equiv := Fintype.equivFin Slot
  have hh := (HistogramNormalization.renameWord (Color := Color) equiv).symm.sum_comp
    (fun word : Slot → Color => MvPolynomial.C (kernel word*∏ slot,primary.weight (word slot))*
      ∏ slot,MvPolynomial.X (word slot))
  change (∑ word : Fin (Fintype.card Slot) → Color,
    MvPolynomial.C (kernel (word ∘ equiv)*∏ slot,primary.weight (word slot))*∏ slot,MvPolynomial.X (word slot)) = _
  apply Eq.trans ?_ hh
  apply Finset.sum_congr rfl
  intro word _
  have hp := equiv.prod_comp (fun slot => primary.weight (word slot))
  have hx := equiv.prod_comp (fun slot => MvPolynomial.X (R := ℝ) (word slot))
  simp only [HistogramNormalization.renameWord,Equiv.coe_fn_symm_mk,Function.comp_def,hp,hx]

end
end AFT.RepresentedPolynomial
