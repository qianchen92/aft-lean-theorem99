import AFT.PolynomialCoordinateOutput
import AFT.SeedRoleEquivalence

/-! # Unweighted joint-kernel forms retaining the primary/body roles -/
namespace AFT.RepresentedPolynomial
open V7Calibration
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance kernelPolynomialUnitDecEq : DecidableEq Unit := Classical.decEq _
local instance kernelPolynomialFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {Slot Other Color Output : Type*} [Fintype Slot] [Fintype Other]
  [DecidableEq Slot] [DecidableEq Other] [Fintype Color]

def kernelPolynomial (forms : Slot → Color → Table Output) (kernel : (Slot → Color) → ℝ) : Table Output :=
  ∑ word,MvPolynomial.C (kernel word)*∏ slot,forms slot (word slot)

theorem kernelPolynomial_equiv (equiv : Slot ≃ Other)
    (forms : Slot → Color → Table Output) (kernel : (Slot → Color) → ℝ) :
    kernelPolynomial (fun slot => forms (equiv.symm slot)) (fun word => kernel (word ∘ equiv))=
      kernelPolynomial forms kernel := by
  have hh := (HistogramNormalization.renameWord (Color := Color) equiv).symm.sum_comp
    (fun word : Slot → Color => MvPolynomial.C (kernel word)*∏ slot,forms slot (word slot))
  apply Eq.trans ?_ hh
  unfold kernelPolynomial
  apply Finset.sum_congr (by ext word; simp)
  intro word _
  have hx := equiv.prod_comp (fun slot => forms (equiv.symm slot) (word slot))
  simp only [Equiv.symm_apply_apply] at hx
  simp only [HistogramNormalization.renameWord,Equiv.coe_fn_symm_mk,Function.comp_def,hx]

theorem kernelPolynomial_sum (forms : Slot → Color → Table Output)
    (otherForms : Other → Color → Table Output) (kernel : (Slot ⊕ Other → Color) → ℝ) :
    kernelPolynomial (Sum.elim forms otherForms) kernel=
      ∑ rest,kernelPolynomial forms (fun word => kernel (Sum.elim word rest))*
        ∏ slot,otherForms slot (rest slot) := by
  unfold kernelPolynomial
  rw [← (Equiv.sumArrowEquivProdArrow Slot Other Color).symm.sum_comp,
    Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro rest _
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro word _
  simp only [Equiv.sumArrowEquivProdArrow,Fintype.prod_sum_type,Sum.elim_inl,Sum.elim_inr]
  change MvPolynomial.C (kernel (Sum.elim word rest))*((∏ slot,forms slot (word slot))*
    ∏ slot,otherForms slot (rest slot))=_
  ring

theorem kernelPolynomial_singleton (form : Color → Table Output) (kernel : Color → ℝ) :
    kernelPolynomial (fun _ : Unit => form) (fun word => kernel (word ()))=
      ∑ color,MvPolynomial.C (kernel color)*form color := by
  unfold kernelPolynomial
  rw [← (Equiv.funUnique Unit Color).symm.sum_comp]
  simp only [Fintype.prod_unique,Equiv.funUnique_symm_apply,uniqueElim_const]

theorem kernelPolynomial_unit (form : Color → Table Output) (kernel : (Unit → Color) → ℝ) :
    kernelPolynomial (fun _ : Unit => form) kernel=
      ∑ color,MvPolynomial.C (kernel (fun _ => color))*form color := by
  unfold kernelPolynomial
  rw [← (Equiv.funUnique Unit Color).symm.sum_comp]
  simp only [Fintype.prod_unique,Equiv.funUnique_symm_apply,uniqueElim_const]
  apply Finset.sum_congr rfl
  intro color _
  congr 2

/-- The forms may keep the roles as separate indeterminates. No physical
channel identification or invertibility premise is used. -/
def inputKernelPolynomial (primary body : Color → Table Output) (seed : InputSeed Color) : Table Output :=
  kernelPolynomial (Fin.addCases (fun _ => primary) (fun _ => body)) seed.kernel

def inputKernelPolynomialHom (primary body : Color → Table Output) :
    Table (InputSeed Color) →+* Table Output :=
  MvPolynomial.eval₂Hom MvPolynomial.C (inputKernelPolynomial primary body)

@[simp] theorem inputKernelPolynomialHom_X (primary body : Color → Table Output) (seed : InputSeed Color) :
    inputKernelPolynomialHom primary body (MvPolynomial.X seed)=inputKernelPolynomial primary body seed := by
  simp [inputKernelPolynomialHom]

theorem SeedRoleEquiv.inputKernelPolynomial {first second : InputSeed Color}
    (equiv : SeedRoleEquiv first second) (primary body : Color → Table Output) :
    inputKernelPolynomial primary body first=inputKernelPolynomial primary body second := by
  have hf (seed : InputSeed Color) :
      (Fin.addCases (fun _ : Fin seed.primaryOrder => primary) (fun _ : Fin seed.bodyOrder => body))=
        fun slot => if inputSeedRole seed slot then primary else body := by
    funext slot
    cases slot using Fin.addCases <;> simp [inputSeedRole]
  have he := kernelPolynomial_equiv equiv.coordinates
    (Fin.addCases (fun _ : Fin first.primaryOrder => primary) (fun _ : Fin first.bodyOrder => body)) first.kernel
  have hk : (fun word => first.kernel (word ∘ equiv.coordinates))=second.kernel := funext equiv.kernel
  have hr (slot) : inputSeedRole first (equiv.coordinates.symm slot)=inputSeedRole second slot := by
    simpa using (equiv.role (equiv.coordinates.symm slot)).symm
  simp only [hf,hk,hr] at he
  simpa only [RepresentedPolynomial.inputKernelPolynomial,hf] using he.symm

end
end AFT.RepresentedPolynomial
