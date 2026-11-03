import AFT.ReferenceCoefficientTable
import AFT.PrimaryInverseMatrix

/-! # Scalar formulas for the literal singleton reference coefficient -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
variable {Color : Type*} [Fintype Color]
section SingletonIndex
variable [DecidableEq (Fin 1)]

/-- The unique nonempty selected set contributes exactly one actual seed. -/
theorem referenceCoefficientTable_fin_one (primary reference : FiniteDist Color)
    (mass : (Fin 1 → Color) → ℝ) :
    referenceCoefficientTable primary reference mass=
      MvPolynomial.X (referenceCoefficientSeed primary reference mass Finset.univ) := by
  unfold referenceCoefficientTable
  apply Finset.sum_eq_single
  · intro selected hs hne
    have hnonempty : selected.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hs).1
    obtain ⟨slot,hslot⟩ := hnonempty
    have heq : selected=Finset.univ := by
      ext other
      constructor
      · intro _;exact Finset.mem_univ _
      · intro _
        simpa only [Subsingleton.elim other slot] using hslot
    exact (hne heq).elim
  · intro hn
    exact (hn (Finset.mem_erase.mpr ⟨by simp,Finset.mem_univ _⟩)).elim

/-- Evaluating at a constant word removes all arbitrary finite numberings
from the singleton label; no choice of `equivFin` is computed. -/
theorem referenceCoefficientSeed_fin_one_constant (primary reference : FiniteDist Color)
    (profile : Color → ℝ) (color : Color) :
    (referenceCoefficientSeed primary reference (fun word : Fin 1 → Color => profile (word 0)) Finset.univ).kernel
      (fun _ => color)=(profile color-reference.weight color*(∑ input,profile input))/primary.weight color := by
  change (∑ input : Fin 1 → Color,profile (input 0)*
    ∏ slot : (Finset.univ : Finset (Fin 1)),MixedKernel.referenceAtom primary reference (input slot.val) color)=_
  have hprod (input : Fin 1 → Color) :
      (∏ slot : (Finset.univ : Finset (Fin 1)),MixedKernel.referenceAtom primary reference (input slot.val) color)=
        MixedKernel.referenceAtom primary reference (input 0) color := by
    have he (slot : (Finset.univ : Finset (Fin 1))) : input slot.val=input 0 := congrArg input (Subsingleton.elim _ _)
    simp only [he,Finset.prod_const,Finset.card_univ,Fintype.card_coe,Finset.card_univ,Fintype.card_fin,pow_one]
  simp_rw [hprod]
  rw [←(Equiv.funUnique (Fin 1) Color).symm.sum_comp]
  simp only [Equiv.funUnique_symm_apply,uniqueElim_const,MixedKernel.referenceAtom_eq]
  simp_rw [←mul_div_assoc,mul_sub]
  rw [←Finset.sum_div,Finset.sum_sub_distrib]
  have hd : (∑ input,profile input*(if input=color then 1 else 0))=profile color := by simp
  rw [hd,←Finset.sum_mul,mul_comm (∑ input,profile input)]

end SingletonIndex

/-- The complete primary inverse of a singleton, in its original label. -/
theorem inversePrimarySeed_singleton_constant (primary body : FiniteDist Color) (rho : ℝ)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (seed : InputSeed Color)
    (hp : seed.primaryOrder=1) (hb : seed.bodyOrder=0) (output : Color) :
    (inversePrimarySeed primary body rho operator seed).kernel (fun _ => output)=
      ∑ input,seed.kernel (fun _ => input)*
        (rho⁻¹*primary.weight input*operator.symm (Pi.single input 1) output/primary.weight output) := by
  cases seed with
  | mk p b kernel =>
    dsimp only at hp hb
    subst p
    subst b
    rw [inversePrimarySeed_matrix]
    unfold MixedKernel.matrixApply
    letI : Unique (Fin (1+0)) := inferInstanceAs (Unique (Fin 1))
    rw [←(Equiv.funUnique (Fin (1+0)) Color).symm.sum_comp]
    simp only [Equiv.funUnique_symm_apply,uniqueElim_const]
    apply Finset.sum_congr rfl
    intro input _
    rw [Fin.prod_univ_add]
    simp only [primaryInverseMatrix,Fin.addCases_left,Fin.addCases_right,Fin.prod_univ_one,
      Fin.prod_univ_zero,mul_one]
    congr 1

end
end AFT.RepresentedPolynomial
