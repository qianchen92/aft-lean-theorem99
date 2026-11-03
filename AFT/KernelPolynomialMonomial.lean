import AFT.KernelPolynomial
import AFT.IndependentProductPolynomial

/-! # The literal input homomorphism retains every joint monomial exactly -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 450000
variable {Color Output Primary Body : Type*} [Fintype Color] [Fintype Primary] [Fintype Body]
  [DecidableEq Primary] [DecidableEq Body]

theorem kernelPolynomial_tensor (forms : Primary → Color → Table Output)
    (otherForms : Body → Color → Table Output)
    (kernel : (Primary → Color) → ℝ) (other : (Body → Color) → ℝ) :
    kernelPolynomial (Sum.elim forms otherForms) (MixedKernel.tensor kernel other)=
      kernelPolynomial forms kernel*kernelPolynomial otherForms other := by
  rw [kernelPolynomial_sum]
  unfold kernelPolynomial
  simp only [MixedKernel.tensor,Function.comp_def,Sum.elim_inl,Sum.elim_inr,map_mul,
    Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro word _
  apply Finset.sum_congr rfl
  intro rest _
  ring

theorem inputKernelPolynomial_mixedFiniteSeed (primary body : Color → Table Output)
    (kernel : (Primary ⊕ Body → Color) → ℝ) :
    inputKernelPolynomial primary body (mixedFiniteSeed kernel)=
      kernelPolynomial (Sum.elim (fun _ : Primary => primary) (fun _ : Body => body)) kernel := by
  have he := kernelPolynomial_equiv (mixedFiniteEquiv (Primary := Primary) (Body := Body))
    (Sum.elim (fun _ : Primary => primary) (fun _ : Body => body)) kernel
  have hf : (fun slot => Sum.elim (fun _ : Primary => primary) (fun _ : Body => body)
      (mixedFiniteEquiv.symm slot))=
      Fin.addCases (fun _ : Fin (Fintype.card Primary) => primary) (fun _ : Fin (Fintype.card Body) => body) := by
    funext slot
    cases slot using Fin.addCases <;> simp [mixedFiniteEquiv]
  rw [hf] at he
  apply Eq.trans ?_ he
  unfold inputKernelPolynomial mixedFiniteSeed kernelPolynomial
  apply Finset.sum_congr (by ext word;simp)
  intro word _
  rfl

omit [Fintype Primary] [Fintype Body] [DecidableEq Primary] [DecidableEq Body] in
theorem controlProduct_kernelPolynomial (primary body : Color → Table Output) (seeds : List (InputSeed Color)) :
    kernelPolynomial (controlProductForms primary body seeds) (controlProductKernel seeds)=
      (seeds.map (inputKernelPolynomial primary body)).prod := by
  induction seeds with
  | nil => simp [kernelPolynomial,ControlProductSlot,controlProductKernel]
  | cons seed rest ih =>
    have he := kernelPolynomial_tensor
      (Fin.addCases (fun _ : Fin seed.primaryOrder => primary) (fun _ : Fin seed.bodyOrder => body))
      (controlProductForms primary body rest) seed.kernel (controlProductKernel rest)
    change kernelPolynomial _ (MixedKernel.tensor seed.kernel (controlProductKernel rest))=_
    have ht : kernelPolynomial (controlProductForms primary body (seed::rest))
        (MixedKernel.tensor seed.kernel (controlProductKernel rest))=
      kernelPolynomial
        (Sum.elim (Fin.addCases (fun _ : Fin seed.primaryOrder => primary) (fun _ : Fin seed.bodyOrder => body))
          (controlProductForms primary body rest)) (MixedKernel.tensor seed.kernel (controlProductKernel rest)) := by
      unfold kernelPolynomial
      apply Finset.sum_congr (by ext word;simp)
      intro word _
      rfl
    rw [ht,he,ih]
    simp only [List.map_cons,List.prod_cons]
    congr 1
    unfold inputKernelPolynomial kernelPolynomial
    apply Finset.sum_congr (by ext word;simp)
    intro word _
    rfl

omit [Fintype Primary] [Fintype Body] [DecidableEq Primary] [DecidableEq Body] in
theorem inputKernelPolynomial_mixedProductSeed (primary body : Color → Table Output)
    (seeds : List (InputSeed Color)) :
    inputKernelPolynomial primary body (mixedProductSeed seeds)=
      (seeds.map (inputKernelPolynomial primary body)).prod := by
  rw [mixedProductSeed,inputKernelPolynomial_mixedFiniteSeed]
  have he := kernelPolynomial_equiv (controlPoolEquiv seeds).symm
    (controlProductForms primary body seeds) (controlProductKernel seeds)
  have hf : (fun slot => controlProductForms primary body seeds (controlPoolEquiv seeds slot))=
      Sum.elim (fun _ : ControlPrimarySlot seeds => primary) (fun _ : ControlBodySlot seeds => body) := by
    funext slot
    cases slot with
    | inl slot => simp [controlPoolEquiv,controlProductForms_role,slot.property]
    | inr slot => simp [controlPoolEquiv,controlProductForms_role,slot.property]
  simp only [Equiv.symm_symm,hf] at he
  exact he.trans (controlProduct_kernelPolynomial primary body seeds)

omit [Fintype Primary] [Fintype Body] [DecidableEq Primary] [DecidableEq Body] in
theorem inputKernelPolynomialHom_monomial (primary body : Color → Table Output)
    (powers : InputSeed Color →₀ ℕ) (scalar : ℝ) :
    inputKernelPolynomialHom primary body (MvPolynomial.monomial powers scalar)=
      MvPolynomial.C scalar*inputKernelPolynomial primary body (mixedMonomialSeed powers) := by
  rw [mixedMonomialSeed,inputKernelPolynomial_mixedProductSeed,monomialOccurrences_product]
  simp only [inputKernelPolynomialHom,MvPolynomial.eval₂Hom_monomial]

end
end AFT.RepresentedPolynomial
