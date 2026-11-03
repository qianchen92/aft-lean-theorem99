import AFT.WholeBoundaryKernelPolynomial
import AFT.WholeBoundaryTable

/-! # The whole-table legal projection preserves the full role polynomial -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {Color Output : Type*} [Fintype Color]

/-- Zero body forms kill precisely every term that has a body input. -/
theorem inputKernelPolynomial_body_zero (primary : Color → Table Output)
    (seed : InputSeed Color) (hbody : seed.bodyOrder≠0) :
    inputKernelPolynomial primary 0 seed=0 := by
  unfold inputKernelPolynomial kernelPolynomial
  apply Finset.sum_eq_zero
  intro word _
  apply mul_eq_zero_of_right
  apply Finset.prod_eq_zero (Finset.mem_univ (Fin.natAdd seed.primaryOrder ⟨0,by omega⟩))
  simp only [Fin.addCases_right,Pi.zero_apply]

omit [Fintype Color] in
theorem controlProductForms_all_primary (primary body : Color → Table Output)
    (seeds : List (InputSeed Color)) (hbody : controlProductBodyOrder seeds=0) :
    controlProductForms primary body seeds=(fun _ => primary) := by
  induction seeds with
  | nil => funext slot; exact PEmpty.elim slot
  | cons seed rest ih =>
    have hs : seed.bodyOrder=0 ∧ controlProductBodyOrder rest=0 := by
      simpa only [controlProductBodyOrder,List.map_cons,List.sum_cons,Nat.add_eq_zero_iff] using hbody
    funext slot
    cases slot with
    | inr slot => exact congrFun (ih hs.2) slot
    | inl slot =>
      cases slot using Fin.addCases with
      | left slot => simp only [controlProductForms,Sum.elim_inl,Fin.addCases_left]
      | right slot => exact False.elim (by have := slot.isLt; omega)

theorem inputKernelPolynomial_primaryMonomialSeed (primary body : Color → Table Output)
    (powers : InputSeed Color →₀ ℕ) (hbody : controlProductBodyOrder (monomialOccurrences powers)=0) :
    inputKernelPolynomial primary body (primaryMonomialSeed powers)=
      inputKernelPolynomialHom primary body (MvPolynomial.monomial powers 1) := by
  rw [primaryMonomialSeed,inputKernelPolynomial_primaryFiniteSeed,
    inputKernelPolynomialHom_monomial,map_one,one_mul,mixedMonomialSeed,
    inputKernelPolynomial_mixedProductSeed,← controlProduct_kernelPolynomial,
    controlProductForms_all_primary primary body _ hbody]

theorem inputKernelPolynomialHom_body_zero (primary : Color → Table Output)
    (powers : InputSeed Color →₀ ℕ) (hbody : controlProductBodyOrder (monomialOccurrences powers)≠0) :
    inputKernelPolynomialHom primary 0 (MvPolynomial.monomial powers 1)=0 := by
  obtain ⟨seed,hs,hb⟩ := monomial_body_exists powers hbody
  simp only [inputKernelPolynomialHom,MvPolynomial.eval₂Hom_monomial,map_one,one_mul,Finsupp.prod]
  apply Finset.prod_eq_zero hs
  rw [inputKernelPolynomial_body_zero primary seed hb,zero_pow (Finsupp.mem_support_iff.mp hs)]

theorem inputKernelPolynomialHom_as_sum (primary body : Color → Table Output)
    (table : Table (InputSeed Color)) :
    inputKernelPolynomialHom primary body table=
      ∑ powers∈table.support,MvPolynomial.C (MvPolynomial.coeff powers table)*
        inputKernelPolynomialHom primary body (MvPolynomial.monomial powers 1) := by
  conv_lhs => rw [MvPolynomial.as_sum table]
  simp only [map_sum,inputKernelPolynomialHom_monomial,map_one,one_mul]

variable [DecidableEq Color]

theorem wholeBoundaryMonomial_inputHom (primary body : FiniteDist Color)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (interior : Finset Color)
    (primaryForm bodyForm : Color → Table Output) (powers : InputSeed Color →₀ ℕ) :
    inputKernelPolynomialHom primaryForm bodyForm
      (wholeBoundaryMonomial primary body operator interior powers)=
      inputKernelPolynomialHom primaryForm bodyForm (MvPolynomial.monomial powers 1)-
        inputKernelPolynomialHom (complementaryPrimaryForm primary operator interior primaryForm) 0
          (MvPolynomial.monomial powers 1) := by
  unfold wholeBoundaryMonomial
  split_ifs with hb
  · rw [inputKernelPolynomialHom_X,wholeBoundarySeed_inputKernelPolynomial _ _ _ _ _ _ _ rfl,
      inputKernelPolynomial_primaryMonomialSeed _ _ _ hb]
    congr 1
    rw [← inputKernelPolynomial_primaryMonomialSeed _ _ _ hb,
      inputKernelPolynomial_all_primary _ _ _ rfl,inputKernelPolynomial_all_primary _ _ _ rfl]
  · rw [inputKernelPolynomialHom_body_zero _ powers hb,sub_zero]

/-- The original whole J table equals the identity minus the complementary
primary transform on its body-free part. No canonicality premise is needed. -/
theorem wholeBoundaryTable_inputHom (primary body : FiniteDist Color)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (interior : Finset Color)
    (primaryForm bodyForm : Color → Table Output) (table : Table (InputSeed Color)) :
    inputKernelPolynomialHom primaryForm bodyForm (wholeBoundaryTable primary body operator interior table)=
      inputKernelPolynomialHom primaryForm bodyForm table-
        inputKernelPolynomialHom (complementaryPrimaryForm primary operator interior primaryForm) 0 table := by
  rw [wholeBoundaryTable]
  simp only [map_sum,map_mul]
  have hc (scalar : ℝ) : inputKernelPolynomialHom primaryForm bodyForm (MvPolynomial.C scalar)=
      MvPolynomial.C scalar := by simp [inputKernelPolynomialHom]
  simp only [hc,wholeBoundaryMonomial_inputHom,mul_sub]
  rw [Finset.sum_sub_distrib]
  rw [← inputKernelPolynomialHom_as_sum,← inputKernelPolynomialHom_as_sum]

/-- Whole J descends to equality of role polynomials, so executable tables
may be stored with independent finite coordinate numberings. -/
theorem wholeBoundaryTable_inputHom_congr (primary body : FiniteDist Color)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (interior : Finset Color)
    (first second : Table (InputSeed Color))
    (hequal : ∀ primaryForm bodyForm : Color → Table Output,
      inputKernelPolynomialHom primaryForm bodyForm first=inputKernelPolynomialHom primaryForm bodyForm second)
    (primaryForm bodyForm : Color → Table Output) :
    inputKernelPolynomialHom primaryForm bodyForm (wholeBoundaryTable primary body operator interior first)=
      inputKernelPolynomialHom primaryForm bodyForm (wholeBoundaryTable primary body operator interior second) := by
  rw [wholeBoundaryTable_inputHom,wholeBoundaryTable_inputHom,hequal,hequal]

end
end AFT.RepresentedPolynomial
