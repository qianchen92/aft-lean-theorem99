import AFT.PendingKernelSubstitution
import AFT.IndependentGlobalQuotient

/-! # Independent response is invariant under role-preserving input reindexing -/
namespace AFT.V7Calibration
open GaussianSource RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance independentRolePolynomialFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {Output : Type*}
variable (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)

theorem independentGlobalQuotient_role_equiv
    (primary body : Fin (Parameters.modulus n) → Table Output)
    {first second : InputSeed (Fin (Parameters.modulus n))} (equiv : SeedRoleEquiv first second) (depth : ℕ) :
    inputKernelPolynomialHom primary body (independentGlobalQuotient C n beta operator charts first depth)=
      inputKernelPolynomialHom primary body (independentGlobalQuotient C n beta operator charts second depth) := by
  simp only [independentGlobalQuotient,map_mul,map_pow,
    independentNumeratorTable_role_equiv C n beta operator charts primary body equiv,
    equiv.primaryOrder_eq,equiv.bodyOrder_eq]

theorem independentGlobalQuotient_sub_role_equiv
    (primary body : Fin (Parameters.modulus n) → Table Output)
    {first second : InputSeed (Fin (Parameters.modulus n))} (equiv : SeedRoleEquiv first second) (depth : ℕ) :
    inputKernelPolynomialHom primary body
        (independentGlobalQuotient C n beta operator charts first depth-MvPolynomial.X first)=
      inputKernelPolynomialHom primary body
        (independentGlobalQuotient C n beta operator charts second depth-MvPolynomial.X second) := by
  rw [map_sub,map_sub,independentGlobalQuotient_role_equiv C n beta operator charts primary body equiv,
    inputKernelPolynomialHom_X,inputKernelPolynomialHom_X,equiv.inputKernelPolynomial]

/-- A pending subset is transported by its actual full-coordinate forms.
This permits E to leave all newly produced coordinates unmarked. -/
theorem pendingNumeratorTable_forms_equiv
    (primary body : Fin (Parameters.modulus n) → Table Output)
    {first second : PendingInput (Fin (Parameters.modulus n))}
    (equiv : SeedRoleEquiv first.seed second.seed)
    (hforms : ∀ slot,pendingKernelForms primary body (independentInputForm C n beta operator charts primary) second
      (equiv.coordinates slot)=pendingKernelForms primary body (independentInputForm C n beta operator charts primary) first slot) :
    inputKernelPolynomialHom primary body (pendingNumeratorTable C n beta operator charts first)=
      inputKernelPolynomialHom primary body (pendingNumeratorTable C n beta operator charts second) := by
  rw [pendingNumeratorTable_kernelPolynomial,pendingNumeratorTable_kernelPolynomial]
  have he := kernelPolynomial_equiv equiv.coordinates
    (pendingKernelForms primary body (independentInputForm C n beta operator charts primary) first) first.seed.kernel
  have hk : (fun word => first.seed.kernel (word ∘ equiv.coordinates))=second.seed.kernel := funext equiv.kernel
  have hf : (fun slot => pendingKernelForms primary body (independentInputForm C n beta operator charts primary) first
      (equiv.coordinates.symm slot))=pendingKernelForms primary body (independentInputForm C n beta operator charts primary) second := by
    funext slot
    simpa using (hforms (equiv.coordinates.symm slot)).symm
  rw [hk,hf] at he
  exact he.symm

end
end AFT.V7Calibration
