import AFT.IndependentRolePolynomial
import AFT.KernelPolynomialMonomial
import AFT.IndependentUpperOperator

/-! # The full independent joint response acts by role-specific forms -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance independentActionFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {Color Output : Type*} [Fintype Color]

theorem inputKernelPolynomial_mul_forms (primary body : Color → Table Output)
    (primaryFactor bodyFactor : Table Output) (seed : InputSeed Color) :
    inputKernelPolynomial (fun color => primary color*primaryFactor) (fun color => body color*bodyFactor) seed=
      inputKernelPolynomial primary body seed*primaryFactor^seed.primaryOrder*bodyFactor^seed.bodyOrder := by
  simp only [inputKernelPolynomial,kernelPolynomial,Fin.prod_univ_add,Fin.addCases_left,Fin.addCases_right,
    Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro word _
  ring

@[simp] theorem inputKernelPolynomialHom_C (primary body : Color → Table Output) (scalar : ℝ) :
    inputKernelPolynomialHom primary body (MvPolynomial.C scalar)=MvPolynomial.C scalar := by
  simp [inputKernelPolynomialHom]

theorem inputKernelPolynomialHom_smul (primary body : Color → Table Output) (scalar : ℝ)
    (table : Table (InputSeed Color)) :
    inputKernelPolynomialHom primary body (scalar • table)=scalar • inputKernelPolynomialHom primary body table := by
  simp only [MvPolynomial.smul_eq_C_mul,map_mul,inputKernelPolynomialHom_C]

end
end AFT.RepresentedPolynomial
namespace AFT.V7Calibration
open GaussianSource RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance independentActionV7FinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {Output : Type*}
variable (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)

def independentNormalizedPrimaryForm (primary body : Fin (Parameters.modulus n) → Table Output) (depth : ℕ)
    (color : Fin (Parameters.modulus n)) : Table Output :=
  independentInputForm C n beta operator charts primary color*
    inputKernelPolynomialHom primary body (independentPositiveReciprocal C n beta operator charts depth)

def independentNormalizedBodyForm (primary body : Fin (Parameters.modulus n) → Table Output) (depth : ℕ)
    (color : Fin (Parameters.modulus n)) : Table Output :=
  body color*inputKernelPolynomialHom primary body (independentBodyReciprocal C n beta operator depth)

/-- Both actual denominator reciprocals are absorbed once per old role.
The whole original joint kernel remains inside a single contraction. -/
theorem independentGlobalQuotient_polynomial (primary body : Fin (Parameters.modulus n) → Table Output)
    (depth : ℕ) (seed : InputSeed (Fin (Parameters.modulus n))) :
    inputKernelPolynomialHom primary body (independentGlobalQuotient C n beta operator charts seed depth)=
      inputKernelPolynomial
        (independentNormalizedPrimaryForm C n beta operator charts primary body depth)
        (independentNormalizedBodyForm C n beta operator primary body depth) seed := by
  change _ = inputKernelPolynomial
    (fun color => independentInputForm C n beta operator charts primary color*
      inputKernelPolynomialHom primary body (independentPositiveReciprocal C n beta operator charts depth))
    (fun color => body color*inputKernelPolynomialHom primary body (independentBodyReciprocal C n beta operator depth)) seed
  rw [inputKernelPolynomial_mul_forms]
  simp only [independentGlobalQuotient,map_mul,map_pow,independentNumeratorTable_kernelPolynomial]

/-- This column map is unrestricted; the original operator restricts it to
its proved canonical cutoff domain and then truncates its output. -/
def independentRawColumnLinear (depth : ℕ) : Module.End ℝ (Table (InputSeed (Fin (Parameters.modulus n)))) :=
  Finsupp.linearCombination ℝ (fun powers =>
    independentGlobalQuotient C n beta operator charts (mixedMonomialSeed powers) depth-
      MvPolynomial.X (mixedMonomialSeed powers))

theorem independentRawColumnLinear_polynomial (primary body : Fin (Parameters.modulus n) → Table Output)
    (depth : ℕ) (table : Table (InputSeed (Fin (Parameters.modulus n)))) :
    inputKernelPolynomialHom primary body (independentRawColumnLinear C n beta operator charts depth table)=
      inputKernelPolynomialHom
        (independentNormalizedPrimaryForm C n beta operator charts primary body depth)
        (independentNormalizedBodyForm C n beta operator primary body depth) table-
          inputKernelPolynomialHom primary body table := by
  induction table using MvPolynomial.induction_on' with
  | monomial powers scalar =>
    change inputKernelPolynomialHom primary body
      (Finsupp.linearCombination ℝ _ (Finsupp.single powers scalar))=_
    rw [Finsupp.linearCombination_single,inputKernelPolynomialHom_smul,map_sub,
      independentGlobalQuotient_polynomial,inputKernelPolynomialHom_X,
      inputKernelPolynomialHom_monomial,inputKernelPolynomialHom_monomial]
    simp only [MvPolynomial.smul_eq_C_mul,mul_sub]
  | add first second hfirst hsecond =>
    simp only [map_add,hfirst,hsecond]
    ring

/-- The complete U action preserves all role-polynomial identities, rather
than merely preserving a scalar physical PGF. -/
theorem independentRawColumnLinear_polynomial_congr
    (first second : Table (InputSeed (Fin (Parameters.modulus n))))
    (heq : ∀ primary body : Fin (Parameters.modulus n) → Table Output,
      inputKernelPolynomialHom primary body first=inputKernelPolynomialHom primary body second)
    (primary body : Fin (Parameters.modulus n) → Table Output) (depth : ℕ) :
    inputKernelPolynomialHom primary body (independentRawColumnLinear C n beta operator charts depth first)=
      inputKernelPolynomialHom primary body (independentRawColumnLinear C n beta operator charts depth second) := by
  rw [independentRawColumnLinear_polynomial,independentRawColumnLinear_polynomial,heq,heq]

end
end AFT.V7Calibration
