import AFT.SquarefreePoolExtraction
import AFT.KernelPolynomialMonomial

/-! # The full paired score factors through the role-preserving polynomial

This identity permits executable syntax to keep its stored factor order.
It retains all coefficients, cancellations, paired observations and distinct
public-placement normalizers of the original represented table.
-/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
local instance pairedExtractionSumDecEq {First Second : Type*} : DecidableEq (First⊕Second) := Classical.decEq _
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
variable {Color : Type*} [Fintype Color]

/-- Coefficient extraction recovers the literal complete paired public score,
including arbitrary joint monomial kernels. -/
theorem poolCoefficientExtraction_inputHom (primary body : FiniteDist Color)
    (anchor : Color → Color → ℝ) (activation : ℝ) (primaryPool bodyPool : ℕ)
    (table : Table (InputSeed Color)) (word : (Fin primaryPool⊕Fin bodyPool) → Color×Color) :
    poolCoefficientExtraction (inputKernelPolynomialHom
      (pairedPrimaryForm primary body anchor activation word) (pairedBodyForm word) table)=
      tablePairedStatistic primary body anchor activation primaryPool bodyPool table word := by
  rw [← tablePairedStatisticLinear_apply]
  induction table using MvPolynomial.induction_on' with
  | monomial powers scalar =>
    rw [inputKernelPolynomialHom_monomial,MvPolynomial.C_mul',map_smul]
    rw [tablePairedStatisticLinear_apply,tablePairedStatistic_monomial]
    simp only [Pi.smul_apply,smul_eq_mul]
    congr 1
    rw [mixedMonomialSeed,mixedProductSeed,inputKernelPolynomial_mixedFiniteSeed]
    have he := poolCoefficientExtraction_kernelPolynomial primary body anchor activation
      (twoPoolControlKernel (monomialOccurrences powers)) word
    refine Eq.trans ?_ he
    congr 1
    unfold kernelPolynomial
    apply Finset.sum_congr (by ext; simp)
    intro colors _
    rfl
  | add first second hfirst hsecond =>
    simp only [map_add,Pi.add_apply,hfirst,hsecond]

/-- Equality under arbitrary role-specific forms suffices for equality of the
actual full paired score; equality of the ordinary output PGF is not assumed. -/
theorem tablePairedStatistic_of_inputHom_eq (primary body : FiniteDist Color)
    (anchor : Color → Color → ℝ) (activation : ℝ) (primaryPool bodyPool : ℕ)
    (first second : Table (InputSeed Color))
    (hequal : ∀ primaryForm bodyForm : Color → Table (Fin primaryPool⊕Fin bodyPool),
      inputKernelPolynomialHom primaryForm bodyForm first=
        inputKernelPolynomialHom primaryForm bodyForm second) :
    tablePairedStatistic primary body anchor activation primaryPool bodyPool first=
      tablePairedStatistic primary body anchor activation primaryPool bodyPool second := by
  funext word
  rw [← poolCoefficientExtraction_inputHom,← poolCoefficientExtraction_inputHom,hequal]

end
end AFT.RepresentedPolynomial
