import AFT.OrderedJointRole
import AFT.IndependentQuotientProgram
import AFT.IndependentRolePolynomial
import AFT.PairedPolynomialExtraction

/-! # Runnable ordered U columns have the original complete paired score

The runtime keeps factor occurrences and uses explicit coordinate offsets.
The real-label monomial enumeration appears only in the specification.
-/
namespace AFT.RationalNumerics

def orderedIndependentQuotientFactors {Leaf : Type*} {bound : ℕ}
    (numbering : FixedOrderNumberingCode bound) (shape : Leaf → KernelShape)
    (factors : List Leaf) (depth : ℕ) : OrderedSeedTable (IndependentQuotientCode (List Leaf)) :=
  independentQuotientFactors numbering (orderedJointShape shape) (.leaf factors) depth

def orderedIndependentColumnFactors {Leaf : Type*} {bound : ℕ}
    (numbering : FixedOrderNumberingCode bound) (shape : Leaf → KernelShape)
    (factors : List Leaf) (depth : ℕ) : OrderedSeedTable (IndependentQuotientCode (List Leaf)) :=
  orderedIndependentQuotientFactors numbering shape factors depth ++ [⟨-1,[Sum.inl (.leaf factors)]⟩]

noncomputable section
open RepresentedPolynomial V7Calibration GaussianSource
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
variable {Leaf Output : Type*} {bound : ℕ}
variable (numbering : FixedOrderNumberingCode bound)
    (hnumbering : ∀ order point mask slot,numbering.primaryLookup order point mask slot=pendingNumberingMeaning order point mask slot)
    (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (shape : Leaf → KernelShape)
    (value : (label : Leaf) → (Fin ((shape label).primary+(shape label).body) → Fin (Parameters.modulus n)) → ℝ)
    (factors : List Leaf)
    (hp : 4*(orderedJointShape shape factors).primary ≤ bound)
    (hb : (orderedJointShape shape factors).body ≤ bound) (depth : ℕ)

def orderedIndependentDecode : IndependentQuotientCode (List Leaf) → InputSeed (Fin (Parameters.modulus n)) :=
  independentQuotientDecode C n beta operator charts (orderedJointSeed shape value)

include hnumbering hp hb

theorem orderedIndependentQuotientFactors_interpret :
    (orderedIndependentQuotientFactors numbering shape factors depth).interpret
      (orderedIndependentDecode C n beta operator charts shape value)=
      independentGlobalQuotient C n beta operator charts (orderedJointSeed shape value factors) depth := by
  apply independentQuotientFactors_interpret numbering hnumbering
    C n beta operator charts (orderedJointSeed shape value) (orderedJointShape shape)
    (fun _ => ⟨rfl,rfl⟩) (.leaf factors) (And.intro (by omega) hb) hp

theorem orderedIndependentColumnFactors_interpret :
    (orderedIndependentColumnFactors numbering shape factors depth).interpret
      (orderedIndependentDecode C n beta operator charts shape value)=
      independentGlobalQuotient C n beta operator charts (orderedJointSeed shape value factors) depth-
        MvPolynomial.X (orderedJointSeed shape value factors) := by
  rw [orderedIndependentColumnFactors,OrderedSeedTable.interpret_append,
    orderedIndependentQuotientFactors_interpret numbering hnumbering C n beta operator charts shape value factors hp hb depth]
  simp only [OrderedSeedTable.interpret_cons,OrderedSeedTable.interpret_nil,OrderedSeedTerm.interpret,
    List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,Rat.cast_neg,Rat.cast_one,neg_one_smul,
    add_zero,sub_eq_add_neg]
  rfl

/-- Equality holds for every pair of primary/body forms, so it retains all
mixed coefficients required by the actual public paired statistic. -/
theorem orderedIndependentColumnFactors_polynomial (primary body : Fin (Parameters.modulus n) → Table Output) :
    inputKernelPolynomialHom primary body
      ((orderedIndependentColumnFactors numbering shape factors depth).interpret
        (orderedIndependentDecode C n beta operator charts shape value))=
      inputKernelPolynomialHom primary body
        (independentGlobalQuotient C n beta operator charts
          (mixedMonomialSeed (orderedSeedPowers (fun label => shapeSeed (shape label) (value label)) factors)) depth-
            MvPolynomial.X (mixedMonomialSeed
              (orderedSeedPowers (fun label => shapeSeed (shape label) (value label)) factors))) := by
  rw [orderedIndependentColumnFactors_interpret numbering hnumbering C n beta operator charts shape value factors hp hb depth]
  exact independentGlobalQuotient_sub_role_equiv C n beta operator charts primary body
    (orderedJointMonomialRoleEquiv shape value factors) depth

/-- The executable ordering preserves the original complete score, with the
same two without-replacement public-pool normalizers. -/
theorem orderedIndependentColumnFactors_pairedScore
    (primary body : FiniteDist (Fin (Parameters.modulus n)))
    (anchor : Fin (Parameters.modulus n) → Fin (Parameters.modulus n) → ℝ)
    (activation : ℝ) (primaryPool bodyPool : ℕ) :
    tablePairedStatistic primary body anchor activation primaryPool bodyPool
      ((orderedIndependentColumnFactors numbering shape factors depth).interpret
        (orderedIndependentDecode C n beta operator charts shape value))=
    tablePairedStatistic primary body anchor activation primaryPool bodyPool
      (independentGlobalQuotient C n beta operator charts
        (mixedMonomialSeed (orderedSeedPowers (fun label => shapeSeed (shape label) (value label)) factors)) depth-
          MvPolynomial.X (mixedMonomialSeed
            (orderedSeedPowers (fun label => shapeSeed (shape label) (value label)) factors))) := by
  apply tablePairedStatistic_of_inputHom_eq
  intro primaryForm bodyForm
  exact orderedIndependentColumnFactors_polynomial numbering hnumbering C n beta operator charts shape value factors hp hb depth
    primaryForm bodyForm

end
end AFT.RationalNumerics
