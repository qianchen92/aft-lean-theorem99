import AFT.OrderedIndependentTable
import AFT.ParametricOrderedOperations

/-! # The actual independent upper map with explicit real scalar expressions -/
namespace AFT.RationalNumerics
open V7Calibration

/-- Rational literals in a finite structural column become scalar expression
nodes. This does not approximate any real source coefficient. -/
def ParametricSeedTable.ofOrdered {Scalar Code : Type*} (table : OrderedSeedTable Code) : ParametricSeedTable Scalar Code :=
  table.map (fun term => ⟨.rational term.coefficient,term.factors⟩)

def parametricIndependentUpperTable {Scalar Leaf : Type*} {bound : ℕ}
    (numbering : FixedOrderNumberingCode bound) (shape : Leaf → KernelShape)
    (cutoff depth : ℕ) (table : ParametricSeedTable Scalar Leaf) :
    ParametricSeedTable Scalar (IndependentQuotientCode (List Leaf)) :=
  table.flatMap (fun term =>
    (ParametricSeedTable.ofOrdered (orderedIndependentUpperFactors numbering shape term.factors cutoff depth)).scale term.coefficient)

@[simp] theorem ParametricSeedTable.ofOrdered_length {Scalar Code : Type*} (table : OrderedSeedTable Code) :
    (ofOrdered (Scalar := Scalar) table).length=table.length := List.length_map _

@[simp] theorem ParametricSeedTable.scale_length {Scalar Code : Type*} (scalar : ScalarProgram Scalar)
    (table : ParametricSeedTable Scalar Code) : (table.scale scalar).length=table.length := List.length_map _

theorem parametricIndependentUpperTable_length {Scalar Leaf : Type*} {bound : ℕ}
    (numbering : FixedOrderNumberingCode bound) (shape : Leaf → KernelShape)
    (cutoff depth : ℕ) (table : ParametricSeedTable Scalar Leaf)
    (hd : ∀ term∈table,(orderedJointShape shape term.factors).primary+(orderedJointShape shape term.factors).body ≤ cutoff) :
    (parametricIndependentUpperTable numbering shape cutoff depth table).length ≤ table.length*orderedUpperColumnSize cutoff depth := by
  induction table with
  | nil => simp [parametricIndependentUpperTable]
  | cons term rest ih =>
    simp only [parametricIndependentUpperTable,List.flatMap_cons,List.length_append,
      ParametricSeedTable.scale_length,ParametricSeedTable.ofOrdered_length,List.length_cons]
    have ht := orderedIndependentUpperFactors_length numbering shape cutoff depth term.factors (hd term (List.mem_cons_self ..))
    have hr := ih (fun other ho => hd other (List.mem_cons_of_mem _ ho))
    exact (Nat.add_le_add ht hr).trans_eq (by ring)

noncomputable section
open RepresentedPolynomial

theorem ParametricSeedTable.interpret_ofOrdered {Scalar Code Seed : Type*} (leaf : Scalar → ℝ)
    (decode : Code → Seed) (table : OrderedSeedTable Code) :
    (ofOrdered table).interpret leaf decode=table.interpret decode := by
  induction table with
  | nil => rfl
  | cons term rest ih =>
    simp only [ofOrdered,List.map_cons,interpret_cons,OrderedSeedTable.interpret_cons,
      ParametricSeedTerm.interpret,OrderedSeedTerm.interpret,ScalarProgram.denote]
    exact congrArg (fun value => (term.coefficient : ℝ) •
      (term.factors.map (fun code => MvPolynomial.X (decode code))).prod+value) ih

end

noncomputable section
open RepresentedPolynomial GaussianSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {Scalar Leaf Output : Type*} {bound : ℕ}
variable (numbering : FixedOrderNumberingCode bound)
    (hnumbering : ∀ order point mask slot,numbering.primaryLookup order point mask slot=pendingNumberingMeaning order point mask slot)
    (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (shape : Leaf → KernelShape)
    (value : (label : Leaf) → (Fin ((shape label).primary+(shape label).body) → Fin (Parameters.modulus n)) → ℝ)

include hnumbering in
/-- This statement applies U to every signed coefficient of the actual
literal table.  The input keeps ordered factors and repeated labels. -/
theorem parametricIndependentUpperTable_polynomial (scalar : Scalar → ℝ) (cutoff depth : ℕ) (table : ParametricSeedTable Scalar Leaf)
    (hcanonical : ∀ label,Hoeffding.Canonical
      (inputReference (actualPrimaryLaw C n beta) (actualBodyLaw C n beta) (shapeSeed (shape label) (value label)))
      Finset.univ (value label))
    (hshape : ∀ term∈table,4*(orderedJointShape shape term.factors).primary ≤ bound ∧
      (orderedJointShape shape term.factors).body ≤ bound ∧
      (orderedJointShape shape term.factors).primary+(orderedJointShape shape term.factors).body ≤ cutoff)
    (primary body : Fin (Parameters.modulus n) → Table Output) :
    inputKernelPolynomialHom primary body
      ((parametricIndependentUpperTable numbering shape cutoff depth table).interpret scalar
        (orderedIndependentDecode C n beta operator charts shape value))=
      inputKernelPolynomialHom primary body
        (independentUpperLinear C n beta operator charts cutoff depth
          (table.interpret scalar (fun label => shapeSeed (shape label) (value label)))) := by
  induction table with
  | nil => simp [parametricIndependentUpperTable]
  | cons term rest ih =>
    have hs := hshape term (List.mem_cons_self ..)
    have hc : ∀ seed∈(orderedSeedPowers (fun label => shapeSeed (shape label) (value label)) term.factors).support,
        Hoeffding.Canonical (inputReference (actualPrimaryLaw C n beta) (actualBodyLaw C n beta) seed) Finset.univ seed.kernel := by
      intro seed hseed
      obtain ⟨label,_,rfl⟩ := orderedSeedPowers_support _ _ hseed
      exact hcanonical label
    have hd : weightedOrder (fun seed => seed.primaryOrder+seed.bodyOrder)
        (orderedSeedPowers (fun label => shapeSeed (shape label) (value label)) term.factors) ≤ cutoff := by
      rw [orderedSeedPowers_order]
      change (term.factors.map (fun label => (shape label).primary+(shape label).body)).sum ≤ cutoff
      rw [←orderedJointShape_order shape term.factors]
      exact hs.2.2
    have hcolumn := orderedIndependentUpperFactors_polynomial numbering hnumbering C n beta operator charts
      shape value term.factors hs.1 hs.2.1 cutoff depth hc hd primary body
    have hr := ih (fun other ho => hshape other (List.mem_cons_of_mem _ ho))
    change inputKernelPolynomialHom primary body
      ((((ParametricSeedTable.ofOrdered (orderedIndependentUpperFactors numbering shape term.factors cutoff depth)).scale term.coefficient) ++
        parametricIndependentUpperTable numbering shape cutoff depth rest).interpret scalar _)=_
    rw [ParametricSeedTable.interpret_append,ParametricSeedTable.interpret_scale,ParametricSeedTable.interpret_ofOrdered,
      map_add,inputKernelPolynomialHom_smul,hcolumn,hr,ParametricSeedTable.interpret_cons,map_add,map_add]
    congr 1
    rw [ParametricSeedTerm.interpret_monomial]
    change (term.coefficient.denote scalar) • inputKernelPolynomialHom primary body (_)=
      inputKernelPolynomialHom primary body (Finsupp.linearCombination ℝ _
        (Finsupp.single (orderedSeedPowers (fun label => shapeSeed (shape label) (value label)) term.factors) (term.coefficient.denote scalar)))
    rw [Finsupp.linearCombination_single,inputKernelPolynomialHom_smul]

end
end AFT.RationalNumerics
