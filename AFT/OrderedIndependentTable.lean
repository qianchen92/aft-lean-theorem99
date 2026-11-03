import AFT.OrderedIndependentUpper
import AFT.OrderedFactorResources

/-! # Whole ordered input tables implement the original independent upper map -/
namespace AFT.RationalNumerics
open V7Calibration
open scoped BigOperators

def orderedIndependentUpperTable {Leaf : Type*} {bound : ℕ}
    (numbering : FixedOrderNumberingCode bound) (shape : Leaf → KernelShape)
    (cutoff depth : ℕ) (table : OrderedSeedTable Leaf) : OrderedSeedTable (IndependentQuotientCode (List Leaf)) :=
  table.flatMap (fun term => (orderedIndependentUpperFactors numbering shape term.factors cutoff depth).scale term.coefficient)

def orderedUpperColumnSize (cutoff depth : ℕ) : ℕ :=
  12^cutoff*(∑ count∈Finset.range (depth+1),15^count)^cutoff*(depth+1)^cutoff+1

theorem orderedJointShape_order {Leaf : Type*} (shape : Leaf → KernelShape) (factors : List Leaf) :
    (orderedJointShape shape factors).primary+(orderedJointShape shape factors).body=
      (factors.map (fun label => (shape label).primary+(shape label).body)).sum := by
  induction factors with
  | nil => rfl
  | cons label rest ih =>
    simp only [orderedJointShape,KernelShape.join,List.map_cons,List.sum_cons]
    omega

theorem orderedIndependentUpperFactors_length {Leaf : Type*} {bound : ℕ}
    (numbering : FixedOrderNumberingCode bound) (shape : Leaf → KernelShape)
    (cutoff depth : ℕ) (factors : List Leaf)
    (hd : (orderedJointShape shape factors).primary+(orderedJointShape shape factors).body ≤ cutoff) :
    (orderedIndependentUpperFactors numbering shape factors cutoff depth).length ≤ orderedUpperColumnSize cutoff depth := by
  apply (List.length_filter_le _ _).trans
  apply (orderedIndependentColumnFactors_length numbering shape factors depth).trans
  have hp : (orderedJointShape shape factors).primary ≤ cutoff := by omega
  have hb : (orderedJointShape shape factors).body ≤ cutoff := by omega
  have hsum : 1 ≤ ∑ count∈Finset.range (depth+1),15^count := by
    have hh := Finset.single_le_sum (f:=fun count : ℕ => 15^count) (fun _ _ => Nat.zero_le _)
      (show 0∈Finset.range (depth+1) by simp)
    simpa only [pow_zero] using hh
  unfold orderedUpperColumnSize
  gcongr <;> omega

theorem orderedIndependentUpperTable_length {Leaf : Type*} {bound : ℕ}
    (numbering : FixedOrderNumberingCode bound) (shape : Leaf → KernelShape)
    (cutoff depth : ℕ) (table : OrderedSeedTable Leaf)
    (hd : ∀ term∈table,(orderedJointShape shape term.factors).primary+(orderedJointShape shape term.factors).body ≤ cutoff) :
    (orderedIndependentUpperTable numbering shape cutoff depth table).length ≤ table.length*orderedUpperColumnSize cutoff depth := by
  induction table with
  | nil => simp [orderedIndependentUpperTable]
  | cons term rest ih =>
    simp only [orderedIndependentUpperTable,List.flatMap_cons,List.length_append,
      OrderedSeedTable.scale_length,List.length_cons]
    have ht := orderedIndependentUpperFactors_length numbering shape cutoff depth term.factors (hd term (List.mem_cons_self ..))
    have hr := ih (fun other ho => hd other (List.mem_cons_of_mem _ ho))
    exact (Nat.add_le_add ht hr).trans_eq (by ring)

noncomputable section
open RepresentedPolynomial GaussianSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {Leaf Output : Type*} {bound : ℕ}
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
theorem orderedIndependentUpperTable_polynomial (cutoff depth : ℕ) (table : OrderedSeedTable Leaf)
    (hcanonical : ∀ label,Hoeffding.Canonical
      (inputReference (actualPrimaryLaw C n beta) (actualBodyLaw C n beta) (shapeSeed (shape label) (value label)))
      Finset.univ (value label))
    (hshape : ∀ term∈table,4*(orderedJointShape shape term.factors).primary ≤ bound ∧
      (orderedJointShape shape term.factors).body ≤ bound ∧
      (orderedJointShape shape term.factors).primary+(orderedJointShape shape term.factors).body ≤ cutoff)
    (primary body : Fin (Parameters.modulus n) → Table Output) :
    inputKernelPolynomialHom primary body
      ((orderedIndependentUpperTable numbering shape cutoff depth table).interpret
        (orderedIndependentDecode C n beta operator charts shape value))=
      inputKernelPolynomialHom primary body
        (independentUpperLinear C n beta operator charts cutoff depth
          (table.interpret (fun label => shapeSeed (shape label) (value label)))) := by
  induction table with
  | nil => simp [orderedIndependentUpperTable]
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
      (((orderedIndependentUpperFactors numbering shape term.factors cutoff depth).scale term.coefficient ++
        orderedIndependentUpperTable numbering shape cutoff depth rest).interpret _)=_
    rw [OrderedSeedTable.interpret_append,OrderedSeedTable.interpret_scale,map_add,inputKernelPolynomialHom_smul,hcolumn,hr,
      OrderedSeedTable.interpret_cons,map_add,map_add]
    congr 1
    rw [OrderedSeedTerm.interpret_monomial]
    change (term.coefficient : ℝ) • inputKernelPolynomialHom primary body (_)=
      inputKernelPolynomialHom primary body (Finsupp.linearCombination ℝ _
        (Finsupp.single (orderedSeedPowers (fun label => shapeSeed (shape label) (value label)) term.factors) (term.coefficient : ℝ)))
    rw [Finsupp.linearCombination_single,inputKernelPolynomialHom_smul]

end
end AFT.RationalNumerics
