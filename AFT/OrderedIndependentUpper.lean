import AFT.OrderedIndependentColumn
import AFT.OrderedTruncation
import AFT.IndependentUpperPolynomial

/-! # The runnable ordered U column implements the actual weighted cutoff -/
namespace AFT.RationalNumerics

def independentQuotientShape {Leaf : Type*} (shape : Leaf → KernelShape) : IndependentQuotientCode Leaf → KernelShape :=
  Sum.elim (fun code => code.shape shape) (Sum.elim (fun selected => ⟨selected.card,0⟩) (fun _ => ⟨1,0⟩))

def orderedIndependentUpperFactors {Leaf : Type*} {bound : ℕ}
    (numbering : FixedOrderNumberingCode bound) (shape : Leaf → KernelShape)
    (factors : List Leaf) (cutoff depth : ℕ) : OrderedSeedTable (IndependentQuotientCode (List Leaf)) :=
  (orderedIndependentColumnFactors numbering shape factors depth).truncate
    (fun code => let s := independentQuotientShape (orderedJointShape shape) code;s.primary+s.body) cutoff

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

theorem independentQuotientDecode_shape (decode : Leaf → InputSeed (Fin (Parameters.modulus n)))
    (hshape : ∀ label,(decode label).primaryOrder=(shape label).primary ∧ (decode label).bodyOrder=(shape label).body)
    (code : IndependentQuotientCode Leaf) :
    (independentQuotientDecode C n beta operator charts decode code).primaryOrder=(independentQuotientShape shape code).primary ∧
      (independentQuotientDecode C n beta operator charts decode code).bodyOrder=(independentQuotientShape shape code).body := by
  rcases code with code|selected|value
  · exact code.denote_shape C n beta operator charts decode shape hshape
  · change Fintype.card selected=selected.card ∧ (0 : ℕ)=0
    simp only [Fintype.card_coe,and_self]
  · exact ⟨rfl,rfl⟩

theorem orderedIndependentUpperFactors_interpret (factors : List Leaf) (cutoff depth : ℕ) :
    (orderedIndependentUpperFactors numbering shape factors cutoff depth).interpret
      (orderedIndependentDecode C n beta operator charts shape value)=
      truncate (fun seed => seed.primaryOrder+seed.bodyOrder) cutoff
        ((orderedIndependentColumnFactors numbering shape factors depth).interpret
          (orderedIndependentDecode C n beta operator charts shape value)) := by
  apply OrderedSeedTable.interpret_truncate
  intro code
  have hs := independentQuotientDecode_shape C n beta operator charts (orderedJointShape shape)
    (orderedJointSeed shape value) (fun _ => ⟨rfl,rfl⟩) code
  exact congrArg₂ Nat.add hs.1 hs.2

include hnumbering in
theorem orderedIndependentUpperFactors_polynomial (factors : List Leaf)
    (hp : 4*(orderedJointShape shape factors).primary ≤ bound)
    (hb : (orderedJointShape shape factors).body ≤ bound) (cutoff depth : ℕ)
    (hc : ∀ seed∈(orderedSeedPowers (fun label => shapeSeed (shape label) (value label)) factors).support,
      Hoeffding.Canonical (inputReference (actualPrimaryLaw C n beta) (actualBodyLaw C n beta) seed) Finset.univ seed.kernel)
    (hd : weightedOrder (fun seed => seed.primaryOrder+seed.bodyOrder)
      (orderedSeedPowers (fun label => shapeSeed (shape label) (value label)) factors) ≤ cutoff)
    (primary body : Fin (Parameters.modulus n) → Table Output) :
    inputKernelPolynomialHom primary body
      ((orderedIndependentUpperFactors numbering shape factors cutoff depth).interpret
        (orderedIndependentDecode C n beta operator charts shape value))=
      inputKernelPolynomialHom primary body (independentUpperColumn C n beta operator charts cutoff depth
        (orderedSeedPowers (fun label => shapeSeed (shape label) (value label)) factors)) := by
  rw [orderedIndependentUpperFactors_interpret]
  simp only [independentUpperColumn,if_pos (And.intro hd hc)]
  apply inputKernelPolynomialHom_truncate_congr
  exact orderedIndependentColumnFactors_polynomial numbering hnumbering C n beta operator charts shape value factors hp hb depth _ _

end
end AFT.RationalNumerics
