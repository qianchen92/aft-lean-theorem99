import AFT.IndependentNumeratorProgram
import AFT.ActualPairedReciprocalFactors
import AFT.ActualBodyInputProgram
import AFT.IndependentGlobalQuotient

/-! # Ordered finite code for both actual positive denominator reciprocals -/
namespace AFT.RationalNumerics

def OrderedSeedTable.relabel {Code Other : Type*} (rename : Code → Other) (table : OrderedSeedTable Code) : OrderedSeedTable Other :=
  table.map (fun term => ⟨term.coefficient,term.factors.map rename⟩)

theorem OrderedSeedTable.relabel_length {Code Other : Type*} (rename : Code → Other) (table : OrderedSeedTable Code) :
    (table.relabel rename).length=table.length := List.length_map ..

abbrev IndependentQuotientCode (Leaf : Type*) := PendingKernelCode Leaf ⊕ (Finset (Fin 4) ⊕ Unit)

def independentQuotientFactors {Leaf : Type*} {bound : ℕ} (numbering : FixedOrderNumberingCode bound)
    (leafShape : Leaf → KernelShape) (code : PendingKernelCode Leaf) (depth : ℕ) :
    OrderedSeedTable (IndependentQuotientCode Leaf) :=
  ((independentNumeratorFactors numbering leafShape code).relabel Sum.inl).multiply
    (((V7Calibration.actualPairedReciprocalFactors depth).relabel (fun selected => Sum.inr (Sum.inl selected))).power
      (code.shape leafShape).primary) |>.multiply
    (((V7Calibration.actualBodyReciprocalFactors depth).relabel (fun value => Sum.inr (Sum.inr value))).power
      (code.shape leafShape).body)

noncomputable section
open RepresentedPolynomial V7Calibration GaussianSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem OrderedSeedTable.interpret_relabel {Code Other Seed : Type*} (decode : Other → Seed)
    (rename : Code → Other) (table : OrderedSeedTable Code) :
    (table.relabel rename).interpret decode=table.interpret (decode ∘ rename) := by
  simp only [relabel,interpret,List.map_map,OrderedSeedTerm.interpret,Function.comp_def]
  rfl

def independentQuotientDecode {Leaf : Type*} (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (decode : Leaf → InputSeed (Fin (Parameters.modulus n))) :
    IndependentQuotientCode Leaf → InputSeed (Fin (Parameters.modulus n)) :=
  Sum.elim (PendingKernelCode.denote C n beta operator charts decode)
    (Sum.elim (actualPairedInputSeed C n beta operator charts) (fun _ => actualBodyInputSeed C n beta operator))

theorem independentQuotientFactors_interpret {Leaf : Type*} {bound : ℕ} (numbering : FixedOrderNumberingCode bound)
    (hnumbering : ∀ order point mask slot,numbering.primaryLookup order point mask slot=pendingNumberingMeaning order point mask slot)
    (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (decode : Leaf → InputSeed (Fin (Parameters.modulus n))) (leafShape : Leaf → KernelShape)
    (hshape : ∀ leaf,(decode leaf).primaryOrder=(leafShape leaf).primary ∧ (decode leaf).bodyOrder=(leafShape leaf).body)
    (code : PendingKernelCode Leaf) (hc : code.Valid bound leafShape)
    (hbound : 4*(code.shape leafShape).primary≤bound) (depth : ℕ) :
    (independentQuotientFactors numbering leafShape code depth).interpret
      (independentQuotientDecode C n beta operator charts decode)=
      independentGlobalQuotient C n beta operator charts (code.denote C n beta operator charts decode) depth := by
  simp only [independentQuotientFactors,OrderedSeedTable.interpret_multiply,OrderedSeedTable.interpret_power,
    OrderedSeedTable.interpret_relabel,independentQuotientDecode,Function.comp_def,Sum.elim_inl,Sum.elim_inr]
  rw [independentNumeratorFactors_interpret numbering hnumbering C n beta operator charts decode leafShape hshape code hc hbound,
    actualPairedReciprocalFactors_interpret,actualBodyReciprocalFactors_interpret]
  unfold independentGlobalQuotient
  rw [(code.denote_shape C n beta operator charts decode leafShape hshape).1,
    (code.denote_shape C n beta operator charts decode leafShape hshape).2]

end
end AFT.RationalNumerics
