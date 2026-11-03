import AFT.OrderedReciprocalFactors
import AFT.IndependentPositiveInverse

/-! # Literal ordered factors for the actual paired positive denominator -/
namespace AFT.V7Calibration
open RationalNumerics RepresentedPolynomial
open scoped BigOperators

/-- A fixed, explicitly ordered list of the fifteen nonempty masks. -/
def actualPairedSelections : List (Finset (Fin 4)) :=
  (List.range 15).map (fun mask => Finset.univ.filter (fun slot : Fin 4 => (mask+1).testBit slot.val))

theorem actualPairedSelections_nodup : actualPairedSelections.Nodup := by decide

theorem actualPairedSelections_set : actualPairedSelections.toFinset=
    (Finset.univ : Finset (Finset (Fin 4))).erase ∅ := by decide

def actualPairedInputFactors : OrderedSeedTable (Finset (Fin 4)) :=
  actualPairedSelections.map (fun selected => ⟨1,[selected]⟩)

def actualPairedReciprocalFactors (depth : ℕ) : OrderedSeedTable (Finset (Fin 4)) :=
  actualPairedInputFactors.reciprocal depth

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local instance pairedReciprocalFactorsFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def actualPairedInputSeed (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (selected : Finset (Fin 4)) : InputSeed (Fin (Parameters.modulus n)) :=
  inversePrimarySeed (actualPrimaryLaw C n beta) (actualBodyLaw C n beta) (GaussianSource.v7Activation C n) operator
    (referenceCoefficientSeed (actualPrimaryLaw C n beta) (actualReferenceLaw C n beta)
      (independentPairedPositiveMass C n beta charts) selected)

theorem actualPairedSelections_sum {Value : Type*} [AddCommMonoid Value] (value : Finset (Fin 4) → Value) :
    (actualPairedSelections.map value).sum=
      ∑ selected∈(Finset.univ : Finset (Finset (Fin 4))).erase ∅,value selected := by
  have hp := List.perm_of_nodup_nodup_toFinset_eq actualPairedSelections_nodup
    (Finset.nodup_toList ((Finset.univ : Finset (Finset (Fin 4))).erase ∅))
    (by
      rw [Finset.toList_toFinset]
      ext selected
      have hh := congrArg (fun set : Finset (Finset (Fin 4)) => selected∈set) actualPairedSelections_set
      simpa only [List.mem_toFinset,Finset.mem_erase,Finset.mem_univ,and_true] using (Iff.of_eq hh))
  rw [(hp.map value).sum_eq,Finset.sum_map_toList]

theorem actualPairedInputFactors_interpret (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark) :
    actualPairedInputFactors.interpret (actualPairedInputSeed C n beta operator charts)=
      independentPositiveInputTable C n beta operator charts := by
  simp only [actualPairedInputFactors,OrderedSeedTable.interpret,List.map_map,Function.comp_def,
    OrderedSeedTerm.interpret,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,Rat.cast_one,one_smul,
    actualPairedSelections_sum,independentPositiveInputTable,referenceInverseTable,referenceCoefficientTable,
    map_sum,inversePrimaryTable,MvPolynomial.aeval_X]
  rfl

/-- The executable ordered expansion denotes the exact original reciprocal,
including the selected seed labels. -/
theorem actualPairedReciprocalFactors_interpret (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark) (depth : ℕ) :
    (actualPairedReciprocalFactors depth).interpret (actualPairedInputSeed C n beta operator charts)=
      independentPositiveReciprocal C n beta operator charts depth := by
  rw [actualPairedReciprocalFactors,OrderedSeedTable.interpret_reciprocal,actualPairedInputFactors_interpret]
  rfl

theorem actualPairedInputFactors_length : actualPairedInputFactors.length=15 := by
  simp only [actualPairedInputFactors,actualPairedSelections,List.length_map,List.length_range]

theorem actualPairedReciprocalFactors_length (depth : ℕ) :
    (actualPairedReciprocalFactors depth).length=∑ count∈Finset.range (depth+1),15^count := by
  rw [actualPairedReciprocalFactors,OrderedSeedTable.reciprocal_length,actualPairedInputFactors_length]

end
end AFT.V7Calibration
