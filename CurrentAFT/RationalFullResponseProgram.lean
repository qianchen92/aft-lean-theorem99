import CurrentAFT.RationalPackedRootSource
import CurrentAFT.RationalBackgroundPopulationProgram
import CurrentAFT.RationalScalarFamilyAverage
import CurrentAFT.FullResponsePointFormula

/-! The complete rational response column: actual distinct control choices,
bounded root tags, and the three population products under one shared queue.
The final subtraction produces the defect matrix used by iteration. -/
namespace CurrentAFT.RationalFullResponseProgram
open AFT ActualBlockFock TaggedSelection GradedControlAlgebra RationalFamilyProductProgram
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension

def centerSplit (security : ℕ) :
    (Fin (Parameters.legCount security) ⊕ Fin (BackgroundRates.ordinaryPool security)) ≃ Fin (centerCount security) :=
  finSumFinEquiv.trans (finCongr (UniformTaggedOutput.centerCount_split security))

def selection (security r s : ℕ) (choice : UniformTaggedOutput.Choice security r s) : Selection security r s where
  primary := choice.1
  compensator := choice.1.trans ⟨fun index => centerSplit security (.inl index),
    fun _ _ he => Sum.inl.inj ((centerSplit security).injective he)⟩
  body := choice.2.trans ⟨fun index => centerSplit security (.inr index),
    fun _ _ he => Sum.inr.inj ((centerSplit security).injective he)⟩
  separated _ _ he := by
    have h := (centerSplit security).injective he
    cases h

theorem selection_eq (security r s : ℕ) (choice : UniformTaggedOutput.Choice security r s) :
    selection security r s choice = UniformTaggedOutput.selection security r s choice := rfl

def tags (security order : ℕ) : Finset (Finset (BlockIndex security)) :=
  (FullResponseEnumeration.boundedSubsets (BlockIndex security) order).filter (fun tagged => 2 ≤ tagged.card)

def selected {security r s : ℕ} (bits order : ℕ) (queue : ℤ) (chosen : Selection security r s)
    (sourcePrimary : Fin r → ℕ) (sourceBody : Fin s → ℕ) : Table ℚ ℕ ℕ order :=
  fun arity colors centers =>
    RationalPackedRootProgram.current security bits order queue (RationalPackedRootProgram.actualMetadata chosen ∅)
      sourcePrimary sourceBody arity colors centers +
    ∑ tagged ∈ tags security order,
      RationalPackedRootProgram.current security bits order queue (RationalPackedRootProgram.actualMetadata chosen tagged)
        sourcePrimary sourceBody arity colors centers

def choiceAverage (security bits order r s : ℕ) (queue : ℤ)
    (sourcePrimary : Fin r → ℕ) (sourceBody : Fin s → ℕ) : Table ℚ ℕ ℕ order :=
  letI := CyclePatternProgram.selectionFintype (Parameters.legCount security) r
  letI := CyclePatternProgram.selectionFintype (BackgroundRates.ordinaryPool security) s
  fun arity colors centers =>
    (∑ choice : UniformTaggedOutput.Choice security r s,
      selected bits order queue (selection security r s choice) sourcePrimary sourceBody arity colors centers) /
      (((Parameters.legCount security).descFactorial r : ℚ)*((BackgroundRates.ordinaryPool security).descFactorial s : ℚ))

def fixedQueue (security bits order r s : ℕ) (queue : ℤ)
    (sourcePrimary : Fin r → ℕ) (sourceBody : Fin s → ℕ) : Table ℚ ℕ ℕ order :=
  product order (RationalBackgroundPopulationProgram.current security bits order queue)
    (choiceAverage security bits order r s queue sourcePrimary sourceBody)

def response (security bits order r s : ℕ)
    (sourcePrimary : Fin r → ℕ) (sourceBody : Fin s → ℕ) : Table ℚ ℕ ℕ order :=
  RationalScalarFamilyAverage.current security bits order
    (fun queue => fixedQueue security bits order r s queue sourcePrimary sourceBody)

def basis (security bits order : ℕ) (source : TruncatedArity order)
    (sourcePrimary : Fin source.val.1.val → ℕ) (sourceBody : Fin source.val.2.val → ℕ) : Table ℚ ℕ ℕ order :=
  fun output colors centers => if h : output = source then
    WeightedPointKernelProgram.current security bits source.val.1.val source.val.2.val sourcePrimary sourceBody
      (fun index => colors (index.cast (congrArg (fun arity : TruncatedArity order => arity.val.1.val) h).symm))
      (fun index => centers (index.cast (congrArg (fun arity : TruncatedArity order => arity.val.2.val) h).symm))
    else 0

def defect (security bits order : ℕ) (source : TruncatedArity order)
    (sourcePrimary : Fin source.val.1.val → ℕ) (sourceBody : Fin source.val.2.val → ℕ) : Table ℚ ℕ ℕ order :=
  response security bits order source.val.1.val source.val.2.val sourcePrimary sourceBody-
    basis security bits order source sourcePrimary sourceBody

end CurrentAFT.RationalFullResponseProgram
