import CurrentAFT.BinaryCoefficientExtraction
import CurrentAFT.BinaryFiniteCoefficient
import CurrentAFT.RationalLocalFamilyProgram

/-! # A stored four-endpoint subset inserted in its actual coefficient fiber -/
namespace CurrentAFT.BinaryPrimarySelectedCoefficient
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  GradedControlAlgebra RationalRejectionProgram BinaryFamilyProduct
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

structure Entry where
  selected : Finset (Fin 4)
  slots : Vector (Fin 4) selected.card
  program : BinaryStoredSymmetrization.Program selected.card

def finite (security bits order : ℕ) (entry : Entry)
    (mass : Vector (Fin (BinaryFirstInverseProgram.colors security)) 4 → RationalResult) :
    BinaryFiniteCoefficient.FiniteProgram security order := fun arity colors centers =>
  let result := BinaryCoefficientFiber.current security arity.val.1.val arity.val.2.val entry.selected.card 0 colors centers
    (fun inputs _ => BinaryCoefficientExtraction.current security bits entry.slots entry.program inputs mass)
  ⟨result.data,result.work+4⟩

def current (security bits order : ℕ) (entry : Entry)
    (mass : Vector (Fin (BinaryFirstInverseProgram.colors security)) 4 → RationalResult) : CoefficientProgram order :=
  BinaryFiniteCoefficient.lift security order (finite security bits order entry mass)

noncomputable section
open scoped Classical

theorem finite_value (security bits order : ℕ) (entry : Entry)
    (hslots : ∀ index, entry.slots.get index=((Finset.orderIsoOfFin entry.selected rfl) index).val)
    (hprogram : entry.program.meaning RationalBits.decode=BinaryStoredSymmetrization.meanSyntax entry.selected.card)
    (mass : Vector (Fin (BinaryFirstInverseProgram.colors security)) 4 → RationalResult)
    (value : (Fin 4 → ℕ) → ℚ) (hmass : ∀ source, (mass source).data.decode=value (fun index => (source.get index).val))
    (arity : TruncatedArity order) (colors : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.1.val)
    (centers : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.2.val) :
    (finite security bits order entry mass arity colors centers).data.decode=
      RationalLocalFamilyProgram.insertSelected order entry.selected
        (RationalCoefficientExtraction.selectedKernel security bits value entry.selected)
          arity (fun index => (colors.get index).val) (fun index => (centers.get index).val) := by
  unfold finite
  rw [BinaryCoefficientFiber.current_value]
  unfold RationalLocalFamilyProgram.insertSelected
  by_cases hshape : arity.val.1.val=entry.selected.card ∧ arity.val.2.val=0
  · have hmatch : entry.selected.card=arity.val.1.val ∧ 0=arity.val.2.val := ⟨hshape.1.symm,hshape.2.symm⟩
    rw [dif_pos hshape,dif_pos hmatch,BinaryCoefficientExtraction.current_value security bits entry.selected entry.slots
      hslots entry.program hprogram _ mass value hmass]
    congr 1
  · have hn : ¬(entry.selected.card=arity.val.1.val ∧ 0=arity.val.2.val) := fun h => hshape ⟨h.1.symm,h.2.symm⟩
    rw [dif_neg hshape,dif_neg hn]

theorem current_value (security bits order : ℕ) (entry : Entry)
    (hslots : ∀ index, entry.slots.get index=((Finset.orderIsoOfFin entry.selected rfl) index).val)
    (hprogram : entry.program.meaning RationalBits.decode=BinaryStoredSymmetrization.meanSyntax entry.selected.card)
    (mass : Vector (Fin (BinaryFirstInverseProgram.colors security)) 4 → RationalResult)
    (value : (Fin 4 → ℕ) → ℚ) (hmass : ∀ source, (mass source).data.decode=value (fun index => (source.get index).val))
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryFirstInverseProgram.colors security) (hd : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    (current security bits order entry mass arity colors centers).value.decode=
      RationalLocalFamilyProgram.insertSelected order entry.selected
        (RationalCoefficientExtraction.selectedKernel security bits value entry.selected) arity colors.get centers.get :=
  BinaryFiniteCoefficient.lift_value security order _ _ (finite_value security bits order entry hslots hprogram mass value hmass)
    arity colors centers hc hd

def heightPolynomial (entry : Entry) (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCoefficientExtraction.heightPolynomial 4 entry.program precision inputBits
def finiteWorkPolynomial (order : ℕ) (entry : Entry) (precision inputBits inputWork : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (6*order+8*entry.selected.card+34)+BinaryCoefficientExtraction.workPolynomial 4 entry.program precision inputBits inputWork
def workPolynomial (order : ℕ) (entry : Entry) (precision inputBits inputWork : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFiniteCoefficient.workPolynomial order (finiteWorkPolynomial order entry precision inputBits inputWork)

theorem finite_bounds (security order : ℕ) (entry : Entry) (precision inputBits inputWork : Polynomial ℕ)
    (mass : Vector (Fin (BinaryFirstInverseProgram.colors security)) 4 → RationalResult)
    (hh : ∀ source, HeightBound (mass source).data.decode (inputBits.eval security))
    (hw : ∀ source, (mass source).work ≤ inputWork.eval security)
    (arity : TruncatedArity order) (colors : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.1.val)
    (centers : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.2.val) :
    HeightBound (finite security (precision.eval security) order entry mass arity colors centers).data.decode
      ((heightPolynomial entry precision inputBits).eval security) ∧
      (finite security (precision.eval security) order entry mass arity colors centers).work ≤
        (finiteWorkPolynomial order entry precision inputBits inputWork).eval security := by
  have hk (inputs : Vector (Fin (BinaryFirstInverseProgram.colors security)) entry.selected.card) :=
    BinaryCoefficientExtraction.current_bounds security precision inputBits inputWork entry.slots entry.program inputs mass hh hw
  have h := BinaryCoefficientFiber.current_bounds security arity.val.1.val arity.val.2.val entry.selected.card 0 colors centers
    (fun inputs _ => BinaryCoefficientExtraction.current security (precision.eval security) entry.slots entry.program inputs mass)
    ((heightPolynomial entry precision inputBits).eval security)
    ((BinaryCoefficientExtraction.workPolynomial 4 entry.program precision inputBits inputWork).eval security)
    (fun inputs _ => (hk inputs).1) (fun inputs _ => (hk inputs).2)
  constructor
  · exact h.1
  · change (BinaryCoefficientFiber.current _ _ _ _ _ _ _ _).work+4 ≤ _
    simp only [finiteWorkPolynomial,Polynomial.eval_add,Polynomial.eval_C]
    have ha := arity.property
    omega

theorem current_bounds (security order : ℕ) (entry : Entry) (precision inputBits inputWork : Polynomial ℕ)
    (mass : Vector (Fin (BinaryFirstInverseProgram.colors security)) 4 → RationalResult)
    (hh : ∀ source, HeightBound (mass source).data.decode (inputBits.eval security))
    (hw : ∀ source, (mass source).work ≤ inputWork.eval security)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryFirstInverseProgram.colors security) (hd : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    HeightBound (current security (precision.eval security) order entry mass arity colors centers).value.decode
      ((heightPolynomial entry precision inputBits).eval security) ∧
      (current security (precision.eval security) order entry mass arity colors centers).work ≤
        (workPolynomial order entry precision inputBits inputWork).eval security :=
  BinaryFiniteCoefficient.lift_bounds security order _ _ (finite security (precision.eval security) order entry mass)
    (fun arity colors centers => (finite_bounds security order entry precision inputBits inputWork mass hh hw arity colors centers).1)
    (fun arity colors centers => (finite_bounds security order entry precision inputBits inputWork mass hh hw arity colors centers).2)
    arity colors centers hc hd

def Valid (entry : Entry) : Prop :=
  (∀ index, entry.slots.get index=((Finset.orderIsoOfFin entry.selected rfl) index).val) ∧
    entry.program.meaning RationalBits.decode=BinaryStoredSymmetrization.meanSyntax entry.selected.card

theorem exists_entry (selected : Finset (Fin 4)) : ∃ entry : Entry, entry.selected=selected ∧ Valid entry := by
  obtain ⟨program,hprogram⟩ := BinaryStoredSymmetrization.exists_stored selected.card
  refine ⟨⟨selected,Vector.ofFn (fun index => ((Finset.orderIsoOfFin selected rfl) index).val),program⟩,rfl,?_,hprogram⟩
  intro index
  exact Vector.get_ofFn _ _

theorem exists_entries : ∃ entries : Vector Entry 16, ∃ ordering : Fin 16 ≃ Finset (Fin 4),
    (∀ index, (entries.get index).selected=ordering index) ∧ ∀ index, Valid (entries.get index) := by
  have hcard : Fintype.card (Finset (Fin 4))=16 := by simp
  let ordering : Fin 16 ≃ Finset (Fin 4) := (Fintype.equivFinOfCardEq hcard).symm
  choose entry hselected hvalid using exists_entry
  refine ⟨Vector.ofFn (fun index => entry (ordering index)),ordering,?_,?_⟩
  · intro index
    rw [Vector.get_ofFn]
    exact hselected _
  · intro index
    rw [Vector.get_ofFn]
    exact hvalid _

end
end CurrentAFT.BinaryPrimarySelectedCoefficient
