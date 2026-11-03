import CurrentAFT.BinaryNormalizedPrimary
import CurrentAFT.BinaryLegGroup
import CurrentAFT.BinaryOrdinaryGroup
import CurrentAFT.BinarySingletonGroup
import CurrentAFT.RationalRootGroupProgram

/-! # Every actual grouped response column has an executed binary producer

The stored multiplication and subset programs are fixed before security.
Their correctness assertions verify finite metadata, not response bounds.
-/
namespace CurrentAFT.BinaryRootGroupProgram
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  RationalRejectionProgram BinaryFamilyProduct FixedFamilyPrograms
open RationalRootGroupProgram (LocalRole)
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

structure Data (order : ℕ) where
  programs : List (Entry order)
  primaryFallback : BinaryNormalizedPrimary.Descriptor
  primaryEntries : Vector BinaryNormalizedPrimary.Descriptor 16
  legFallback : BinaryLegGroup.Descriptor
  legEntries : Vector BinaryLegGroup.Descriptor 8

def Correct {order : ℕ} (data : Data order) : Prop :=
  FixedFamilyPrograms.Correct order data.programs ∧ FixedFamilyPrograms.Complete order data.programs ∧
    (∃ ordering : Fin 16 ≃ Finset (Fin 4), (∀ index, (data.primaryEntries.get index).selected=ordering index) ∧
      ∀ index, BinaryPrimarySelectedCoefficient.Valid (data.primaryEntries.get index)) ∧
    (∃ ordering : Fin 8 ≃ Finset (Fin 3), (∀ index, (data.legEntries.get index).selected=ordering index) ∧
      ∀ index, BinaryLegSelectedCoefficient.Valid (data.legEntries.get index))

def primary (security bits order : ℕ) (data : Data order) (source : Vector (Fin (colors security)) 3) : CoefficientProgram order :=
  fun arity inputs centers =>
    let comp := readVector (BinaryFirstFamily.first security) source 0
    let attach := readVector (BinaryFirstFamily.first security) source 1
    let control := readVector (BinaryFirstFamily.first security) source 2
    let result := BinaryNormalizedPrimary.current security bits order data.programs data.primaryFallback data.primaryEntries
      comp.value attach.value control.value arity inputs centers
    ⟨result.value,comp.work+attach.work+control.work+result.work+4⟩

def localTable (security bits order : ℕ) (data : Data order) (queue : IntegerBits) (role : LocalRole)
    (source : Vector (Fin (colors security)) 3) : CoefficientProgram order :=
  let table := match role with
    | .primary => primary security bits order data source
    | .ordinary => BinaryOrdinaryGroup.current security bits order data.programs source
    | .leg => BinaryLegGroup.current security bits order data.programs data.legFallback data.legEntries source
    | .center => BinarySingletonGroup.current security bits order data.programs .free queue source
    | .queue => BinarySingletonGroup.current security bits order data.programs .queue queue source
  fun arity inputs centers =>
    let result := table arity inputs centers
    ⟨result.value,result.work+1⟩

noncomputable section
open scoped Classical

theorem exists_data (order : ℕ) : ∃ data : Data order, Correct data := by
  obtain ⟨programs,hcorrect,hcomplete⟩ := FixedFamilyPrograms.exists_complete order
  obtain ⟨primaryEntries,primaryOrder,hprimary,hprimaryValid⟩ := BinaryPrimarySelectedCoefficient.exists_entries
  obtain ⟨legEntries,legOrder,hleg,hlegValid⟩ := BinaryLegSelectedCoefficient.exists_entries
  refine ⟨⟨programs,primaryEntries.get 0,primaryEntries,legEntries.get 0,legEntries⟩,
    hcorrect,hcomplete,⟨primaryOrder,hprimary,hprimaryValid⟩,⟨legOrder,hleg,hlegValid⟩⟩

theorem localTable_value (security bits order : ℕ) (data : Data order) (hdata : Correct data)
    (queue : IntegerBits) (role : LocalRole) (source : Vector (Fin (colors security)) 3)
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, inputs.get i<colors security) (hd : ∀ i, centers.get i<colors security) :
    (localTable security bits order data queue role source arity inputs centers).value.decode=
      RationalRootGroupProgram.localTable security bits order queue.decode role
        (fun index => (source.get index).val) arity inputs.get centers.get := by
  rcases hdata with ⟨hcorrect,hcomplete,⟨primaryOrder,hprimary,hprimaryValid⟩,⟨legOrder,hleg,hlegValid⟩⟩
  cases role with
  | primary =>
    simp only [localTable,primary,readVector_value]
    exact BinaryNormalizedPrimary.current_value security bits order data.programs hcorrect hcomplete
      data.primaryFallback data.primaryEntries primaryOrder hprimary hprimaryValid _ _ _ arity inputs centers hc hd
  | ordinary =>
    exact BinaryOrdinaryGroup.current_value security bits order data.programs hcorrect hcomplete source arity inputs centers hc hd
  | leg =>
    exact BinaryLegGroup.current_value security bits order data.programs hcorrect hcomplete data.legFallback data.legEntries
      legOrder hleg hlegValid source arity inputs centers hc hd
  | center =>
    change (BinarySingletonGroup.current security bits order data.programs .free queue source arity inputs centers).value.decode=_
    rw [BinarySingletonGroup.current_value security bits order data.programs hcorrect hcomplete]
    exact BinaryRootSingleton.normalized_point security order _ arity inputs.get centers.get hc hd
  | queue =>
    change (BinarySingletonGroup.current security bits order data.programs .queue queue source arity inputs centers).value.decode=_
    rw [BinarySingletonGroup.current_value security bits order data.programs hcorrect hcomplete]
    exact BinaryRootSingleton.normalized_point security order _ arity inputs.get centers.get hc hd

def heightPolynomial (order : ℕ) (data : Data order) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryNormalizedPrimary.heightPolynomial order data.programs data.primaryEntries precision+
    BinaryOrdinaryGroup.heightPolynomial order data.programs precision+
    BinaryLegGroup.heightPolynomial order data.programs data.legEntries precision+
    BinarySingletonGroup.heightPolynomial order data.programs precision queueBits
def workPolynomial (order : ℕ) (data : Data order) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryNormalizedPrimary.workPolynomial order data.programs data.primaryEntries precision+
    BinaryOrdinaryGroup.workPolynomial order data.programs precision+
    BinaryLegGroup.workPolynomial order data.programs data.legEntries precision+
    BinarySingletonGroup.workPolynomial order data.programs precision queueBits+41

theorem localTable_bounds (security order : ℕ) (data : Data order) (precision queueBits : Polynomial ℕ)
    (queue : IntegerBits) (hq : queue.digits.length ≤ queueBits.eval security) (role : LocalRole) (source : Vector (Fin (colors security)) 3)
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, inputs.get i<colors security) (hd : ∀ i, centers.get i<colors security) :
    HeightBound (localTable security (precision.eval security) order data queue role source arity inputs centers).value.decode
      ((heightPolynomial order data precision queueBits).eval security) ∧
      (localTable security (precision.eval security) order data queue role source arity inputs centers).work ≤
        (workPolynomial order data precision queueBits).eval security := by
  have hp := BinaryNormalizedPrimary.current_bounds security order data.programs data.primaryFallback data.primaryEntries precision
  have ho := BinaryOrdinaryGroup.current_bounds security order data.programs precision source arity inputs centers hc hd
  have hl := BinaryLegGroup.current_bounds security order data.programs data.legFallback data.legEntries precision source arity inputs centers hc hd
  have hs := BinarySingletonGroup.current_bounds security order data.programs precision queueBits
  have hprimary : HeightBound (primary security (precision.eval security) order data source arity inputs centers).value.decode
      ((BinaryNormalizedPrimary.heightPolynomial order data.programs data.primaryEntries precision).eval security) ∧
      (primary security (precision.eval security) order data source arity inputs centers).work ≤
        (BinaryNormalizedPrimary.workPolynomial order data.programs data.primaryEntries precision).eval security+40 := by
    let comp := readVector (BinaryFirstFamily.first security) source 0
    let attach := readVector (BinaryFirstFamily.first security) source 1
    let control := readVector (BinaryFirstFamily.first security) source 2
    have h := hp comp.value attach.value control.value arity inputs centers hc hd
    have wc : comp.work ≤ 12 := readVector_work (BinaryFirstFamily.first security) source 0
    have wa : attach.work ≤ 12 := readVector_work (BinaryFirstFamily.first security) source 1
    have wp : control.work ≤ 12 := readVector_work (BinaryFirstFamily.first security) source 2
    exact ⟨h.1,by
      change comp.work+attach.work+control.work+
        (BinaryNormalizedPrimary.current security (precision.eval security) order data.programs data.primaryFallback data.primaryEntries
          comp.value attach.value control.value arity inputs centers).work+4 ≤ _
      omega⟩
  cases role with
  | primary =>
    exact ⟨hprimary.1.mono (by simp only [heightPolynomial,Polynomial.eval_add]; omega),by
      change (primary security (precision.eval security) order data source arity inputs centers).work+1 ≤ _
      simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_ofNat]; omega⟩
  | ordinary =>
    exact ⟨ho.1.mono (by simp only [heightPolynomial,Polynomial.eval_add]; omega),by
      change (BinaryOrdinaryGroup.current security (precision.eval security) order data.programs source arity inputs centers).work+1 ≤ _
      simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_ofNat]; omega⟩
  | leg =>
    exact ⟨hl.1.mono (by simp only [heightPolynomial,Polynomial.eval_add]; omega),by
      change (BinaryLegGroup.current security (precision.eval security) order data.programs data.legFallback data.legEntries source arity inputs centers).work+1 ≤ _
      simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_ofNat]; omega⟩
  | center =>
    have h := hs .free queue source hq arity inputs centers hc hd
    exact ⟨h.1.mono (by simp only [heightPolynomial,Polynomial.eval_add]; omega),by
      change (BinarySingletonGroup.current security (precision.eval security) order data.programs .free queue source arity inputs centers).work+1 ≤ _
      simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_ofNat]; omega⟩
  | queue =>
    have h := hs .queue queue source hq arity inputs centers hc hd
    exact ⟨h.1.mono (by simp only [heightPolynomial,Polynomial.eval_add]; omega),by
      change (BinarySingletonGroup.current security (precision.eval security) order data.programs .queue queue source arity inputs centers).work+1 ≤ _
      simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_ofNat]; omega⟩

end
end CurrentAFT.BinaryRootGroupProgram
