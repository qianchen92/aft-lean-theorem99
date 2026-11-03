import CurrentAFT.CurrentBinaryOffsetLoad
import CurrentAFT.CurrentBinaryBaselineResources
import CurrentAFT.CurrentBinaryLoadResources

/-! Bit lengths and work of actual offset-load production. -/
namespace CurrentAFT.CurrentBinaryOffsetResources
open AFT BinaryArithmetic RationalRejectionProgram CurrentEmissionMetadata
open CurrentBinaryLoadColumns CurrentBinaryOffsetLoad
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current

 theorem closure_length (bodyEdges root bits : ℕ) (scalar : IntegerBits) (hs : scalar.digits.length ≤ bits) :
    (closure bodyEdges root scalar).value.digits.length ≤ bits + 1 := by
  have hp : (if (equalCounter root bodyEdges).value then scalar else IntegerBits.zero).digits.length ≤ bits := by
    split_ifs; exact hs; exact Nat.zero_le _
  have hn : (if (equalCounter root 0).value then scalar else IntegerBits.zero).digits.length ≤ bits := by
    split_ifs; exact hs; exact Nat.zero_le _
  exact (IntegerBits.subtract_length _ _).trans (by omega)

 theorem closure_work (bodyEdges root bits : ℕ) (scalar : IntegerBits) (hs : scalar.digits.length ≤ bits) :
    (closure bodyEdges root scalar).work ≤ 6 * root + 3 * bodyEdges + 20 * bits + 30 := by
  have hp : (if (equalCounter root bodyEdges).value then scalar else IntegerBits.zero).digits.length ≤ bits := by
    split_ifs; exact hs; exact Nat.zero_le _
  have hn : (if (equalCounter root 0).value then scalar else IntegerBits.zero).digits.length ≤ bits := by
    split_ifs; exact hs; exact Nat.zero_le _
  have hl := equalCounter_work root bodyEdges
  have hf := equalCounter_work root 0
  have hsub := IntegerBits.subtract_work
    (if (equalCounter root bodyEdges).value then scalar else IntegerBits.zero)
    (if (equalCounter root 0).value then scalar else IntegerBits.zero)
  change (equalCounter root bodyEdges).work + (equalCounter root 0).work + (IntegerBits.subtract _ _).work + 4 ≤ _
  omega

 theorem entry_length (security bits : ℕ) (hbits : 1 ≤ bits) (hq : Parameters.modulus security ≤ bits)
    (core : CurrentCoreProposal.MaterializedCore security) (modulus : IntegerBits) (shift intercept : Vector IntegerBits (Legs security))
    (roots : Roots security) (scalar : IntegerBits) (hm : modulus.digits.length ≤ bits)
    (hs : ∀ leg, (shift.get leg).digits.length ≤ bits) (hi : ∀ leg, (intercept.get leg).digits.length ≤ bits)
    (hc : scalar.digits.length ≤ bits) (point : Point security) :
    (CurrentBinaryOffsetLoad.entry security core modulus shift intercept roots scalar point).value.digits.length ≤ bits + 3 := by
  rcases point with ⟨leg | body, slot⟩
  · have hclosed := closure_length (current security).bodyEdges (rootRead security roots (.inl leg)).value.val bits scalar hc
    have hbase := (CurrentBinaryBaselineResources.read_length security core (.inl leg)).trans hq
    have ha := IntegerBits.add_length (CurrentBinaryBaselines.read security core (.inl leg)).value
      (closure (current security).bodyEdges (rootRead security roots (.inl leg)).value.val scalar).value
    have hr := IntegerBits.subtract_length modulus IntegerBits.one
    have hsh := IntegerBits.add_length (IntegerBits.subtract modulus IntegerBits.one).value (shift.get leg)
    have hcomp := IntegerBits.subtract_length
      (IntegerBits.add (IntegerBits.subtract modulus IntegerBits.one).value (shift.get leg)).value (intercept.get leg)
    have hsl := hs leg
    have hil := hi leg
    change Fin 3 at slot
    fin_cases slot <;> simp only [CurrentBinaryOffsetLoad.entry, Matrix.cons_val_zero', Matrix.cons_val_succ', readVector_value] <;>
      change _ ≤ bits + 3 <;> simp only [show IntegerBits.one.digits.length = 1 from rfl] at hr <;> omega
  · have hclosed := closure_length (current security).bodyEdges (rootRead security roots (.inr body)).value.val bits scalar hc
    have hbase := (CurrentBinaryBaselineResources.read_length security core (.inr body)).trans hq
    have ha := IntegerBits.add_length (CurrentBinaryBaselines.read security core (.inr body)).value
      (closure (current security).bodyEdges (rootRead security roots (.inr body)).value.val scalar).value
    change (IntegerBits.add _ _).value.digits.length ≤ _
    omega


def entryWork (security bits : ℕ) : ℕ :=
  CurrentBinaryBaselineResources.readWork security + 100 * (Body security + Legs security + (current security).bodyEdges + bits + 10)

 theorem entry_work (security bits : ℕ) (_hbits : 1 ≤ bits)
    (core : CurrentCoreProposal.MaterializedCore security) (modulus : IntegerBits) (shift intercept : Vector IntegerBits (Legs security))
    (roots : Roots security) (scalar : IntegerBits) (hm : modulus.digits.length ≤ bits)
    (hs : ∀ leg, (shift.get leg).digits.length ≤ bits) (hi : ∀ leg, (intercept.get leg).digits.length ≤ bits)
    (hc : scalar.digits.length ≤ bits) (point : Point security) :
    (CurrentBinaryOffsetLoad.entry security core modulus shift intercept roots scalar point).work ≤ entryWork security bits := by
  rcases point with ⟨leg | body, slot⟩
  · have hroot := CurrentBinaryLoadResources.rootRead_work security roots (.inl leg)
    have hcl := closure_work (current security).bodyEdges (rootRead security roots (.inl leg)).value.val bits scalar hc
    have hcls := closure_length (current security).bodyEdges (rootRead security roots (.inl leg)).value.val bits scalar hc
    have hb := CurrentBinaryBaselineResources.read_work security core (.inl leg)
    have hbl := CurrentBinaryBaselineResources.read_length security core (.inl leg)
    have ha := IntegerBits.add_work (CurrentBinaryBaselines.read security core (.inl leg)).value
      (closure (current security).bodyEdges (rootRead security roots (.inl leg)).value.val scalar).value
    have hq := (CurrentProposalDimensions.current_values security).1
    have hbase : Parameters.modulus security ≤ Body security := by
      change Parameters.modulus security ≤ (CurrentProposalDimensions.current security).body
      rw [(CurrentProposalDimensions.current_values security).2.2.1]
      have h := ProposalPrimary.population_room security
      omega
    have ht := readVector_work IntegerBits.zero shift leg
    have hij := readVector_work IntegerBits.zero intercept leg
    have hr := IntegerBits.subtract_work modulus IntegerBits.one
    have hrl := IntegerBits.subtract_length modulus IntegerBits.one
    have hsh := IntegerBits.add_work (IntegerBits.subtract modulus IntegerBits.one).value (shift.get leg)
    have hshl := IntegerBits.add_length (IntegerBits.subtract modulus IntegerBits.one).value (shift.get leg)
    have hcomp := IntegerBits.subtract_work
      (IntegerBits.add (IntegerBits.subtract modulus IntegerBits.one).value (shift.get leg)).value (intercept.get leg)
    have hsl := hs leg
    have hil := hi leg
    have hv := (rootRead security roots (.inl leg)).value.isLt
    change (rootRead _ _ _).work + (closure _ _ _).work + (CurrentBinaryBaselines.read _ _ _).work +
      (IntegerBits.add _ _).work + (readVector _ shift leg).work + (readVector _ intercept leg).work +
      (IntegerBits.subtract modulus _).work + (IntegerBits.add _ _).work + (IntegerBits.subtract _ _).work + 9 ≤ _
    simp only [readVector_value]
    simp only [show IntegerBits.one.digits.length = 1 from rfl] at hr hrl
    unfold entryWork
    omega
  · have hroot := CurrentBinaryLoadResources.rootRead_work security roots (.inr body)
    have hcl := closure_work (current security).bodyEdges (rootRead security roots (.inr body)).value.val bits scalar hc
    have hcls := closure_length (current security).bodyEdges (rootRead security roots (.inr body)).value.val bits scalar hc
    have hb := CurrentBinaryBaselineResources.read_work security core (.inr body)
    have hbl := CurrentBinaryBaselineResources.read_length security core (.inr body)
    have ha := IntegerBits.add_work (CurrentBinaryBaselines.read security core (.inr body)).value
      (closure (current security).bodyEdges (rootRead security roots (.inr body)).value.val scalar).value
    have hbase : Parameters.modulus security ≤ Body security := by
      change Parameters.modulus security ≤ (CurrentProposalDimensions.current security).body
      rw [(CurrentProposalDimensions.current_values security).2.2.1]
      have h := ProposalPrimary.population_room security
      omega
    have hv := (rootRead security roots (.inr body)).value.isLt
    change (rootRead _ _ _).work + (closure _ _ _).work + (CurrentBinaryBaselines.read _ _ _).work + (IntegerBits.add _ _).work + 4 ≤ _
    unfold entryWork
    omega

 theorem load_length (security bits : ℕ) (hbits : 1 ≤ bits) (hq : Parameters.modulus security ≤ bits)
    (core : CurrentCoreProposal.MaterializedCore security) (modulus : IntegerBits)
    (shift intercept : Vector IntegerBits (Legs security)) (roots : Roots security) (scalar : IntegerBits)
    (hm : modulus.digits.length ≤ bits) (hs : ∀ leg, (shift.get leg).digits.length ≤ bits)
    (hi : ∀ leg, (intercept.get leg).digits.length ≤ bits) (hc : scalar.digits.length ≤ bits)
    (row : Fin ((current security).edges + 1)) :
    ((CurrentBinaryOffsetLoad.load security core modulus shift intercept roots scalar).value.get row).digits.length ≤ bits + 3 := by
  simp only [CurrentBinaryOffsetLoad.load, storeData_get]
  exact entry_length security bits hbits hq core modulus shift intercept roots scalar hm hs hi hc _


def loadWork (security bits : ℕ) : ℕ :=
  let size := (current security).edges + 1
  size * (1000 * (size + 6)^2 + entryWork security bits + 4) + 2

 theorem load_work (security bits : ℕ) (hbits : 1 ≤ bits)
    (core : CurrentCoreProposal.MaterializedCore security) (modulus : IntegerBits)
    (shift intercept : Vector IntegerBits (Legs security)) (roots : Roots security) (scalar : IntegerBits)
    (hm : modulus.digits.length ≤ bits) (hs : ∀ leg, (shift.get leg).digits.length ≤ bits)
    (hi : ∀ leg, (intercept.get leg).digits.length ≤ bits) (hc : scalar.digits.length ≤ bits) :
    (CurrentBinaryOffsetLoad.load security core modulus shift intercept roots scalar).work ≤ loadWork security bits := by
  apply storeData_work
  intro row
  have hv := binaryVertexCode_work (Legs security) (current security).rest (row.cast (current_counts security).2.2.2.1.symm)
  have he := entry_work security bits hbits core modulus shift intercept roots scalar hm hs hi hc
    (binaryPhysicalVertex (Legs security) (current security).rest (current security).edges (current_counts security).2.2.2.1 row).value
  have hcount : Legs security * 3 + (current security).rest = (current security).edges + 1 := (current_counts security).2.2.2.1
  have hp : 1000 * (Legs security * 3 + (current security).rest + 6)^2 = 1000 * ((current security).edges + 1 + 6)^2 := by rw [hcount]
  change (binaryPhysicalVertex (Legs security) (current security).rest (current security).edges (current_counts security).2.2.2.1 row).work ≤ _ at hv
  change (binaryPhysicalVertex _ _ _ _ row).work + (CurrentBinaryOffsetLoad.entry security core modulus shift intercept roots scalar _).work + 2 ≤ _
  omega

end CurrentAFT.CurrentBinaryOffsetResources
