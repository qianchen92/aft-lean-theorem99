import CurrentAFT.CurrentEmissionMetadata
import CurrentAFT.CurrentPathImpulse

/-! Literal entries of the current physical load matrix, including the shared
queue column. The stored root-order array is read for every physical body root;
scales and shears are read once per leg entry. -/
namespace CurrentAFT.CurrentBinaryLoadColumns
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
open CurrentEmissionMetadata
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current

abbrev Legs (security : ℕ) := (CurrentProposalDimensions.current security).legs
abbrev Body (security : ℕ) := (CurrentProposalDimensions.current security).body
abbrev Point (security : ℕ) := Sigma (blockSlotsProgram (Legs security) (current security).rest)
abbrev Roots (security : ℕ) := Vector (Fin (Body security)) (Body security)


def rootZero (security : ℕ) : Fin (Body security) := ⟨0, by
  change 0 < (CurrentProposalDimensions.current security).body
  rw [(CurrentProposalDimensions.current_values security).2.2.1]
  exact LobsterCoordinates.current_body_positive security⟩

def rootRead (security : ℕ) (roots : Roots security) (point : Fin (Legs security) ⊕ Fin (current security).rest) :
    CountedValue (Fin (Body security)) :=
  let address := binaryRootAddress (Legs security) (current security).rest point
  let selected := readVector (rootZero security) roots (address.value.cast (current_counts security).2.2.1)
  ⟨selected.value, address.work + selected.work + 2⟩

 theorem rootRead_value (security : ℕ) (roots : Roots security) (point : Fin (Legs security) ⊕ Fin (current security).rest) :
    (rootRead security roots point).value = roots.get
      ((blockNumbering (Legs security) (current security).rest point).cast (current_counts security).2.2.1) := by
  simp only [rootRead, readVector_value, binaryRootAddress_value]


def entry (security column : ℕ) (scale shear : Vector IntegerBits (Legs security)) (roots : Roots security) :
    Point security → CountedValue IntegerBits
  | ⟨.inl leg, slot⟩ =>
    let root := rootRead security roots (.inl leg)
    let path := CurrentBinaryIncidence.pathEntry (current security).bodyEdges column root.value.val
    let legValues := CurrentBinaryIncidence.legEntries (current security).bodyEdges column scale shear leg
    let attached := IntegerBits.add path.value legValues.value.2.2
    ⟨![legValues.value.1, legValues.value.2.1, attached.value] slot,
      root.work + path.work + legValues.work + attached.work + 4⟩
  | ⟨.inr body, _⟩ =>
    let root := rootRead security roots (.inr body)
    let path := CurrentBinaryIncidence.pathEntry (current security).bodyEdges column root.value.val
    let center := lessCounter body.val (current security).centers
    let charge := equalCounter column (current security).edges
    let injection := if (!center.value) && charge.value then IntegerBits.one else IntegerBits.zero
    let result := IntegerBits.add path.value injection
    ⟨result.value, root.work + path.work + center.work + charge.work + result.work + 5⟩


def primaryEntry (security column : ℕ) (scale shear : Fin (Legs security) → ℤ) (leg : Fin (Legs security)) : ℤ :=
  (if column = (current security).bodyEdges + leg.val then scale leg else 0) +
    (if column = (current security).bodyEdges + leg.val + Legs security then shear leg else 0)

def secondEntry (security column : ℕ) (leg : Fin (Legs security)) : ℤ :=
  if column = (current security).bodyEdges + leg.val + Legs security then 1 else 0

def pathValue (security column : ℕ) (roots : Roots security) (point : Fin (Legs security) ⊕ Fin (current security).rest) : ℤ :=
  let vertex := roots.get ((blockNumbering (Legs security) (current security).rest point).cast (current_counts security).2.2.1)
  pathLoad (current security).bodyEdges (fun edge => if edge.val = column then 1 else 0)
    (vertex.cast (current_counts security).1.symm)


def loadEntry (security column : ℕ) (scale shear : Fin (Legs security) → ℤ) (roots : Roots security) : Point security → ℤ
  | ⟨.inl leg, slot⟩ => ![primaryEntry security column scale shear leg,
      -primaryEntry security column scale shear leg - secondEntry security column leg,
      pathValue security column roots (.inl leg) + secondEntry security column leg] slot
  | ⟨.inr body, _⟩ => pathValue security column roots (.inr body) +
      if (current security).centers ≤ body.val ∧ column = (current security).edges then 1 else 0

 theorem entry_value (security column : ℕ) (scale shear : Vector IntegerBits (Legs security)) (roots : Roots security)
    (point : Point security) :
    (entry security column scale shear roots point).value.decode =
      loadEntry security column (fun leg => (scale.get leg).decode) (fun leg => (shear.get leg).decode) roots point := by
  rcases point with ⟨leg | body, slot⟩
  · have hv := CurrentBinaryIncidence.legEntries_value (current security).bodyEdges column scale shear leg
    have hfirst := congrArg Prod.fst hv
    have hcompanion := congrArg (fun value => value.2.1) hv
    have hsecond := congrArg (fun value => value.2.2) hv
    dsimp only at hfirst hcompanion hsecond
    have hp := CurrentPathImpulse.pathEntry_basis (current security).bodyEdges column
      ((rootRead security roots (.inl leg)).value.cast (current_counts security).1.symm)
    simp only [Fin.val_cast] at hp
    change Fin 3 at slot
    fin_cases slot <;> simp only [entry, loadEntry, Matrix.cons_val_zero', Matrix.cons_val_succ', IntegerBits.add_value,
      hfirst, hcompanion, hsecond, primaryEntry, secondEntry]
    change (CurrentBinaryIncidence.pathEntry (current security).bodyEdges column (rootRead security roots (.inl leg)).value.val).value.decode + _ = _
    rw [hp]
    simp only [rootRead_value, pathValue]
  · have hp := CurrentPathImpulse.pathEntry_basis (current security).bodyEdges column
      ((rootRead security roots (.inr body)).value.cast (current_counts security).1.symm)
    simp only [Fin.val_cast] at hp
    have hf : (lessCounter body.val (current security).centers).value = false ↔ (current security).centers ≤ body.val := by
      rw [Bool.eq_false_iff]
      exact (not_congr (lessCounter_value _ _)).trans not_lt
    have hc : ((! (lessCounter body.val (current security).centers).value) &&
        (equalCounter column (current security).edges).value) = true ↔
        (current security).centers ≤ body.val ∧ column = (current security).edges := by
      simp only [Bool.and_eq_true, Bool.not_eq_true', hf, equalCounter_value]
    simp only [entry, loadEntry, IntegerBits.add_value]
    rw [hp]
    simp only [rootRead_value, pathValue]
    congr 1
    by_cases h : ((! (lessCounter body.val (current security).centers).value) &&
      (equalCounter column (current security).edges).value) = true
    · rw [if_pos h, if_pos (hc.mp h), IntegerBits.one_value]
    · rw [if_neg h, if_neg (fun hh => h (hc.mpr hh)), IntegerBits.zero_value]


def matrix (security : ℕ) (scale shear : Vector IntegerBits (Legs security)) (roots : Roots security) :
    CountedValue (Vector (Vector IntegerBits ((current security).edges + 1)) ((current security).edges + 1)) :=
  storeData ((current security).edges + 1) (fun column => storeData ((current security).edges + 1) (fun row =>
    let point := binaryPhysicalVertex (Legs security) (current security).rest (current security).edges
      (current_counts security).2.2.2.1 row
    let result := entry security column.val scale shear roots point.value
    ⟨result.value, point.work + result.work + 2⟩))

 theorem matrix_value (security : ℕ) (scale shear : Vector IntegerBits (Legs security)) (roots : Roots security)
    (column row : Fin ((current security).edges + 1)) :
    (((matrix security scale shear roots).value.get column).get row).decode =
      loadEntry security column.val (fun leg => (scale.get leg).decode) (fun leg => (shear.get leg).decode) roots
        ((physicalVertexNumberingProgram (Legs security) (current security).rest (current security).edges
          (current_counts security).2.2.2.1).symm row) := by
  simp only [matrix, storeData_get, entry_value, binaryPhysicalVertex_value]

end CurrentAFT.CurrentBinaryLoadColumns
