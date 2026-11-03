import CurrentAFT.CurrentBinaryLoadColumns

/-! Bit length and work of the current executed physical load matrix. -/
namespace CurrentAFT.CurrentBinaryLoadResources
open AFT BinaryArithmetic RationalRejectionProgram CurrentEmissionMetadata CurrentBinaryLoadColumns
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current

theorem rootRead_work (security : ℕ) (roots : Roots security) (point : Fin (Legs security) ⊕ Fin (current security).rest) :
    (rootRead security roots point).work ≤ 2 * Legs security + 3 * Body security + 8 := by
  have ha := binaryRootAddress_work (Legs security) (current security).rest point
  have hr := readVector_work (rootZero security) roots ((binaryRootAddress (Legs security) (current security).rest point).value.cast (current_counts security).2.2.1)
  change (binaryRootAddress _ _ point).work + (readVector _ roots _).work + 2 ≤ _
  omega

 theorem entry_length (security column bits : ℕ) (hbits : 1 ≤ bits)
    (scale shear : Vector IntegerBits (Legs security)) (roots : Roots security)
    (hs : ∀ leg, (scale.get leg).digits.length ≤ bits) (hh : ∀ leg, (shear.get leg).digits.length ≤ bits)
    (point : Point security) : (entry security column scale shear roots point).value.digits.length ≤ bits + 3 := by
  rcases point with ⟨leg | body, slot⟩
  · have hl := CurrentBinaryIncidence.legEntries_length (current security).bodyEdges column bits scale shear leg (hs leg) (hh leg)
    have hp := CurrentBinaryIncidence.pathEntry_length (current security).bodyEdges column (rootRead security roots (.inl leg)).value.val
    have ha := IntegerBits.add_length
      (CurrentBinaryIncidence.pathEntry (current security).bodyEdges column (rootRead security roots (.inl leg)).value.val).value
      (CurrentBinaryIncidence.legEntries (current security).bodyEdges column scale shear leg).value.2.2
    change Fin 3 at slot
    fin_cases slot <;> simp only [entry, Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> omega
  · have hp := CurrentBinaryIncidence.pathEntry_length (current security).bodyEdges column (rootRead security roots (.inr body)).value.val
    let indicator := if (!(lessCounter body.val (current security).centers).value) && (equalCounter column (current security).edges).value then IntegerBits.one else IntegerBits.zero
    have hi : indicator.digits.length ≤ 1 := by dsimp only [indicator]; split_ifs <;> decide
    have ha := IntegerBits.add_length
      (CurrentBinaryIncidence.pathEntry (current security).bodyEdges column (rootRead security roots (.inr body)).value.val).value indicator
    change (IntegerBits.add _ indicator).value.digits.length ≤ _
    omega


def entryWork (security column bits : ℕ) : ℕ := 100 * ((current security).bodyEdges + Legs security + Body security +
    (current security).edges + (current security).rest + column + bits + 10)

 theorem entry_work (security column bits : ℕ)
    (scale shear : Vector IntegerBits (Legs security)) (roots : Roots security)
    (hs : ∀ leg, (scale.get leg).digits.length ≤ bits) (hh : ∀ leg, (shear.get leg).digits.length ≤ bits)
    (point : Point security) : (entry security column scale shear roots point).work ≤ entryWork security column bits := by
  rcases point with ⟨leg | body, slot⟩
  · have hr := rootRead_work security roots (.inl leg)
    have hp := CurrentBinaryIncidence.pathEntry_work (current security).bodyEdges column (rootRead security roots (.inl leg)).value.val
    have hl := CurrentBinaryIncidence.legEntries_work (current security).bodyEdges column bits scale shear leg (hs leg) (hh leg)
    have hd := CurrentBinaryIncidence.pathEntry_length (current security).bodyEdges column (rootRead security roots (.inl leg)).value.val
    have hi := (CurrentBinaryIncidence.legEntries_length (current security).bodyEdges column bits scale shear leg (hs leg) (hh leg)).2.2
    have ha := IntegerBits.add_work
      (CurrentBinaryIncidence.pathEntry (current security).bodyEdges column (rootRead security roots (.inl leg)).value.val).value
      (CurrentBinaryIncidence.legEntries (current security).bodyEdges column scale shear leg).value.2.2
    have hroot := (rootRead security roots (.inl leg)).value.isLt
    change (rootRead _ _ _).work + (CurrentBinaryIncidence.pathEntry _ _ _).work + (CurrentBinaryIncidence.legEntries _ _ _ _ _).work + (IntegerBits.add _ _).work + 4 ≤ _
    unfold CurrentBinaryIncidence.pathEntryWork CurrentBinaryIncidence.legEntriesWork entryWork at *
    omega
  · have hr := rootRead_work security roots (.inr body)
    have hp := CurrentBinaryIncidence.pathEntry_work (current security).bodyEdges column (rootRead security roots (.inr body)).value.val
    have hd := CurrentBinaryIncidence.pathEntry_length (current security).bodyEdges column (rootRead security roots (.inr body)).value.val
    have hc := lessCounter_work_left body.val (current security).centers
    have hq := equalCounter_work column (current security).edges
    let indicator := if (!(lessCounter body.val (current security).centers).value) && (equalCounter column (current security).edges).value then IntegerBits.one else IntegerBits.zero
    have hi : indicator.digits.length ≤ 1 := by dsimp only [indicator]; split_ifs <;> decide
    have ha := IntegerBits.add_work
      (CurrentBinaryIncidence.pathEntry (current security).bodyEdges column (rootRead security roots (.inr body)).value.val).value indicator
    have hroot := (rootRead security roots (.inr body)).value.isLt
    have hb := body.isLt
    change (rootRead _ _ _).work + (CurrentBinaryIncidence.pathEntry _ _ _).work + (lessCounter _ _).work + (equalCounter _ _).work + (IntegerBits.add _ indicator).work + 5 ≤ _
    unfold CurrentBinaryIncidence.pathEntryWork entryWork at *
    omega

 theorem matrix_length (security bits : ℕ) (hbits : 1 ≤ bits)
    (scale shear : Vector IntegerBits (Legs security)) (roots : Roots security)
    (hs : ∀ leg, (scale.get leg).digits.length ≤ bits) (hh : ∀ leg, (shear.get leg).digits.length ≤ bits)
    (column row : Fin ((current security).edges + 1)) :
    (((matrix security scale shear roots).value.get column).get row).digits.length ≤ bits + 3 := by
  simp only [matrix, storeData_get]
  exact entry_length security column.val bits hbits scale shear roots hs hh _


def matrixWork (security bits : ℕ) : ℕ :=
  let size := (current security).edges + 1
  size * (size * (1000 * (size + 6)^2 + entryWork security size bits + 4) + 4) + 2

 theorem matrix_work (security bits : ℕ)
    (scale shear : Vector IntegerBits (Legs security)) (roots : Roots security)
    (hs : ∀ leg, (scale.get leg).digits.length ≤ bits) (hh : ∀ leg, (shear.get leg).digits.length ≤ bits) :
    (matrix security scale shear roots).work ≤ matrixWork security bits := by
  apply storeData_work
  intro column
  apply storeData_work
  intro row
  have hv := binaryVertexCode_work (Legs security) (current security).rest (row.cast (current_counts security).2.2.2.1.symm)
  have he := entry_work security column.val bits scale shear roots hs hh
    (binaryPhysicalVertex (Legs security) (current security).rest (current security).edges (current_counts security).2.2.2.1 row).value
  have hc : Legs security * 3 + (current security).rest = (current security).edges + 1 := (current_counts security).2.2.2.1
  have hp : 1000 * (Legs security * 3 + (current security).rest + 6)^2 = 1000 * ((current security).edges + 1 + 6)^2 := by rw [hc]
  have hm : entryWork security column.val bits ≤ entryWork security ((current security).edges + 1) bits := by
    unfold entryWork
    have hcol := column.isLt
    omega
  change (binaryPhysicalVertex _ _ _ _ row).work + (entry security column.val scale shear roots _).work + 2 ≤ _
  change (binaryPhysicalVertex (Legs security) (current security).rest (current security).edges (current_counts security).2.2.2.1 row).work ≤ _ at hv
  omega

end CurrentAFT.CurrentBinaryLoadResources
