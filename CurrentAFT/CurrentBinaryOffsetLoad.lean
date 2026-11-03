import CurrentAFT.CurrentBinaryBaselines

/-! Executed baseline and public cycle-closure load, before the final endpoint
permutation. The same stored leg shift is used in its companion coordinate. -/
namespace CurrentAFT.CurrentBinaryOffsetLoad
open AFT BinaryArithmetic RationalRejectionProgram CurrentEmissionMetadata CurrentCoreProposal
open CurrentBinaryLoadColumns
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current


def closure (bodyEdges root : ℕ) (scalar : IntegerBits) : CountedValue IntegerBits :=
  let last := equalCounter root bodyEdges
  let first := equalCounter root 0
  let positive := if last.value then scalar else IntegerBits.zero
  let negative := if first.value then scalar else IntegerBits.zero
  let result := IntegerBits.subtract positive negative
  ⟨result.value, last.work + first.work + result.work + 4⟩

theorem closure_value (bodyEdges : ℕ) (root : Fin (bodyEdges + 1)) (scalar : IntegerBits) :
    (closure bodyEdges root.val scalar).value.decode = AffineBaseline.closure bodyEdges scalar.decode root := by
  have hl : (equalCounter root.val bodyEdges).value = true ↔ root = Fin.last bodyEdges := by
    rw [equalCounter_value, Fin.ext_iff]
    rfl
  have hf : (equalCounter root.val 0).value = true ↔ root = 0 := by
    rw [equalCounter_value, Fin.ext_iff]
    rfl
  unfold closure AffineBaseline.closure
  dsimp only
  rw [IntegerBits.subtract_value]
  have he (test : Bool) : (if test then scalar else IntegerBits.zero).decode = if test then scalar.decode else 0 := by
    cases test <;> rfl
  rw [he, he]
  simp only [hl, hf]


def entry (security : ℕ) (core : MaterializedCore security) (modulus : IntegerBits)
    (shift intercept : Vector IntegerBits (Legs security)) (roots : Roots security) (scalar : IntegerBits) :
    Point security → CountedValue IntegerBits
  | ⟨.inl leg, slot⟩ =>
    let root := rootRead security roots (.inl leg)
    let closed := closure (current security).bodyEdges root.value.val scalar
    let baseline := CurrentBinaryBaselines.read security core (.inl leg)
    let attached := IntegerBits.add baseline.value closed.value
    let translated := readVector IntegerBits.zero shift leg
    let anchored := readVector IntegerBits.zero intercept leg
    let reduced := IntegerBits.subtract modulus IntegerBits.one
    let shifted := IntegerBits.add reduced.value translated.value
    let companion := IntegerBits.subtract shifted.value anchored.value
    ⟨![anchored.value, companion.value, attached.value] slot,
      root.work + closed.work + baseline.work + attached.work + translated.work + anchored.work +
        reduced.work + shifted.work + companion.work + 9⟩
  | ⟨.inr body, _⟩ =>
    let root := rootRead security roots (.inr body)
    let closed := closure (current security).bodyEdges root.value.val scalar
    let baseline := CurrentBinaryBaselines.read security core (.inr body)
    let result := IntegerBits.add baseline.value closed.value
    ⟨result.value, root.work + closed.work + baseline.work + result.work + 4⟩


def physicalLoad (security : ℕ) (core : MaterializedCore security)
    (layout : ConditionalHistogramMean.RoleIndex security ≃ ActualCycleMeanMGF.BodyIndex security)
    (modulus : ℤ) (shift intercept : Fin (Legs security) → ℤ) (roots : Roots security) (scalar : ℤ) : Point security → ℤ
  | ⟨.inl leg, slot⟩ => ![intercept leg, modulus - 1 + shift leg - intercept leg,
      ActualPublicCharge.centerAt security layout core.core (layout (CurrentBinaryBaselines.role security (.inl leg))) +
        AffineBaseline.closure (current security).bodyEdges scalar
          ((roots.get ((blockNumbering (Legs security) (current security).rest (.inl leg)).cast (current_counts security).2.2.1)).cast
            (current_counts security).1.symm)] slot
  | ⟨.inr body, _⟩ =>
    ActualPublicCharge.centerAt security layout core.core (layout (CurrentBinaryBaselines.role security (.inr body))) +
      AffineBaseline.closure (current security).bodyEdges scalar
        ((roots.get ((blockNumbering (Legs security) (current security).rest (.inr body)).cast (current_counts security).2.2.1)).cast
          (current_counts security).1.symm)

 theorem entry_value (security : ℕ) (core : MaterializedCore security)
    (layout : ConditionalHistogramMean.RoleIndex security ≃ ActualCycleMeanMGF.BodyIndex security)
    (modulus : IntegerBits) (shift intercept : Vector IntegerBits (Legs security)) (roots : Roots security) (scalar : IntegerBits)
    (point : Point security) :
    (entry security core modulus shift intercept roots scalar point).value.decode =
      physicalLoad security core layout modulus.decode (fun leg => (shift.get leg).decode)
        (fun leg => (intercept.get leg).decode) roots scalar.decode point := by
  rcases point with ⟨leg | body, slot⟩
  · have hc := closure_value (current security).bodyEdges
      ((rootRead security roots (.inl leg)).value.cast (current_counts security).1.symm) scalar
    simp only [Fin.val_cast, rootRead_value] at hc
    change Fin 3 at slot
    fin_cases slot <;> simp only [entry, physicalLoad, Matrix.cons_val_zero', Matrix.cons_val_succ',
      IntegerBits.add_value, IntegerBits.subtract_value, IntegerBits.one_value, readVector_value,
      CurrentBinaryBaselines.read_value security core layout, hc, rootRead_value]
  · have hc := closure_value (current security).bodyEdges
      ((rootRead security roots (.inr body)).value.cast (current_counts security).1.symm) scalar
    simp only [Fin.val_cast, rootRead_value] at hc
    simp only [entry, physicalLoad, IntegerBits.add_value,
      CurrentBinaryBaselines.read_value security core layout, hc, rootRead_value]


def load (security : ℕ) (core : MaterializedCore security) (modulus : IntegerBits)
    (shift intercept : Vector IntegerBits (Legs security)) (roots : Roots security) (scalar : IntegerBits) :
    CountedValue (Vector IntegerBits ((current security).edges + 1)) :=
  storeData ((current security).edges + 1) (fun row =>
    let point := binaryPhysicalVertex (Legs security) (current security).rest (current security).edges
      (current_counts security).2.2.2.1 row
    let result := entry security core modulus shift intercept roots scalar point.value
    ⟨result.value, point.work + result.work + 2⟩)

 theorem load_value (security : ℕ) (core : MaterializedCore security)
    (layout : ConditionalHistogramMean.RoleIndex security ≃ ActualCycleMeanMGF.BodyIndex security)
    (modulus : IntegerBits) (shift intercept : Vector IntegerBits (Legs security)) (roots : Roots security) (scalar : IntegerBits)
    (row : Fin ((current security).edges + 1)) :
    ((load security core modulus shift intercept roots scalar).value.get row).decode =
      physicalLoad security core layout modulus.decode (fun leg => (shift.get leg).decode)
        (fun leg => (intercept.get leg).decode) roots scalar.decode
        ((physicalVertexNumberingProgram (Legs security) (current security).rest (current security).edges
          (current_counts security).2.2.2.1).symm row) := by
  simp only [load, storeData_get, entry_value security core layout, binaryPhysicalVertex_value]

end CurrentAFT.CurrentBinaryOffsetLoad
