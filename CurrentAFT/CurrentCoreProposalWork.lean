import CurrentAFT.CurrentCoreProposal

/-! Bit-work bounds for all materialized public-core buffers and both
permutation directions. References to a stored control/leg use readVector. -/
namespace CurrentAFT.CurrentCoreProposalWork
open AFT AFT.BinaryArithmetic AFT.RationalNumerics AFT.RationalRejectionProgram
open CurrentReferenceDraw CurrentProposalDimensions CurrentCoreProposal
set_option maxHeartbeats 1000000
attribute [local irreducible] CurrentProposalDimensions.current CurrentReferenceDraw.counts
  PublicParameterProgram.modulus CurrentPublicSeedDraw.draw CurrentSafeDraw.draw
  CurrentReferenceDraw.primaryDraw CurrentReferenceDraw.bodyDraw


def controlWork (security height bits : ℕ) : ℕ :=
  (PublicParameterProgram.modulus security).work +
    CurrentProbabilityArrayDraw.workBound (PublicParameterProgram.modulus security).count height bits + 1 +
    (CurrentReferenceDraw.counts security).work +
    CurrentProbabilityArrayDraw.workBound (CurrentReferenceDraw.counts security).safe height bits +
      2 * (CurrentReferenceDraw.counts security).margin + 3 + 2

def legWork (security height bits : ℕ) : ℕ :=
  CurrentPublicSeedDraw.workBound security height bits + CurrentSafeDraw.workBound security bits + 2

theorem controlDraw_work (security tableBits bits height : ℕ) (cache : Cache security tableBits)
    (hp : ∀ index, HeightBound (cache.primary.data.get index).decode height)
    (hb : ∀ index, HeightBound (cache.body.data.get index).decode height)
    (word : ControlTape security bits) :
    (controlDraw security tableBits bits cache word).work ≤ controlWork security height bits := by
  have hfirst := primaryDraw_work security tableBits bits height cache hp word.1
  have hsecond := bodyDraw_work security tableBits bits height cache hb word.2
  change (CurrentReferenceDraw.primaryDraw security tableBits bits cache word.1).work +
    (CurrentReferenceDraw.bodyDraw security tableBits bits cache word.2).work + 2 ≤ _
  unfold controlWork
  omega

theorem legDraw_work (security tableBits bits height : ℕ) (cache : Cache security tableBits)
    (ha : HeightBound cache.activation.decode height) (word : LegTape security bits) :
    (legDraw security tableBits bits cache word).work ≤ legWork security height bits := by
  have hs := CurrentPublicSeedDraw.draw_work security tableBits bits height cache ha word.1
  have hb := CurrentSafeDraw.draw_work security bits word.2
  change (CurrentPublicSeedDraw.draw security tableBits bits cache word.1).work +
    (CurrentSafeDraw.draw security bits word.2).work + 2 ≤ _
  unfold legWork
  omega

def gatherWork (security : ℕ) : ℕ := (current security).work +
  (current security).legs * (3 * (current security).controls + 3 * (current security).legs + 10) + 4

theorem gatherInputs_work (security : ℕ) (controls : Controls security) (legs : Legs security) :
    (gatherInputs security controls legs).work ≤ gatherWork security := by
  let term := fun index : Fin (current security).legs =>
    let address := (controlsEquiv security).symm (.inl (legEquiv security index))
    let control := readVector (defaultControl security) controls address
    let leg := readVector (defaultLeg security) legs index
    (⟨(control.value.1, leg.value.1), control.work + leg.work + 2⟩ : CountedValue (CurrentChartsDraw.Input security))
  have ht (index) : (term index).work ≤ 3 * (current security).controls + 3 * (current security).legs + 8 := by
    have hc := readVector_work (defaultControl security) controls
      ((controlsEquiv security).symm (.inl (legEquiv security index)))
    have hl := readVector_work (defaultLeg security) legs index
    change (readVector _ controls _).work + (readVector _ legs _).work + 2 ≤ _
    omega
  have hs := storeData_work (current security).legs
    (3 * (current security).controls + 3 * (current security).legs + 8) term ht
  change (current security).work + (storeData (current security).legs term).work + 2 ≤ _
  unfold gatherWork
  norm_num only [Nat.add_assoc] at hs ⊢
  omega

def workBound (security height bits : ℕ) : ℕ :=
  (current security).work +
    ((current security).controls * (CurrentPublicIndexProgram.workBound security + controlWork security height bits + 4) + 2) +
    ((current security).legs * (legWork security height bits + 2) + 2) +
    ((current security).colors * (CurrentSafeDraw.workBound security bits + 2) + 2) +
    CurrentPermutationDraw.workBound (current security).body bits +
    CurrentPermutationDraw.workBound (current security).dimension bits + gatherWork security +
    (current security).body * bits + (current security).dimension * bits + 9

theorem draw_work (security tableBits bits height : ℕ) (cache : Cache security tableBits)
    (hp : ∀ index, HeightBound (cache.primary.data.get index).decode height)
    (hb : ∀ index, HeightBound (cache.body.data.get index).decode height)
    (ha : HeightBound cache.activation.decode height) (word : Tapes security bits) :
    (draw security tableBits bits cache word).work ≤ workBound security height bits := by
  let controlTerm := fun index : Fin (current security).controls =>
    let address := CurrentPublicIndexProgram.decode security index
    let result := controlDraw security tableBits bits cache (word.1.1.1.1 address.value)
    (⟨result.value, address.work + result.work + 2⟩ : CountedValue (SafeControlGroups.SafeGroup security))
  let controls := storeData (current security).controls controlTerm
  let legTerm := fun index : Fin (current security).legs =>
    legDraw security tableBits bits cache (word.1.1.1.2 (legEquiv security index))
  let legs := storeData (current security).legs legTerm
  let queueTerm := fun index : Fin (current security).colors =>
    CurrentSafeDraw.draw security bits (word.1.1.2 (queueEquiv security index))
  let baselines := storeData (current security).colors queueTerm
  let body := CurrentPermutationDraw.draw (current security).body bits (Vector.ofFn word.1.2)
  let endpoints := CurrentPermutationDraw.draw (current security).dimension bits (Vector.ofFn word.2)
  let inputs := gatherInputs security controls.value legs.value
  have hct (index) : (controlTerm index).work ≤ CurrentPublicIndexProgram.workBound security + controlWork security height bits + 2 := by
    have hi := CurrentPublicIndexProgram.decode_work security index
    have hc := controlDraw_work security tableBits bits height cache hp hb
      (word.1.1.1.1 (CurrentPublicIndexProgram.decode security index).value)
    change (CurrentPublicIndexProgram.decode security index).work +
      (controlDraw security tableBits bits cache _).work + 2 ≤ _
    omega
  have hc := storeData_work (current security).controls
    (CurrentPublicIndexProgram.workBound security + controlWork security height bits + 2) controlTerm hct
  have hl := storeData_work (current security).legs (legWork security height bits) legTerm
    (fun index => legDraw_work security tableBits bits height cache ha _)
  have hq := storeData_work (current security).colors (CurrentSafeDraw.workBound security bits) queueTerm
    (fun index => CurrentSafeDraw.draw_work security bits _)
  have hbody := CurrentPermutationDraw.draw_work (current security).body bits (Vector.ofFn word.1.2)
  have hendpoints := CurrentPermutationDraw.draw_work (current security).dimension bits (Vector.ofFn word.2)
  have hi := gatherInputs_work security controls.value legs.value
  change (current security).work + controls.work + legs.work + baselines.work + body.work + endpoints.work + inputs.work +
    (current security).body * bits + (current security).dimension * bits + 9 ≤ _
  change controls.work ≤ _ at hc
  change legs.work ≤ _ at hl
  change baselines.work ≤ _ at hq
  change body.work ≤ _ at hbody
  change endpoints.work ≤ _ at hendpoints
  change inputs.work ≤ _ at hi
  unfold workBound
  norm_num only [Nat.add_assoc] at hc hl hq hbody hendpoints hi ⊢
  omega

end CurrentAFT.CurrentCoreProposalWork
