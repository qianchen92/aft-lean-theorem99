import CurrentAFT.CurrentPublicSeedDraw
import CurrentAFT.CurrentSafeDraw
import CurrentAFT.CurrentProposalDimensions
import CurrentAFT.CurrentPublicIndexProgram
import CurrentAFT.CurrentPermutationCache
import CurrentAFT.CurrentPublicCompletion

/-! Literal public proposal buffers. Controls, leg seeds and queue baselines
are materialized sequentially, as are both directions of the two public
permutations. The extra chart-input vector is gathered by charged array reads.
Every input tape is public and independent of the hidden Gaussian source. -/
namespace CurrentAFT.CurrentCoreProposal
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
open ActualPublicCharge CurrentReferenceDraw CurrentProposalDimensions
open scoped BigOperators
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
attribute [local irreducible] Parameters.legCount Parameters.dimension Parameters.bodySize
  CurrentPublicSeedDraw.draw CurrentSafeDraw.draw CurrentReferenceDraw.primaryDraw CurrentReferenceDraw.bodyDraw

abbrev ControlTape (security bits : ℕ) :=
  (Fin (bits + (PublicParameterProgram.modulus security).count + 1) → Fin 2) ×
    (Fin (bits + (CurrentReferenceDraw.counts security).safe + 1) → Fin 2)
abbrev LegTape (security bits : ℕ) := CurrentPublicSeedDraw.Tape security bits × CurrentSafeDraw.Tape security bits
abbrev Tapes (security bits : ℕ) :=
  ((((PublicOutputExperiment.PublicIndex security → ControlTape security bits) ×
      (Fin (Parameters.legCount security) → LegTape security bits)) ×
    (Fin (Parameters.modulus security) → CurrentSafeDraw.Tape security bits)) ×
      (Fin ((current security).body * bits) → Fin 2)) ×
      (Fin ((current security).dimension * bits) → Fin 2)

def controlDraw (security tableBits bits : ℕ) (cache : Cache security tableBits) (word : ControlTape security bits) :
    CountedValue (SafeControlGroups.SafeGroup security) :=
  let primary := CurrentReferenceDraw.primaryDraw security tableBits bits cache word.1
  let body := CurrentReferenceDraw.bodyDraw security tableBits bits cache word.2
  ⟨(primary.value, body.value), primary.work + body.work + 2⟩

def legDraw (security tableBits bits : ℕ) (cache : Cache security tableBits) (word : LegTape security bits) :
    CountedValue (LegCore security) :=
  let seed := CurrentPublicSeedDraw.draw security tableBits bits cache word.1
  let baseline := CurrentSafeDraw.draw security bits word.2
  ⟨(seed.value, baseline.value), seed.work + baseline.work + 2⟩

abbrev Controls (security : ℕ) := Vector (SafeControlGroups.SafeGroup security) (current security).controls
abbrev Legs (security : ℕ) := Vector (LegCore security) (current security).legs
abbrev Baselines (security : ℕ) := Vector (FirstHistogram.Palette security) (current security).colors

def decode (security : ℕ) (controls : Controls security) (legs : Legs security) (baselines : Baselines security)
    (body : CurrentPermutationDraw.CachedPermutation (current security).body)
    (endpoints : CurrentPermutationDraw.CachedPermutation (current security).dimension) : Core security where
  controls index := controls.get ((controlsEquiv security).symm index)
  legs index := legs.get ((legEquiv security).symm index)
  queueBaselines index := baselines.get ((queueEquiv security).symm index)
  bodyPermutation := (CurrentProposalDimensions.bodyEquiv security).permCongr body.toEquiv
  endpointPermutation := (endpointEquiv security).permCongr endpoints.toEquiv

def defaultControl (security : ℕ) : SafeControlGroups.SafeGroup security :=
  (⟨0, (Parameters.modulus_spec security).2.pos⟩,
    CurrentSafePaletteIndex.equiv security ⟨0, CurrentSafePaletteIndex.count_positive security⟩)

def defaultLeg (security : ℕ) : LegCore security :=
  ((CurrentChartsDraw.defaultInput security).2, (defaultControl security).1)

def gatherInputs (security : ℕ) (controls : Controls security) (legs : Legs security) :
    CountedValue (CurrentChartsDraw.InputVector security) :=
  let data := storeData (current security).legs (fun index =>
    let address := (controlsEquiv security).symm (.inl (legEquiv security index))
    let control := readVector (defaultControl security) controls address
    let leg := readVector (defaultLeg security) legs index
    ⟨(control.value.1, leg.value.1), control.work + leg.work + 2⟩)
  ⟨data.value.cast (current_values security).2.1, (current security).work + data.work + 2⟩

theorem gatherInputs_value (security : ℕ) (controls : Controls security) (legs : Legs security)
    (index : Fin (Parameters.legCount security)) :
    (gatherInputs security controls legs).value.get index =
      ((controls.get ((controlsEquiv security).symm (.inl index))).1,
        (legs.get ((legEquiv security).symm index)).1) := by
  simp only [gatherInputs, Vector.get_cast, storeData_get, readVector_value]
  rfl

structure MaterializedCore (security : ℕ) where
  controls : Controls security
  legs : Legs security
  baselines : Baselines security
  body : CurrentPermutationDraw.CachedPermutation (current security).body
  endpoints : CurrentPermutationDraw.CachedPermutation (current security).dimension
  inputs : CurrentChartsDraw.InputVector security
  inputs_correct : ∀ index, inputs.get index =
    ((controls.get ((controlsEquiv security).symm (.inl index))).1,
      (legs.get ((legEquiv security).symm index)).1)

def MaterializedCore.core {security : ℕ} (data : MaterializedCore security) : Core security :=
  decode security data.controls data.legs data.baselines data.body data.endpoints

def MaterializedCore.cached {security : ℕ} (data : MaterializedCore security) : CurrentPublicCompletion.CachedCore security :=
  ⟨data.core, data.inputs, by
    apply Vector.ext
    intro index hindex
    change data.inputs.get ⟨index, hindex⟩ = _
    rw [data.inputs_correct]
    simp only [CurrentChartsDraw.inputsOfCore, Vector.getElem_ofFn, MaterializedCore.core, decode]⟩

def draw (security tableBits bits : ℕ) (cache : Cache security tableBits) (word : Tapes security bits) :
    CountedValue (MaterializedCore security) :=
  let controls := storeData (current security).controls (fun index =>
    let address := CurrentPublicIndexProgram.decode security index
    let result := controlDraw security tableBits bits cache (word.1.1.1.1 address.value)
    ⟨result.value, address.work + result.work + 2⟩)
  let legs := storeData (current security).legs (fun index =>
    legDraw security tableBits bits cache (word.1.1.1.2 (legEquiv security index)))
  let baselines := storeData (current security).colors (fun index =>
    CurrentSafeDraw.draw security bits (word.1.1.2 (queueEquiv security index)))
  let body := CurrentPermutationDraw.draw (current security).body bits (Vector.ofFn word.1.2)
  let endpoints := CurrentPermutationDraw.draw (current security).dimension bits (Vector.ofFn word.2)
  let inputs := gatherInputs security controls.value legs.value
  ⟨⟨controls.value, legs.value, baselines.value, body.value, endpoints.value, inputs.value,
      gatherInputs_value security controls.value legs.value⟩,
    (current security).work + controls.work + legs.work + baselines.work + body.work + endpoints.work + inputs.work +
      (current security).body * bits + (current security).dimension * bits + 9⟩

theorem draw_controls (security tableBits bits : ℕ) (cache : Cache security tableBits)
    (word : Tapes security bits) (index : PublicOutputExperiment.PublicIndex security) :
    ((draw security tableBits bits cache word).value.core).controls index =
      (controlDraw security tableBits bits cache (word.1.1.1.1 index)).value := by
  simp only [draw, MaterializedCore.core, decode, storeData_get, CurrentPublicIndexProgram.decode_value, Equiv.apply_symm_apply]

theorem draw_legs (security tableBits bits : ℕ) (cache : Cache security tableBits)
    (word : Tapes security bits) (index : Fin (Parameters.legCount security)) :
    ((draw security tableBits bits cache word).value.core).legs index =
      (legDraw security tableBits bits cache (word.1.1.1.2 index)).value := by
  simp only [draw, MaterializedCore.core, decode, storeData_get, CurrentPublicIndexProgram.decode_value, Equiv.apply_symm_apply]

theorem draw_baselines (security tableBits bits : ℕ) (cache : Cache security tableBits)
    (word : Tapes security bits) (index : Fin (Parameters.modulus security)) :
    ((draw security tableBits bits cache word).value.core).queueBaselines index =
      (CurrentSafeDraw.draw security bits (word.1.1.2 index)).value := by
  simp only [draw, MaterializedCore.core, decode, storeData_get, CurrentPublicIndexProgram.decode_value, Equiv.apply_symm_apply]

theorem draw_body (security tableBits bits : ℕ) (cache : Cache security tableBits) (word : Tapes security bits) :
    ((draw security tableBits bits cache word).value.core).bodyPermutation =
      (CurrentProposalDimensions.bodyEquiv security).permCongr (PermutationProgram.draw (current security).body bits word.1.2) := by
  change (CurrentProposalDimensions.bodyEquiv security).permCongr ((CurrentPermutationDraw.draw _ _ (Vector.ofFn word.1.2)).value.toEquiv) = _
  rw [CurrentPermutationDraw.draw_equiv]
  congr 1
  congr 1
  funext index
  exact Vector.get_ofFn _ _

theorem draw_endpoints (security tableBits bits : ℕ) (cache : Cache security tableBits) (word : Tapes security bits) :
    ((draw security tableBits bits cache word).value.core).endpointPermutation =
      (endpointEquiv security).permCongr (PermutationProgram.draw (current security).dimension bits word.2) := by
  change (endpointEquiv security).permCongr ((CurrentPermutationDraw.draw _ _ (Vector.ofFn word.2)).value.toEquiv) = _
  rw [CurrentPermutationDraw.draw_equiv]
  congr 1
  congr 1
  funext index
  exact Vector.get_ofFn _ _

end CurrentAFT.CurrentCoreProposal
