import CurrentAFT.CurrentPreparedCoreProposal
import CurrentAFT.BinaryCoreWeightResources
import CurrentAFT.BinaryCoreChargeResources
import CurrentAFT.RejectionProjection
import CurrentAFT.ClippedRejectionCoin

/-! # Actual finite-bit current public rejection

Each attempt produces its public proposal and reference cache, reads the
materialized controls to evaluate the complete joint weight, executes charge,
and uses a binary rational acceptance coin. Failure returns `none`.
-/
namespace CurrentAFT.BinaryPublicRejection
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram CurrentCoreProposal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentPreparedCoreProposal.draw BinaryCoreWeightData.current BinaryCoreCharge.current

def sample (security tableBits drawBits : ℕ) (word : Tapes security drawBits) :
    CountedValue (Option (MaterializedCore security)) :=
  let result := CurrentPreparedCoreProposal.draw security tableBits drawBits word
  ⟨some result.value, result.work+1⟩

def score (security weightBits order : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order) :
    Option (MaterializedCore security) → CountedValue RationalBits
  | none => ⟨RationalBits.zero, 1⟩
  | some core =>
    let value := BinaryCoreWeightData.current security weightBits order table core
    let charge := BinaryCoreCharge.current security core
    ⟨if charge.value then value.value else RationalBits.zero, value.work+charge.work+3⟩

def current (security tableBits drawBits weightBits coinBits order attempts : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order)
    (words : Vector (Tapes security drawBits × (Fin coinBits → Fin 2)) attempts) :
    CountedValue (Option (MaterializedCore security)) :=
  let envelope := RationalBits.ofCounter 2
  let result := BinaryArrayRejection.run (sample security tableBits drawBits) (score security weightBits order table)
    envelope.data coinBits ⟨none, 1⟩ attempts words
  ⟨result.value, envelope.work+result.work+1⟩

def decodeResult (security : ℕ) : Option (MaterializedCore security) → Option (ActualPublicCharge.Core security) :=
  Option.map MaterializedCore.core

def draw (security tableBits drawBits weightBits coinBits order attempts : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order)
    (words : Fin attempts → Tapes security drawBits × (Fin coinBits → Fin 2)) :
    CountedValue (Option (MaterializedCore security)) :=
  let stored := storeData attempts (fun index => ⟨words index, 1⟩)
  let result := current security tableBits drawBits weightBits coinBits order attempts table stored.value
  ⟨result.value, stored.work+result.work+2⟩

noncomputable section
open scoped Classical
attribute [local irreducible] RationalWeightProgram.current

def coreWeight (security weightBits order : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order)
    (core : ActualPublicCharge.Core security) : ℚ :=
  RationalWeightProgram.current security weightBits order (Parameters.legCount security)
    (BackgroundRates.ordinaryPool security) (BinaryWeightLocal.rawTable security order table)
    (fun index => ((core.controls (.inl index)).1.val, (core.controls (.inl index)).2.val.val))
    (fun index => (core.controls (.inr index)).2.val.val)

def coreScore (security weightBits order : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order) :
    Option (ActualPublicCharge.Core security) → ℚ
  | none => 0
  | some core => if ActualPublicCharge.publicCharge security core then coreWeight security weightBits order table core else 0

theorem score_value (security weightBits order : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order)
    (input : Option (MaterializedCore security)) :
    (score security weightBits order table input).value.decode =
      coreScore security weightBits order table (decodeResult security input) := by
  cases input with
  | none => rfl
  | some core =>
    change (if (BinaryCoreCharge.current security core).value = true then
      (BinaryCoreWeightData.current security weightBits order table core).value else RationalBits.zero).decode = _
    by_cases h : (BinaryCoreCharge.current security core).value = true
    · rw [if_pos h, BinaryCoreWeightData.current_value_actual]
      exact (if_pos ((BinaryCoreCharge.current_value security core).mp h)).symm
    · rw [if_neg h, RationalBits.zero_value]
      exact (if_neg (fun hc => h ((BinaryCoreCharge.current_value security core).mpr hc))).symm

theorem current_value (security tableBits drawBits weightBits coinBits order attempts : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order)
    (words : Vector (Tapes security drawBits × (Fin coinBits → Fin 2)) attempts) :
    decodeResult security (current security tableBits drawBits weightBits coinBits order attempts table words).value =
      RationalRejectionProgram.positiveDraw
        (fun word => some (CurrentPreparedCoreProposal.draw security tableBits drawBits word).value.core)
        (coreScore security weightBits order table) 2 coinBits attempts none words.get := by
  exact RejectionProjection.array_value (decodeResult security) (sample security tableBits drawBits)
    (score security weightBits order table) (coreScore security weightBits order table)
    (score_value security weightBits order table) (RationalBits.ofCounter 2).data 2 coinBits
    (RationalBits.ofCounter_value 2) ⟨none, 1⟩ attempts words

theorem draw_value (security tableBits drawBits weightBits coinBits order attempts : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order)
    (words : Fin attempts → Tapes security drawBits × (Fin coinBits → Fin 2)) :
    decodeResult security (draw security tableBits drawBits weightBits coinBits order attempts table words).value =
      RationalRejectionProgram.positiveDraw
        (fun word => some (CurrentPreparedCoreProposal.draw security tableBits drawBits word).value.core)
        (coreScore security weightBits order table) 2 coinBits attempts none words := by
  change decodeResult security (current security tableBits drawBits weightBits coinBits order attempts table
    (storeData attempts (fun index => ⟨words index, 1⟩)).value).value = _
  rw [current_value]
  congr 1
  funext index
  exact storeData_get _ _ index

end
end CurrentAFT.BinaryPublicRejection
