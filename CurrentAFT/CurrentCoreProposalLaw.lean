import CurrentAFT.CurrentCoreProposal
import CurrentAFT.CurrentReferenceDrawRates
import AFT.FiniteIndependentSampling

/-! Exact law of the executed materialized current proposal, before rejection.
The product decomposition is proved from the actual independent input tapes. -/
namespace CurrentAFT.CurrentCoreProposalLaw
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
open ActualPublicCharge CurrentReferenceDraw CurrentProposalDimensions CurrentCoreProposal
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
attribute [local irreducible] Parameters.legCount Parameters.dimension Parameters.bodySize
  CurrentCoreProposal.draw CurrentPermutationDraw.draw

abbrev Source (security : ℕ) :=
  (((PublicOutputExperiment.PublicWord security × (Fin (Parameters.legCount security) → LegCore security)) ×
    (Fin (Parameters.modulus security) → FirstHistogram.Palette security)) ×
      Equiv.Perm (ActualCycleMeanMGF.BodyIndex security)) × Equiv.Perm (Fin (Parameters.dimension security))

def assemble (security : ℕ) (source : Source security) : Core security :=
  ⟨source.1.1.1.1, source.1.1.1.2, source.1.1.2, source.1.2, source.2⟩

def controlTapeLaw (security bits : ℕ) : FiniteDist (ControlTape security bits) :=
  (FiniteDist.uniform (Fin (bits + (PublicParameterProgram.modulus security).count + 1) → Fin 2)).prod
    (FiniteDist.uniform (Fin (bits + (CurrentReferenceDraw.counts security).safe + 1) → Fin 2))

def controlLaw (security tableBits bits : ℕ) (cache : Cache security tableBits) :
    FiniteDist (SafeControlGroups.SafeGroup security) :=
  (controlTapeLaw security bits).map (fun word => (controlDraw security tableBits bits cache word).value)

def legTapeLaw (security bits : ℕ) : FiniteDist (LegTape security bits) :=
  (CurrentPublicSeedDraw.tapeLaw security bits).prod (FiniteDist.uniform (CurrentSafeDraw.Tape security bits))

def legLaw (security tableBits bits : ℕ) (cache : Cache security tableBits) : FiniteDist (LegCore security) :=
  (legTapeLaw security bits).map (fun word => (legDraw security tableBits bits cache word).value)

def bodyPermutationLaw (security bits : ℕ) : FiniteDist (Equiv.Perm (ActualCycleMeanMGF.BodyIndex security)) :=
  (CurrentPermutationDraw.law (current security).body bits).map (CurrentProposalDimensions.bodyEquiv security).permCongr

def endpointPermutationLaw (security bits : ℕ) : FiniteDist (Equiv.Perm (Fin (Parameters.dimension security))) :=
  (CurrentPermutationDraw.law (current security).dimension bits).map (endpointEquiv security).permCongr

def sourceLaw (security tableBits bits : ℕ) (cache : Cache security tableBits) : FiniteDist (Source security) :=
  (((((FiniteDist.independent (fun _ : PublicOutputExperiment.PublicIndex security => controlLaw security tableBits bits cache)).prod
    (FiniteDist.independent (fun _ : Fin (Parameters.legCount security) => legLaw security tableBits bits cache))).prod
    (FiniteDist.independent (fun _ : Fin (Parameters.modulus security) => CurrentSafeDraw.law security bits))).prod
    (bodyPermutationLaw security bits)).prod (endpointPermutationLaw security bits))

def tapeLaw (security bits : ℕ) : FiniteDist (Tapes security bits) :=
  (((((FiniteDist.independent (fun _ : PublicOutputExperiment.PublicIndex security => controlTapeLaw security bits)).prod
    (FiniteDist.independent (fun _ : Fin (Parameters.legCount security) => legTapeLaw security bits))).prod
    (FiniteDist.independent (fun _ : Fin (Parameters.modulus security) => FiniteDist.uniform (CurrentSafeDraw.Tape security bits)))).prod
    (FiniteDist.uniform (Fin ((current security).body * bits) → Fin 2))).prod
    (FiniteDist.uniform (Fin ((current security).dimension * bits) → Fin 2)))

def sourceValue (security tableBits bits : ℕ) (cache : Cache security tableBits) (word : Tapes security bits) : Source security :=
  (((((fun index => (controlDraw security tableBits bits cache (word.1.1.1.1 index)).value),
      (fun index => (legDraw security tableBits bits cache (word.1.1.1.2 index)).value)),
      (fun index => (CurrentSafeDraw.draw security bits (word.1.1.2 index)).value)),
      (CurrentProposalDimensions.bodyEquiv security).permCongr (PermutationProgram.draw (current security).body bits word.1.2)),
      (endpointEquiv security).permCongr (PermutationProgram.draw (current security).dimension bits word.2))

private theorem core_ext {security : ℕ} (first second : Core security)
    (hc : first.controls = second.controls) (hl : first.legs = second.legs)
    (hq : first.queueBaselines = second.queueBaselines) (hb : first.bodyPermutation = second.bodyPermutation)
    (he : first.endpointPermutation = second.endpointPermutation) : first = second := by
  cases first
  cases second
  cases hc
  cases hl
  cases hq
  cases hb
  cases he
  rfl

theorem draw_source (security tableBits bits : ℕ) (cache : Cache security tableBits) (word : Tapes security bits) :
    (draw security tableBits bits cache word).value.core = assemble security (sourceValue security tableBits bits cache word) := by
  apply core_ext
  · funext index; exact draw_controls security tableBits bits cache word index
  · funext index; exact draw_legs security tableBits bits cache word index
  · funext index; exact draw_baselines security tableBits bits cache word index
  · exact draw_body security tableBits bits cache word
  · exact draw_endpoints security tableBits bits cache word

theorem source_law (security tableBits bits : ℕ) (cache : Cache security tableBits) :
    (tapeLaw security bits).map (sourceValue security tableBits bits cache) = sourceLaw security tableBits bits cache := by
  let controlValue := fun word : PublicOutputExperiment.PublicIndex security → ControlTape security bits =>
    fun index => (controlDraw security tableBits bits cache (word index)).value
  let legValue := fun word : Fin (Parameters.legCount security) → LegTape security bits =>
    fun index => (legDraw security tableBits bits cache (word index)).value
  let queueValue := fun word : Fin (Parameters.modulus security) → CurrentSafeDraw.Tape security bits =>
    fun index => (CurrentSafeDraw.draw security bits (word index)).value
  let bodyValue := fun word : Fin ((current security).body * bits) → Fin 2 =>
    (CurrentProposalDimensions.bodyEquiv security).permCongr (PermutationProgram.draw (current security).body bits word)
  let endpointValue := fun word : Fin ((current security).dimension * bits) → Fin 2 =>
    (endpointEquiv security).permCongr (PermutationProgram.draw (current security).dimension bits word)
  have hcontrol := FiniteConditionProgram.independent_decode
    (Index := PublicOutputExperiment.PublicIndex security) (Random := ControlTape security bits)
    (State := SafeControlGroups.SafeGroup security)
    (fun _ => controlTapeLaw security bits) (fun _ word => (controlDraw security tableBits bits cache word).value)
  have hleg := FiniteConditionProgram.independent_decode
    (Index := Fin (Parameters.legCount security)) (Random := LegTape security bits) (State := LegCore security)
    (fun _ => legTapeLaw security bits) (fun _ word => (legDraw security tableBits bits cache word).value)
  have hqueue := FiniteConditionProgram.independent_decode
    (Index := Fin (Parameters.modulus security)) (Random := CurrentSafeDraw.Tape security bits)
    (State := FirstHistogram.Palette security)
    (fun _ => FiniteDist.uniform (CurrentSafeDraw.Tape security bits))
    (fun _ word => (CurrentSafeDraw.draw security bits word).value)
  have hbody : (FiniteDist.uniform (Fin ((current security).body * bits) → Fin 2)).map bodyValue =
      bodyPermutationLaw security bits := by
    unfold bodyPermutationLaw CurrentPermutationDraw.law
    rw [FiniteDist.map_map]
    congr 1
    funext word
    dsimp only [bodyValue]
    rw [CurrentPermutationDraw.draw_equiv]
    congr 1
    congr 1
    funext index
    exact (Vector.get_ofFn word index).symm
  have hendpoint : (FiniteDist.uniform (Fin ((current security).dimension * bits) → Fin 2)).map endpointValue =
      endpointPermutationLaw security bits := by
    unfold endpointPermutationLaw CurrentPermutationDraw.law
    rw [FiniteDist.map_map]
    congr 1
    funext word
    dsimp only [endpointValue]
    rw [CurrentPermutationDraw.draw_equiv]
    congr 1
    congr 1
    funext index
    exact (Vector.get_ofFn word index).symm
  have hfirst := FiniteDist.prod_map_functions
    (FiniteDist.independent (fun _ : PublicOutputExperiment.PublicIndex security => controlTapeLaw security bits))
    (FiniteDist.independent (fun _ : Fin (Parameters.legCount security) => legTapeLaw security bits)) controlValue legValue
  rw [hcontrol, hleg] at hfirst
  have hsecond := FiniteDist.prod_map_functions
    ((FiniteDist.independent (fun _ : PublicOutputExperiment.PublicIndex security => controlTapeLaw security bits)).prod
      (FiniteDist.independent (fun _ : Fin (Parameters.legCount security) => legTapeLaw security bits)))
    (FiniteDist.independent (fun _ : Fin (Parameters.modulus security) => FiniteDist.uniform (CurrentSafeDraw.Tape security bits)))
    (fun pair => (controlValue pair.1, legValue pair.2)) queueValue
  rw [hfirst, hqueue] at hsecond
  have hthird := FiniteDist.prod_map_functions
    (((FiniteDist.independent (fun _ : PublicOutputExperiment.PublicIndex security => controlTapeLaw security bits)).prod
      (FiniteDist.independent (fun _ : Fin (Parameters.legCount security) => legTapeLaw security bits))).prod
      (FiniteDist.independent (fun _ : Fin (Parameters.modulus security) => FiniteDist.uniform (CurrentSafeDraw.Tape security bits))))
    (FiniteDist.uniform (Fin ((current security).body * bits) → Fin 2))
    (fun pair => ((controlValue pair.1.1, legValue pair.1.2), queueValue pair.2)) bodyValue
  rw [hsecond, hbody] at hthird
  have hfourth := FiniteDist.prod_map_functions
    ((((FiniteDist.independent (fun _ : PublicOutputExperiment.PublicIndex security => controlTapeLaw security bits)).prod
      (FiniteDist.independent (fun _ : Fin (Parameters.legCount security) => legTapeLaw security bits))).prod
      (FiniteDist.independent (fun _ : Fin (Parameters.modulus security) => FiniteDist.uniform (CurrentSafeDraw.Tape security bits)))).prod
      (FiniteDist.uniform (Fin ((current security).body * bits) → Fin 2)))
    (FiniteDist.uniform (Fin ((current security).dimension * bits) → Fin 2))
    (fun pair => (((controlValue pair.1.1.1, legValue pair.1.1.2), queueValue pair.1.2), bodyValue pair.2)) endpointValue
  rw [hthird, hendpoint] at hfourth
  exact hfourth

def law (security tableBits bits : ℕ) (cache : Cache security tableBits) : FiniteDist (Core security) :=
  (tapeLaw security bits).map (fun word => (draw security tableBits bits cache word).value.core)

theorem law_eq (security tableBits bits : ℕ) (cache : Cache security tableBits) :
    law security tableBits bits cache = (sourceLaw security tableBits bits cache).map (assemble security) := by
  simp only [law, draw_source, ← FiniteDist.map_map, source_law]

end
end CurrentAFT.CurrentCoreProposalLaw
