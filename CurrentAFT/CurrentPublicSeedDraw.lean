import CurrentAFT.CurrentActivationDraw
import CurrentAFT.CurrentAnchorIndexDraw
import CurrentAFT.CurrentEdgeDrawProgram

/-! Executed current public leg seeds. The protected first/second sources are
absent: activation, fair coin, anchor index and two blur edges are sampled
independently from the actual public reference data. -/
namespace CurrentAFT.CurrentPublicSeedDraw
open AFT AFT.GaussianSource AFT.RationalNumerics AFT.BinaryArithmetic AFT.RationalRejectionProgram
open CurrentReferenceDraw
open scoped BigOperators
set_option maxHeartbeats 800000
attribute [local irreducible] Parameters.anchorWidth Parameters.base

abbrev EdgeTape (security bits : ℕ) := Fin (windowTicketBits (DiffuseProfiles.edgeCutoff security) bits) → Fin 2
abbrev Tape (security bits : ℕ) := (Fin (bits + 2 + 1) → Fin 2) ×
  (Bool × (CurrentAnchorIndexDraw.Tape security bits × (EdgeTape security bits × EdgeTape security bits)))

def draw (security tableBits drawBits : ℕ) (cache : Cache security tableBits) (word : Tape security drawBits) :
    CountedValue (ActualPublicLegCharge.PublicSeed security) :=
  let activation := CurrentActivationDraw.draw security tableBits drawBits cache word.1
  let anchor := CurrentAnchorIndexDraw.draw security drawBits word.2.2.1
  let first := CurrentEdgeDrawProgram.draw security drawBits word.2.2.2.1
  let second := CurrentEdgeDrawProgram.draw security drawBits word.2.2.2.2
  ⟨⟨activation.value, word.2.1, anchor.value, (first.value, second.value)⟩,
    activation.work + anchor.work + first.work + second.work + 5⟩


def workBound (security height bits : ℕ) : ℕ :=
  CurrentActivationDraw.workBound height bits + CurrentAnchorIndexDraw.workBound security bits +
    2 * CurrentEdgeDrawProgram.workBound security bits + 5

theorem draw_work (security tableBits bits height : ℕ) (cache : Cache security tableBits)
    (hh : AFT.RationalNumerics.HeightBound cache.activation.decode height) (word : Tape security bits) :
    (draw security tableBits bits cache word).work ≤ workBound security height bits := by
  have ha := CurrentActivationDraw.draw_work security tableBits bits height cache hh word.1
  have hi := CurrentAnchorIndexDraw.draw_work security bits word.2.2.1
  have hfirst := CurrentEdgeDrawProgram.draw_work security bits word.2.2.2.1
  have hsecond := CurrentEdgeDrawProgram.draw_work security bits word.2.2.2.2
  change (CurrentActivationDraw.draw security tableBits bits cache word.1).work +
    (CurrentAnchorIndexDraw.draw security bits word.2.2.1).work +
    (CurrentEdgeDrawProgram.draw security bits word.2.2.2.1).work +
    (CurrentEdgeDrawProgram.draw security bits word.2.2.2.2).work + 5 ≤ _
  unfold workBound
  omega

noncomputable section
open scoped Classical
local instance anchorNonempty (security : ℕ) : Nonempty (InwardAnchor.Index security) :=
  ⟨⟨0, InwardAnchor.anchorWidth_pos security⟩⟩

def edgeLaw (security bits : ℕ) : FiniteDist (Window (DiffuseProfiles.edgeCutoff security)) :=
  (FiniteDist.uniform (EdgeTape security bits)).map (fun word => (CurrentEdgeDrawProgram.draw security bits word).value)

def tapeLaw (security bits : ℕ) : FiniteDist (Tape security bits) :=
  (FiniteDist.uniform (Fin (bits + 2 + 1) → Fin 2)).prod ((FiniteDist.uniform Bool).prod
    ((FiniteDist.uniform (CurrentAnchorIndexDraw.Tape security bits)).prod
      ((FiniteDist.uniform (EdgeTape security bits)).prod (FiniteDist.uniform (EdgeTape security bits)))))

def productLaw (security tableBits drawBits : ℕ) (cache : Cache security tableBits) :
    FiniteDist (ActualPublicLegCharge.SeedProduct security) :=
  (CurrentActivationDraw.drawLaw security tableBits drawBits cache).prod ((FiniteDist.uniform Bool).prod
    ((CurrentAnchorIndexDraw.law security drawBits).prod ((edgeLaw security drawBits).prod (edgeLaw security drawBits))))

def law (security tableBits drawBits : ℕ) (cache : Cache security tableBits) :
    FiniteDist (ActualPublicLegCharge.PublicSeed security) :=
  (tapeLaw security drawBits).map (fun word => (draw security tableBits drawBits cache word).value)

theorem law_eq (security tableBits drawBits : ℕ) (cache : Cache security tableBits) :
    law security tableBits drawBits cache =
      (productLaw security tableBits drawBits cache).map (ActualPublicLegCharge.seedEquiv security).symm := by
  let value : Tape security drawBits → ActualPublicLegCharge.SeedProduct security := fun word =>
    ((CurrentActivationDraw.draw security tableBits drawBits cache word.1).value, (word.2.1,
      ((CurrentAnchorIndexDraw.draw security drawBits word.2.2.1).value,
        ((CurrentEdgeDrawProgram.draw security drawBits word.2.2.2.1).value,
          (CurrentEdgeDrawProgram.draw security drawBits word.2.2.2.2).value))))
  have he : (tapeLaw security drawBits).map value = productLaw security tableBits drawBits cache := by
    let edgeValue := fun word : EdgeTape security drawBits => (CurrentEdgeDrawProgram.draw security drawBits word).value
    let anchorValue := fun word : CurrentAnchorIndexDraw.Tape security drawBits => (CurrentAnchorIndexDraw.draw security drawBits word).value
    let activationValue := fun word : Fin (drawBits + 2 + 1) → Fin 2 => (CurrentActivationDraw.draw security tableBits drawBits cache word).value
    have hfirst := FiniteDist.prod_map_functions
      (FiniteDist.uniform (EdgeTape security drawBits)) (FiniteDist.uniform (EdgeTape security drawBits)) edgeValue edgeValue
    have hsecond := FiniteDist.prod_map_functions
      (FiniteDist.uniform (CurrentAnchorIndexDraw.Tape security drawBits))
      ((FiniteDist.uniform (EdgeTape security drawBits)).prod (FiniteDist.uniform (EdgeTape security drawBits)))
      anchorValue (fun pair => (edgeValue pair.1, edgeValue pair.2))
    rw [hfirst] at hsecond
    have hthird := FiniteDist.prod_map_functions (FiniteDist.uniform Bool)
      ((FiniteDist.uniform (CurrentAnchorIndexDraw.Tape security drawBits)).prod
        ((FiniteDist.uniform (EdgeTape security drawBits)).prod (FiniteDist.uniform (EdgeTape security drawBits))))
      id (fun pair => (anchorValue pair.1, (edgeValue pair.2.1, edgeValue pair.2.2)))
    have hid : (FiniteDist.uniform Bool).map id = FiniteDist.uniform Bool := by
      ext flag
      simp
    rw [hsecond, hid] at hthird
    simp only [id_eq] at hthird
    have hfourth := FiniteDist.prod_map_functions
      (FiniteDist.uniform (Fin (drawBits + 2 + 1) → Fin 2))
      ((FiniteDist.uniform Bool).prod ((FiniteDist.uniform (CurrentAnchorIndexDraw.Tape security drawBits)).prod
        ((FiniteDist.uniform (EdgeTape security drawBits)).prod (FiniteDist.uniform (EdgeTape security drawBits)))))
      activationValue (fun pair => (pair.1, (anchorValue pair.2.1, (edgeValue pair.2.2.1, edgeValue pair.2.2.2))))
    rw [hthird] at hfourth
    exact hfourth
  have h := congrArg (fun distribution => distribution.map (ActualPublicLegCharge.seedEquiv security).symm) he
  simpa only [FiniteDist.map_map, law, value, draw, ActualPublicLegCharge.seedEquiv, Equiv.coe_fn_mk] using h

theorem edge_l1 (security bits : ℕ) :
    (∑ point, |(edgeLaw security bits).weight point - (DiffuseProfiles.edgeLaw security).weight point|) ≤ 1 / (2 : ℝ)^bits := by
  have h := CurrentEdgeDrawProgram.draw_l1 security bits
  rw [FiniteTicketSampler.independent_fair_bits_uniform] at h
  exact h

theorem law_l1 (security tableBits drawBits : ℕ) (cache : Cache security tableBits) :
    (∑ seed, |(law security tableBits drawBits cache).weight seed -
      (ActualPublicLegCharge.seedLaw security).weight seed|) ≤
        4 * (1 / (2 : ℝ)^drawBits) + 1 / (2 : ℝ)^tableBits := by
  have ha := CurrentActivationDraw.draw_l1 security tableBits drawBits cache
  have hi := CurrentAnchorIndexDraw.law_l1 security drawBits
  have he := edge_l1 security drawBits
  have hb := FiniteDist.l1_prod_le (edgeLaw security drawBits) (DiffuseProfiles.edgeLaw security)
    (edgeLaw security drawBits) (DiffuseProfiles.edgeLaw security)
  have hc := FiniteDist.l1_prod_le (CurrentAnchorIndexDraw.law security drawBits)
    (FiniteDist.uniform (InwardAnchor.Index security)) ((edgeLaw security drawBits).prod (edgeLaw security drawBits))
    (LocalReferenceEnergy.publicBlurLaw security)
  have hd := FiniteDist.l1_prod_le (FiniteDist.uniform Bool) (FiniteDist.uniform Bool)
    ((CurrentAnchorIndexDraw.law security drawBits).prod ((edgeLaw security drawBits).prod (edgeLaw security drawBits)))
    ((FiniteDist.uniform (InwardAnchor.Index security)).prod (LocalReferenceEnergy.publicBlurLaw security))
  have hf := FiniteDist.l1_prod_le (CurrentActivationDraw.drawLaw security tableBits drawBits cache)
    (ActualPublicLegCharge.activationLaw security)
    ((FiniteDist.uniform Bool).prod ((CurrentAnchorIndexDraw.law security drawBits).prod
      ((edgeLaw security drawBits).prod (edgeLaw security drawBits))))
    ((FiniteDist.uniform Bool).prod ((FiniteDist.uniform (InwardAnchor.Index security)).prod
      (LocalReferenceEnergy.publicBlurLaw security)))
  have hm := FiniteDist.l1_map_le (productLaw security tableBits drawBits cache)
    ((ActualPublicLegCharge.activationLaw security).prod ((FiniteDist.uniform Bool).prod
      ((FiniteDist.uniform (InwardAnchor.Index security)).prod (LocalReferenceEnergy.publicBlurLaw security))))
    (ActualPublicLegCharge.seedEquiv security).symm
  rw [← law_eq] at hm
  change (∑ seed, |(law security tableBits drawBits cache).weight seed -
    (ActualPublicLegCharge.seedLaw security).weight seed|) ≤ _ at hm
  simp only [sub_self, abs_zero, Finset.sum_const_zero] at hd
  change (∑ pair, |((edgeLaw security drawBits).prod (edgeLaw security drawBits)).weight pair -
    (LocalReferenceEnergy.publicBlurLaw security).weight pair|) ≤ _ at hb
  change (∑ seed, |(productLaw security tableBits drawBits cache).weight seed - _|) ≤ _ at hf
  linarith

end
end CurrentAFT.CurrentPublicSeedDraw
