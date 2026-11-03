import CurrentAFT.CurrentCoreProposalLaw

/-! Product error of the actual finite-bit current public proposal. -/
namespace CurrentAFT.CurrentCoreProposalRates
open AFT ActualPublicCharge CurrentReferenceDraw CurrentReferenceDrawRates CurrentProposalDimensions
  CurrentCoreProposal CurrentCoreProposalLaw
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
attribute [local irreducible] Parameters.legCount Parameters.dimension Parameters.bodySize

abbrev ticketError (bits : ℕ) : ℝ := 1 / (2 : ℝ)^bits

def controlError (security tableBits bits : ℕ) : ℝ :=
  2 * ticketError bits + (Parameters.modulus security : ℝ) *
    (64 * (Parameters.base security : ℝ) * Parameters.dimension security +
      (64 * (Parameters.base security : ℝ) * Parameters.dimension security * Parameters.modulus security + 2)) * ticketError tableBits

def error (security tableBits bits : ℕ) : ℝ :=
  ((current security).controls : ℝ) * controlError security tableBits bits +
    (Parameters.legCount security : ℝ) * (5 * ticketError bits + ticketError tableBits) +
    (Parameters.modulus security : ℝ) * ticketError bits +
    2 * ((current security).body : ℝ)^2 * ticketError bits +
    2 * ((current security).dimension : ℝ)^2 * ticketError bits

theorem control_law_eq (security tableBits bits : ℕ) (cache : Cache security tableBits) :
    controlLaw security tableBits bits cache =
      (primaryDrawLaw security tableBits bits cache).prod (bodyDrawLaw security tableBits bits cache) := by
  exact FiniteDist.prod_map_functions
    (FiniteDist.uniform (Fin (bits + (PublicParameterProgram.modulus security).count + 1) → Fin 2))
    (FiniteDist.uniform (Fin (bits + (CurrentReferenceDraw.counts security).safe + 1) → Fin 2))
    (fun word => (CurrentReferenceDraw.primaryDraw security tableBits bits cache word).value)
    (fun word => (CurrentReferenceDraw.bodyDraw security tableBits bits cache word).value)

theorem leg_law_eq (security tableBits bits : ℕ) (cache : Cache security tableBits) :
    legLaw security tableBits bits cache =
      (CurrentPublicSeedDraw.law security tableBits bits cache).prod (CurrentSafeDraw.law security bits) := by
  exact FiniteDist.prod_map_functions (CurrentPublicSeedDraw.tapeLaw security bits)
    (FiniteDist.uniform (CurrentSafeDraw.Tape security bits))
    (fun word => (CurrentPublicSeedDraw.draw security tableBits bits cache word).value)
    (fun word => (CurrentSafeDraw.draw security bits word).value)

theorem control_l1 (security tableBits bits : ℕ) (cache : Cache security tableBits)
    (hprecision : ticketError tableBits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * ticketError tableBits ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    (∑ group, |(controlLaw security tableBits bits cache).weight group -
      (SafeControlGroups.reference security).weight group|) ≤ controlError security tableBits bits := by
  rw [control_law_eq]
  apply (FiniteDist.l1_prod_le _ (ProposalPrimary.primaryLaw security) _ (ActualControls.bodyReference security)).trans
  have hp := primary_draw_l1 security tableBits bits cache hprecision hbudget
  have hb := body_draw_l1 security tableBits bits cache hprecision hbudget
  unfold controlError ticketError
  linarith

theorem leg_l1 (security tableBits bits : ℕ) (cache : Cache security tableBits) :
    (∑ leg, |(legLaw security tableBits bits cache).weight leg - (legCoreLaw security).weight leg|) ≤
      5 * ticketError bits + ticketError tableBits := by
  rw [leg_law_eq]
  have h := FiniteDist.l1_prod_le (CurrentPublicSeedDraw.law security tableBits bits cache)
    (ActualPublicLegCharge.seedLaw security) (CurrentSafeDraw.law security bits) (ProposalPrimary.safeLaw security)
  have hs := CurrentPublicSeedDraw.law_l1 security tableBits bits cache
  have hb := CurrentSafeDraw.law_l1 security bits
  unfold ticketError
  change (∑ leg, |((CurrentPublicSeedDraw.law security tableBits bits cache).prod (CurrentSafeDraw.law security bits)).weight leg -
    ((ActualPublicLegCharge.seedLaw security).prod (ProposalPrimary.safeLaw security)).weight leg|) ≤ _
  linarith

theorem body_permutation_l1 (security bits : ℕ) :
    (∑ permutation, |(CurrentCoreProposalLaw.bodyPermutationLaw security bits).weight permutation -
      (FiniteDist.uniform (Equiv.Perm (ActualCycleMeanMGF.BodyIndex security))).weight permutation|) ≤
      2 * ((current security).body : ℝ)^2 * ticketError bits := by
  have h := FiniteDist.l1_map_le (CurrentPermutationDraw.law (current security).body bits)
    (FiniteDist.uniform (Equiv.Perm (Fin (current security).body))) (CurrentProposalDimensions.bodyEquiv security).permCongr
  rw [FiniteDist.uniform_map_equiv] at h
  exact h.trans (by simpa only [ticketError, div_eq_mul_inv, one_mul] using CurrentPermutationDraw.law_l1 (current security).body bits)

theorem endpoint_permutation_l1 (security bits : ℕ) :
    (∑ permutation, |(CurrentCoreProposalLaw.endpointPermutationLaw security bits).weight permutation -
      (FiniteDist.uniform (Equiv.Perm (Fin (Parameters.dimension security)))).weight permutation|) ≤
      2 * ((current security).dimension : ℝ)^2 * ticketError bits := by
  have h := FiniteDist.l1_map_le (CurrentPermutationDraw.law (current security).dimension bits)
    (FiniteDist.uniform (Equiv.Perm (Fin (current security).dimension))) (endpointEquiv security).permCongr
  rw [FiniteDist.uniform_map_equiv] at h
  exact h.trans (by simpa only [ticketError, div_eq_mul_inv, one_mul] using CurrentPermutationDraw.law_l1 (current security).dimension bits)

theorem proposal_l1 (security tableBits bits : ℕ) (cache : Cache security tableBits)
    (hprecision : ticketError tableBits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * ticketError tableBits ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    (∑ core, |(CurrentCoreProposalLaw.law security tableBits bits cache).weight core -
      (proposal security).weight core|) ≤ error security tableBits bits := by
  have hcontrol := FiniteDist.l1_independent_le
    (fun _ : PublicOutputExperiment.PublicIndex security => controlLaw security tableBits bits cache)
    (fun _ => SafeControlGroups.reference security)
  have hc : (∑ controls, |(FiniteDist.independent (fun _ : PublicOutputExperiment.PublicIndex security =>
        controlLaw security tableBits bits cache)).weight controls - (PublicOutputExperiment.reference security).weight controls|) ≤
      ((current security).controls : ℝ) * controlError security tableBits bits := by
    apply hcontrol.trans
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun _ : PublicOutputExperiment.PublicIndex security => fun _ => control_l1 security tableBits bits cache hprecision hbudget)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin, nsmul_eq_mul,
      (current_values security).2.2.2.2.2, Nat.cast_add] using hsum
  have hl := FiniteDist.l1_independent_fin_le (Parameters.legCount security)
    (fun _ => legLaw security tableBits bits cache) (fun _ => legCoreLaw security)
  have hl' : (∑ legs, |(FiniteDist.independent (fun _ : Fin (Parameters.legCount security) =>
      legLaw security tableBits bits cache)).weight legs -
      (FiniteDist.independent (fun _ : Fin (Parameters.legCount security) => legCoreLaw security)).weight legs|) ≤
      (Parameters.legCount security : ℝ) * (5 * ticketError bits + ticketError tableBits) := by
    apply hl.trans
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun _ : Fin (Parameters.legCount security) => fun _ => leg_l1 security tableBits bits cache)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hsum
  have hq := FiniteDist.l1_independent_fin_le (Parameters.modulus security)
    (fun _ => CurrentSafeDraw.law security bits) (fun _ => ProposalPrimary.safeLaw security)
  have hq' : (∑ baselines, |(FiniteDist.independent (fun _ : Fin (Parameters.modulus security) =>
      CurrentSafeDraw.law security bits)).weight baselines -
      (FiniteDist.independent (fun _ : Fin (Parameters.modulus security) => ProposalPrimary.safeLaw security)).weight baselines|) ≤
      (Parameters.modulus security : ℝ) * ticketError bits := by
    apply hq.trans
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun _ : Fin (Parameters.modulus security) => fun _ => CurrentSafeDraw.law_l1 security bits)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hsum
  let target : FiniteDist (Source security) :=
    ((((PublicOutputExperiment.reference security).prod
      (FiniteDist.independent (fun _ : Fin (Parameters.legCount security) => legCoreLaw security))).prod
      (FiniteDist.independent (fun _ : Fin (Parameters.modulus security) => ProposalPrimary.safeLaw security))).prod
      (FiniteDist.uniform (Equiv.Perm (ActualCycleMeanMGF.BodyIndex security)))).prod
      (FiniteDist.uniform (Equiv.Perm (Fin (Parameters.dimension security))))
  rw [CurrentCoreProposalLaw.law_eq]
  have he : proposal security = target.map (assemble security) := rfl
  rw [he]
  apply (FiniteDist.l1_map_le _ _ (assemble security)).trans
  unfold sourceLaw target
  apply (FiniteDist.l1_prod_le _ _ _ _).trans
  apply add_le_add _ (endpoint_permutation_l1 security bits)
  apply (FiniteDist.l1_prod_le _ _ _ _).trans
  apply add_le_add _ (body_permutation_l1 security bits)
  apply (FiniteDist.l1_prod_le _ _ _ _).trans
  apply add_le_add _ hq'
  exact (FiniteDist.l1_prod_le _ _ _ _).trans (add_le_add hc hl')

end
end CurrentAFT.CurrentCoreProposalRates
