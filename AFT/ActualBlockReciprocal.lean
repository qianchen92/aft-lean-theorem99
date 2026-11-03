import AFT.GlobalBackgroundCanonical
import AFT.PhysicalBackgroundPolynomial
import AFT.BackgroundQueueAlgebra

/-! # Uniform finite reciprocals of the actual physical local blocks -/
namespace AFT.V7Calibration
open GaussianSource Filter RepresentedPolynomial
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance actualBlockReciprocalFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance actualBlockReciprocalSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _

def actualBlockReciprocal (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (index : blockIndex n) (queue : ℤ) (cutoff : ℕ) : Table (InputSeed (Fin (Parameters.modulus n))) :=
  finiteCorrection (blockBackgroundError C n beta operator index queue) cutoff

theorem actual_block_error_canonical_eventually (C : ℝ) (hC : 1≤C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n)≤beta n ∧
      beta n≤2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap=actualResponse C n →∀ index : blockIndex n,∀ queue : ℤ,|queue| ≤ queueCutoff n →
      InputTableCanonical (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
        (blockBackgroundError C n (beta n) operator index queue) := by
  filter_upwards [actual_mean_tables_canonical_eventually C hC beta hbeta,
    actual_covariance_table_canonical_eventually C hC beta hbeta,
    actual_endpoint_table_canonical_eventually C hC beta hbeta,
    actual_primary_seed_canonical_eventually C hC beta hbeta] with n hm hc he hi operator hop index queue hq
  dsimp only at hm
  have hT (table : Table (InputSeed (Fin (Parameters.modulus n))))
      (ht : InputTableCanonical (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) table) :
      InputTableCanonical (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
        (inversePrimaryTable (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (v7Activation C n) operator table) :=
    inversePrimaryTable_canonical _ _ _ operator table ht (hi operator hop _)
  have hp := hT _ hm.1
  have he := he operator hop
  cases index with
  | inl _ =>
    have hb := hT _ (hm.2.2.1 queue hq)
    exact (hp.add hb).add (((he.add (hp.mul hb)).add (he.mul hb)).add (hT _ (hc queue hq)))
  | inr _ => exact hT _ (hm.2.1 queue (by unfold maxBodyShift; omega))

theorem actual_block_reciprocal_canonical_eventually (C : ℝ) (hC : 1≤C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n)≤beta n ∧
      beta n≤2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap=actualResponse C n →∀ index : blockIndex n,∀ queue : ℤ,|queue| ≤ queueCutoff n →∀ cutoff,
      InputTableCanonical (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
        (actualBlockReciprocal C n (beta n) operator index queue cutoff) := by
  filter_upwards [actual_block_error_canonical_eventually C hC beta hbeta] with n hc operator hop index queue hq cutoff
  exact (hc operator hop index queue hq).finiteCorrection cutoff

theorem actualBlockReciprocal_sub_one_hasOrder (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (index : blockIndex n) (queue : ℤ) (cutoff : ℕ) :
    HasOrder (fun seed => seed.primaryOrder+seed.bodyOrder) 1
      (actualBlockReciprocal C n beta operator index queue cutoff-1) :=
  hasOrder_finiteCorrection_sub_one _ _ _ (blockBackgroundError_hasOrder C n beta operator index queue)

theorem actual_block_reciprocal_polynomial_eventually (C : ℝ) (hC : 1≤C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n)≤beta n ∧
      beta n≤2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap=actualResponse C n →∀ index : blockIndex n,∀ queue : ℤ,|queue| ≤ queueCutoff n →∀ cutoff,
      truncate (fun _ => 1) cutoff
        (actualLeadingOutput C n (beta n) (actualBlockReciprocal C n (beta n) operator index queue cutoff)*
          blockPhysicalPolynomial C n (beta n) index queue)=1 := by
  filter_upwards [actual_block_background_polynomial_eventually C hC beta hbeta] with n hb operator hop index queue hq cutoff
  let output := actualLeadingOutput C n (beta n)
  let error := blockBackgroundError C n (beta n) operator index queue
  have he := hb operator hop index queue hq
  have ho : HasOrder (fun _ : Fin (Parameters.modulus n) => 1) 1 (output error) :=
    outputHom_hasOrder _ _ _ _ _ _ (blockBackgroundError_hasOrder C n (beta n) operator index queue)
  have hh := truncate_finiteCorrection_residual (fun _ : Fin (Parameters.modulus n) => 1) cutoff (output error) ho
  have hm : output (finiteCorrection error cutoff)=finiteCorrection (output error) cutoff := by
    simp only [finiteCorrection,map_sum,map_pow,map_neg]
  change truncate (fun _ => 1) cutoff (output (finiteCorrection error cutoff)*blockPhysicalPolynomial C n (beta n) index queue)=1
  rw [← he,map_add,map_one,hm,mul_comm]
  exact hh

theorem actual_block_reciprocal_activity_eventually (C : ℝ) (hC : 1≤C)
    (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n)≤beta n ∧
      beta n≤2*(Parameters.legs n : ℝ)/Parameters.dimension n ∧ Parameters.legs n≤2*pool n) :
    ∀ᶠ n in atTop,∃ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap=actualResponse C n ∧∀ bodyPool : ℕ,Parameters.bodies n≤2*bodyPool →
      ∀ index : blockIndex n,∀ queue : ℤ,|queue| ≤ queueCutoff n →
      let weight := inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (pool n) bodyPool ((n : ℝ)^2)
      activity weight (blockBackgroundError C n (beta n) operator index queue)≤1/2 ∧
      ∀ cutoff,activity weight (actualBlockReciprocal C n (beta n) operator index queue cutoff)≤2 := by
  have hlarge : ∀ᶠ n : ℕ in atTop,2*bodyMeanInputConstant≤(n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (2*bodyMeanInputConstant))
  filter_upwards [actual_local_log_remainder_eventually C hC beta pool htypical,
    actual_body_mean_input_table_eventually C hC beta pool htypical,hlarge,eventually_ge_atTop 2]
    with n hl hb hlarge hn
  obtain ⟨operator,hop,hl⟩ := hl
  obtain ⟨other,hother,hb⟩ := hb
  have heq := actualResponse_equiv_unique C n other operator hother hop
  subst other
  refine ⟨operator,hop,?_⟩
  intro bodyPool hpool index queue hq
  dsimp only
  let weight := inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (pool n) bodyPool ((n : ℝ)^2)
  have hw : ∀ seed,0≤weight seed := fun seed => inputWeight_nonneg _ _ _ _ _ seed (sq_nonneg _)
  have hs : activity weight (blockBackgroundError C n (beta n) operator index queue)≤1/2 := by
    cases index with
    | inl leg => exact (hl bodyPool hpool queue hq).1
    | inr body =>
      have hh := hb bodyPool hpool queue (by unfold maxBodyShift; omega)
      apply hh.trans
      have hx : (1 : ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
      have hx0 : (0 : ℝ)<n := lt_of_lt_of_le (by norm_num) hx
      apply (div_le_iff₀ (by positivity)).mpr
      have hp : (n : ℝ)≤(n : ℝ)^46 := by simpa only [pow_one] using pow_le_pow_right₀ hx (by decide : 1≤46)
      linarith
  exact ⟨hs,fun cutoff => activity_finiteCorrection_le_two weight hw _ cutoff hs⟩

end
end AFT.V7Calibration
