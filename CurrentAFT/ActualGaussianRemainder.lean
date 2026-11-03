import CurrentAFT.ActualGaussianAccuracy

/-! A single negligible analytical remainder, uniform over public placements.
The finite maximum is used only in the bound, never by the sampler. -/
namespace CurrentAFT.ActualGaussianRemainder
open AFT ActualCompleteStability ActualCalibrationClipping ActualCalibrationRates
open Filter
open scoped Classical Topology
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension

abbrev Layout (security : ℕ) := ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security

def chargedClip (security order : ℕ) (horder : 2≤order) : ℝ :=
  if hs : threshold order horder≤security then
    (Finset.univ : Finset (Option (Layout security))).sup' Finset.univ_nonempty
      (fun layout => layout.elim 0 (fun layout => (Parameters.modulus security:ℝ)*loss security order horder hs layout))
  else 0

theorem chargedClip_nonneg (security order : ℕ) (horder : 2≤order) : 0≤chargedClip security order horder := by
  unfold chargedClip
  split_ifs
  · exact Finset.le_sup'_of_le _ (Finset.mem_univ none) le_rfl
  · exact le_rfl

theorem chargedClip_le (security order : ℕ) (horder : 2≤order) (hs : threshold order horder≤security)
    (layout : Layout security) :
    (Parameters.modulus security:ℝ)*loss security order horder hs layout ≤ chargedClip security order horder := by
  unfold chargedClip
  rw [dif_pos hs]
  exact Finset.le_sup' (fun entry : Option (Layout security) => entry.elim 0
    (fun entry => (Parameters.modulus security:ℝ)*loss security order horder hs entry)) (Finset.mem_univ (some layout))

theorem chargedClip_negligible (order : ℕ) (horder : 2≤order) : Negligible (fun security => chargedClip security order horder) := by
  intro decay
  obtain ⟨cutoff,hcutoff⟩ := charged_loss_negligible order horder decay
  filter_upwards [eventually_ge_atTop cutoff,eventually_ge_atTop 1] with security hc hs
  rw [abs_of_nonneg (chargedClip_nonneg security order horder)]
  have hip : inversePower security decay ≤ 1/(security:ℝ)^decay := by
    unfold inversePower
    apply one_div_le_one_div_of_le (by positivity)
    apply pow_le_pow_left₀ (Nat.cast_nonneg _)
    exact_mod_cast (show security≤Parameters.base security by unfold Parameters.base; omega)
  unfold chargedClip
  split_ifs with ht
  · apply Finset.sup'_le
    intro layout _
    cases layout with
    | none => positivity
    | some layout => exact (hcutoff security hc ht layout).trans hip
  · positivity

def remainder (security order : ℕ) (horder : 2≤order) : ℝ :=
  2*chargedClip security order horder+CurrentSourceProtection.budget security

theorem remainder_nonneg (security order : ℕ) (horder : 2≤order) : 0≤remainder security order horder := by
  unfold remainder
  positivity [chargedClip_nonneg security order horder,CurrentSourceProtection.budget_nonneg security]

theorem remainder_negligible (order : ℕ) (horder : 2≤order) : Negligible (fun security => remainder security order horder) :=
  ((chargedClip_negligible order horder).const_mul 2).add CurrentSourceTail.budget_negligible

theorem analytic_le (security order : ℕ) (horder : 2≤order) (hs : threshold order horder≤security) (layout : Layout security) :
    2*(Parameters.modulus security:ℝ)*(fourierError security order+loss security order horder hs layout)+CurrentSourceProtection.budget security ≤
      (2*fourierConstant order)*(Parameters.modulus security:ℝ)*(Parameters.base security:ℝ)^(-((order+1:ℕ):ℝ)/4)+remainder security order horder := by
  have h := chargedClip_le security order horder hs layout
  rw [fourierError_eq]
  unfold remainder
  nlinarith

end
end CurrentAFT.ActualGaussianRemainder
