import CurrentAFT.TaggedPhysicalFock
import CurrentAFT.SafeControlGroups

/-! # Actual ordinary-body response in the complete physical Fock space -/

namespace CurrentAFT.OrdinaryPhysicalFock

open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy PhysicalFockRates
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.dimension ProposalPrimary.centerLaw
  BackgroundRates.ordinaryPool BackgroundRates.radius

abbrev Palette (security : ℕ) := LocalReferenceEnergy.Palette security
abbrev SafePalette (security : ℕ) := ActualControls.SafePalette security

/-- Extend a genuine safe control density by zero at forbidden atoms. -/
def extendDensity (security : ℕ) : (SafePalette security → ℝ) →ₗ[ℝ] (Palette security → ℝ) where
  toFun score color := if h : InwardAnchor.SafeColor security color then score ⟨color, h⟩ else 0
  map_add' first second := by
    funext color
    by_cases h : InwardAnchor.SafeColor security color <;> simp [h]
  map_smul' scalar score := by
    funext color
    by_cases h : InwardAnchor.SafeColor security color <;> simp [h]

theorem extendDensity_safe (security : ℕ) (score : SafePalette security → ℝ) (color : SafePalette security) :
    extendDensity security score color.val = score color := by
  simp only [extendDensity, LinearMap.coe_mk, AddHom.coe_mk, dif_pos color.property]

theorem extendDensity_mean (security : ℕ) (score : SafePalette security → ℝ) :
    (centerLaw security).expectation (extendDensity security score) =
      (ActualControls.bodyReference security).expectation score := by
  rw [← SafeControlGroups.bodyReference_expectation]
  simp only [extendDensity_safe]

theorem extendDensity_energy (security : ℕ) (score : SafePalette security → ℝ) :
    (centerLaw security).l2Sq (extendDensity security score) =
      (ActualControls.bodyReference security).l2Sq score := by
  unfold FiniteDist.l2Sq
  rw [← SafeControlGroups.bodyReference_expectation]
  simp only [extendDensity_safe]

def profile (security : ℕ) (score : SafePalette security → ℝ) (color : Palette security) : ℝ :=
  (centerLaw security).weight color * extendDensity security score color

def translatedProfile (security : ℕ) (root : ℤ) (score : SafePalette security → ℝ) (color : Palette security) : ℝ :=
  profile security score ((shiftEquiv security root).symm color)

theorem profile_mass (security : ℕ) (score : SafePalette security → ℝ) :
    (∑ color, profile security score color) = (ActualControls.bodyReference security).expectation score :=
  extendDensity_mean security score

theorem translatedProfile_mass (security : ℕ) (root : ℤ) (score : SafePalette security → ℝ) :
    (∑ color, translatedProfile security root score color) =
      (ActualControls.bodyReference security).expectation score := by
  change (∑ color, profile security score ((shiftEquiv security root).symm color)) = _
  rw [(shiftEquiv security root).symm.sum_comp, profile_mass]

theorem profile_uniform_energy (security : ℕ) (score : SafePalette security → ℝ) :
    profileSquareNorm (uniformReference security).weight (profile security score) ≤
      4 * (ActualControls.bodyReference security).l2Sq score := by
  rw [← extendDensity_energy]
  unfold profileSquareNorm FiniteDist.l2Sq FiniteDist.expectation
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro color _
  rw [profile, uniformReference_weight]
  simp only [div_eq_mul_inv, one_mul, inv_inv]
  have hheight := centerLaw_height security color
  have hscaled : (Parameters.modulus security : ℝ) * (centerLaw security).weight color ≤ 4 := by
    simpa only [mul_comm] using (le_div_iff₀ (FirstResponse.modulus_pos security)).mp hheight
  have h := mul_le_mul_of_nonneg_right hscaled
    (mul_nonneg ((centerLaw security).nonneg color) (sq_nonneg (extendDensity security score color)))
  nlinarith only [h]

theorem translatedProfile_uniform_energy (security : ℕ) (root : ℤ) (score : SafePalette security → ℝ) :
    profileSquareNorm (uniformReference security).weight (translatedProfile security root score) ≤
      4 * (ActualControls.bodyReference security).l2Sq score := by
  have hsame : profileSquareNorm (uniformReference security).weight (translatedProfile security root score) =
      profileSquareNorm (uniformReference security).weight (profile security score) := by
    unfold profileSquareNorm translatedProfile
    simp only [uniformReference_weight]
    exact (shiftEquiv security root).symm.sum_comp (fun color =>
      profile security score color ^ 2 / (1 / (Parameters.modulus security : ℝ)))
  rw [hsame]
  exact profile_uniform_energy security score

/-- The actual root-translated signed center output, as one finite linear
channel. Its positive reference is the actual safe center law. -/
def bodyChannel (security : ℕ) (root : ℤ) :
    (SafePalette security → ℝ) →ₗ[ℝ] ((Fin 1 → Palette security) → ℝ) where
  toFun score word := translatedProfile security root score (word 0)
  map_add' first second := by
    funext word
    simp only [translatedProfile, profile, map_add, Pi.add_apply, mul_add]
  map_smul' scalar score := by
    funext word
    simp only [translatedProfile, profile, map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem bodyChannel_energy_le (security : ℕ) (root : ℤ) (score : SafePalette security → ℝ)
    (hcentered : (ActualControls.bodyReference security).expectation score = 0)
    (multiple : ℝ) :
    BlockProducts.taggedCoefficientEnergy (uniformReference security) (bodyChannel security root score)
      (Parameters.dimension security) (multiple * BackgroundRates.radius security) ≤
      (32 * normalizedScale security multiple ^ 2) * (ActualControls.bodyReference security).l2Sq score := by
  have h := LocalTensors.singleton_tagged_energy_le (uniformReference security)
    (fun color => by rw [uniformReference_weight]; exact one_div_pos.mpr (FirstResponse.modulus_pos security))
    (translatedProfile security root score) ((translatedProfile_mass security root score).trans hcentered)
    (Parameters.dimension security) (multiple * BackgroundRates.radius security)
  apply h.trans
  have hb := mul_le_mul_of_nonneg_left (translatedProfile_uniform_energy security root score)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) (sq_nonneg (normalizedScale security multiple)))
  exact hb.trans_eq (by ring)

end

end CurrentAFT.OrdinaryPhysicalFock
