import CurrentAFT.ActualBackground
import CurrentAFT.Augmentation
import CurrentAFT.GradedInverseNorm

/-! Exact unit constant and a stable finite inverse for the actual averaged background. -/

namespace CurrentAFT.ActualBackgroundInverse

open AFT GradedControlAlgebra GradedControlNorm GradedControlStability GradedInverse GradedInverseNorm
  Augmentation RoleProduct DiffuseProfiles ProposalPrimary ActualControls BackgroundRates BackgroundFamilies
  BackgroundLinear LegBackgroundFamilies BackgroundScalarZero BackgroundPopulationBounds ActualBackground
open Filter
open scoped BigOperators Classical Topology

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference
  ActualBackground.background ActualBackground.fixedQueueBackground

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

theorem fixedQueueBackground_unit_constant (security order : ℕ) (horder : 2 ≤ order) (queueShift : ℤ) :
    fixedQueueBackground security order horder queueShift (zeroArity order) =
      (1 : ActualFamily security order) (zeroArity order) := by
  let atoms := roleAtoms (primaryLaw security) (bodyReference security) order
    (freeCount security) (Parameters.modulus security) (Parameters.legCount security)
    (freeCertificate security order (by omega)) (translationCertificate security order (by omega) queueShift)
    (completeLegAtom security order horder)
  have hzero (index : RoleIndex (freeCount security) (Parameters.modulus security) (Parameters.legCount security)) :
      atoms index (zeroArity order) = 0 := by
    rcases index with index | index
    · exact freeCertificate_zero security order (by omega)
    · rcases index with index | index
      · exact translationCertificate_zero security order (by omega) queueShift
      · exact completeLegAtom_zero security order horder
  have h := product_unit_constant (primaryLaw security) (bodyReference security) order Finset.univ atoms (fun index _ => hzero index)
  change (∏ index, (1 + roleAtoms (primaryLaw security) (bodyReference security) order
    (freeCount security) (Parameters.modulus security) (Parameters.legCount security)
    (freeCertificate security order (by omega)) (translationCertificate security order (by omega) queueShift)
    (completeLegAtom security order horder) index)) (zeroArity order) = _ at h
  rw [roleAtoms_product] at h
  unfold fixedQueueBackground
  exact h

theorem background_unit_constant (security order : ℕ) (horder : 2 ≤ order) :
    background security order horder (zeroArity order) = (1 : ActualFamily security order) (zeroArity order) := by
  simp only [background, Finset.sum_apply, Pi.smul_apply, fixedQueueBackground_unit_constant]
  rw [← Finset.sum_smul, FiniteDist.sum_one, one_smul]

def inverse (security order : ℕ) (horder : 2 ≤ order) : ActualFamily security order :=
  backgroundInverse (primaryLaw security) (bodyReference security) order (background security order horder)

theorem inverse_mul (security order : ℕ) (horder : 2 ≤ order) :
    inverse security order horder * background security order horder = 1 :=
  backgroundInverse_mul _ _ _ _ (background_unit_constant security order horder)

theorem mul_inverse (security order : ℕ) (horder : 2 ≤ order) :
    background security order horder * inverse security order horder = 1 :=
  mul_backgroundInverse _ _ _ _ (background_unit_constant security order horder)

theorem inverse_unit_constant (security order : ℕ) (horder : 2 ≤ order) :
    inverse security order horder (zeroArity order) = (1 : ActualFamily security order) (zeroArity order) := by
  let augmentation := scalarHom (primaryLaw security) (bodyReference security) order
  have hbackground : augmentation (background security order horder) = 1 := by
    have h := (zero_fiber_eq_iff_scalar_eq (primaryLaw security) (bodyReference security) order _ _).mp
      (background_unit_constant security order horder)
    simpa only [map_one] using h
  apply (zero_fiber_eq_iff_scalar_eq (primaryLaw security) (bodyReference security) order _ _).mpr
  have h := congrArg augmentation (inverse_mul security order horder)
  rw [map_mul, map_one, hbackground, mul_one] at h
  simpa only [map_one] using h

def inverseThreshold (order : ℕ) : ℕ :=
  max (max order numericalThreshold) (2 * order * (order + 1) ^ order * numericalThreshold)

theorem theta_le_half (security order : ℕ) (hsecurity : inverseThreshold order ≤ security) :
    stabilityConstant order / (Parameters.base security : ℝ) ^ 6 ≤ 1 / 2 := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  have hbaseNat : 2 * order * (order + 1) ^ order * numericalThreshold ≤ Parameters.base security := by
    have h := (le_max_right (max order numericalThreshold) (2 * order * (order + 1) ^ order * numericalThreshold)).trans hsecurity
    unfold Parameters.base
    omega
  have hbase : 2 * stabilityConstant order ≤ (Parameters.base security : ℝ) := by
    simpa only [stabilityConstant, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc] using
      Nat.cast_le (α := ℝ).mpr hbaseNat
  have hpower : (Parameters.base security : ℝ) ≤ (Parameters.base security : ℝ) ^ 6 :=
    by simpa only [pow_one] using pow_le_pow_right₀ hb1 (show 1 ≤ 6 by omega)
  apply (div_le_iff₀ (pow_pos hb _)).mpr
  linarith

theorem inverse_bounds (security order : ℕ) (horder : 2 ≤ order) (hsecurity : inverseThreshold order ≤ security) :
    certificateNorm security order (inverse security order horder) ≤ 2 ∧
      certificateNorm security order (inverse security order horder - 1) ≤
        2 * stabilityConstant order / (Parameters.base security : ℝ) ^ 6 := by
  let theta := stabilityConstant order / (Parameters.base security : ℝ) ^ 6
  have htheta : 0 ≤ theta := by unfold theta stabilityConstant; positivity
  have hhalf : theta ≤ 1 / 2 := theta_le_half security order hsecurity
  have hgap : theta < 1 := by linarith
  have hlarge : max order numericalThreshold ≤ security :=
    (le_max_left (max order numericalThreshold) (2 * order * (order + 1) ^ order * numericalThreshold)).trans hsecurity
  have hdefect : certificateNorm security order (1 - background security order horder) ≤ theta := by
    have heq : (1 - background security order horder : ActualFamily security order) = -(background security order horder - 1) := by abel
    rw [heq, show certificateNorm security order (-(background security order horder - 1)) =
      certificateNorm security order (background security order horder - 1) from familyNorm_neg _ _ _ _ _ _]
    exact background_norm_decay security order horder hlarge
  have hp : 0 ≤ primaryFactor security := by unfold primaryFactor; positivity
  have hbdy : 0 ≤ bodyFactor security := by unfold bodyFactor radius; positivity
  constructor
  · exact (backgroundInverse_norm_le (primaryLaw security) (bodyReference security) order
      (primaryFactor security) (bodyFactor security) hp hbdy (background security order horder) theta hgap hdefect).trans
        (by apply (div_le_iff₀ (by linarith : 0 < 1 - theta)).mpr; linarith)
  · apply (backgroundInverse_correction_norm_le (primaryLaw security) (bodyReference security) order
      (primaryFactor security) (bodyFactor security) hp hbdy (background security order horder) theta hgap hdefect).trans
    calc
      _ ≤ theta / (1 / 2) := div_le_div_of_nonneg_left htheta (by norm_num) (by linarith)
      _ = _ := by dsimp only [theta]; ring

theorem inverse_bounds_eventually (order : ℕ) (horder : 2 ≤ order) :
    ∀ᶠ security : ℕ in atTop, certificateNorm security order (inverse security order horder) ≤ 2 ∧
      certificateNorm security order (inverse security order horder - 1) ≤
        2 * stabilityConstant order / (Parameters.base security : ℝ) ^ 6 := by
  filter_upwards [eventually_ge_atTop (inverseThreshold order)] with security hsecurity
  exact inverse_bounds security order horder hsecurity

end

end CurrentAFT.ActualBackgroundInverse
