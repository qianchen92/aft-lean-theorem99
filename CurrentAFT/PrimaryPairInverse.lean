import CurrentAFT.ProposalPositivity
import CurrentAFT.ActualControls
import AFT.BlockDensity

/-!
# The actual first inverse on a joint two-primary profile

Each inverse is applied to complete fibers of the joint profile. The
energy proof integrates the actual scalar bound under the other reference
coordinate and introduces no maximum-atom or inverse-root-atom factor.
-/

namespace CurrentAFT.PrimaryPairInverse

open AFT DiffuseProfiles ProposalPrimary ActualControls FirstResponse
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw FirstResponse.responseEquiv

abbrev Palette (security : ℕ) := ActualControls.Palette security

def inverseFirst (security : ℕ) (profile : Palette security → Palette security → ℝ) :
    Palette security → Palette security → ℝ :=
  fun first second => (responseEquiv security).symm (fun color => profile color second) first

def inverseSecond (security : ℕ) (profile : Palette security → Palette security → ℝ) :
    Palette security → Palette security → ℝ :=
  fun first second => (responseEquiv security).symm (profile first) second

def responseFirst (security : ℕ) (profile : Palette security → Palette security → ℝ) :
    Palette security → Palette security → ℝ :=
  fun first second => response security (fun color => profile color second) first

def responseSecond (security : ℕ) (profile : Palette security → Palette security → ℝ) :
    Palette security → Palette security → ℝ :=
  fun first second => response security (profile first) second

theorem responseFirst_inverseFirst (security : ℕ) (profile : Palette security → Palette security → ℝ) :
    responseFirst security (inverseFirst security profile) = profile := by
  funext first second
  unfold responseFirst inverseFirst
  rw [← responseEquiv_forward]
  exact congrFun ((responseEquiv security).apply_symm_apply (fun color => profile color second)) first

theorem responseSecond_inverseSecond (security : ℕ) (profile : Palette security → Palette security → ℝ) :
    responseSecond security (inverseSecond security profile) = profile := by
  funext first second
  unfold responseSecond inverseSecond
  rw [← responseEquiv_forward]
  exact congrFun ((responseEquiv security).apply_symm_apply (profile first)) second

def pairCertificateProfile (security : ℕ) (profile : Palette security → Palette security → ℝ) :
    Palette security → Palette security → ℝ :=
  (activation security)⁻¹ ^ 2 • inverseFirst security (inverseSecond security profile)

def pairLeading (security : ℕ) (profile : Palette security → Palette security → ℝ) :
    Palette security → Palette security → ℝ :=
  activation security ^ 2 • responseSecond security (responseFirst security profile)

theorem pairCertificateProfile_leading (security : ℕ) (profile : Palette security → Palette security → ℝ) :
    pairLeading security (pairCertificateProfile security profile) = profile := by
  have ha := (activation_pos security).ne'
  have hfirst (scalar : ℝ) (joint : Palette security → Palette security → ℝ) :
      responseFirst security (scalar • joint) = scalar • responseFirst security joint := by
    funext first second
    exact congrFun (map_smul (response security) scalar (fun color => joint color second)) first
  have hsecond (scalar : ℝ) (joint : Palette security → Palette security → ℝ) :
      responseSecond security (scalar • joint) = scalar • responseSecond security joint := by
    funext first second
    exact congrFun (map_smul (response security) scalar (joint first)) second
  rw [pairLeading, pairCertificateProfile, hfirst, hsecond, responseFirst_inverseFirst,
    responseSecond_inverseSecond, smul_smul]
  have hc : activation security ^ 2 * (activation security)⁻¹ ^ 2 = 1 := by field_simp
  rw [hc, one_smul]

theorem inverse_square_le (security : ℕ) (profile : Palette security → ℝ) :
    profileSquareNorm (primaryLaw security).weight ((responseEquiv security).symm profile) ≤
      4 * profileSquareNorm (primaryLaw security).weight profile := by
  have h := response_inverse_norm_le_two security (primaryLaw security).weight
    (by simpa only [primaryLaw] using primaryProfile_atom_lower security) (primaryLaw security).sum_one profile
  have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  simpa only [mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num,
    Real.sq_sqrt (profileSquareNorm_nonneg _ _ (fun color => (primaryLaw security).nonneg color))] using hs

theorem pairEnergy_first_fibers (security : ℕ) (profile : Palette security → Palette security → ℝ) :
    BlockDensity.pairEnergy (primaryLaw security).weight (primaryLaw security).weight profile =
      ∑ second, profileSquareNorm (primaryLaw security).weight (fun first => profile first second) /
        (primaryLaw security).weight second := by
  unfold BlockDensity.pairEnergy profileSquareNorm
  rw [Finset.sum_comm]
  simp only [Finset.sum_div, div_mul_eq_div_div]

theorem pairEnergy_second_fibers (security : ℕ) (profile : Palette security → Palette security → ℝ) :
    BlockDensity.pairEnergy (primaryLaw security).weight (primaryLaw security).weight profile =
      ∑ first, profileSquareNorm (primaryLaw security).weight (profile first) /
        (primaryLaw security).weight first := by
  unfold BlockDensity.pairEnergy profileSquareNorm
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  rw [mul_comm, div_mul_eq_div_div]

theorem inverseFirst_energy (security : ℕ) (profile : Palette security → Palette security → ℝ) :
    BlockDensity.pairEnergy (primaryLaw security).weight (primaryLaw security).weight (inverseFirst security profile) ≤
      4 * BlockDensity.pairEnergy (primaryLaw security).weight (primaryLaw security).weight profile := by
  rw [pairEnergy_first_fibers, pairEnergy_first_fibers, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro second _
  have h := div_le_div_of_nonneg_right (inverse_square_le security (fun first => profile first second))
    ((primaryLaw security).nonneg second)
  simpa only [inverseFirst, mul_div_assoc] using h

theorem inverseSecond_energy (security : ℕ) (profile : Palette security → Palette security → ℝ) :
    BlockDensity.pairEnergy (primaryLaw security).weight (primaryLaw security).weight (inverseSecond security profile) ≤
      4 * BlockDensity.pairEnergy (primaryLaw security).weight (primaryLaw security).weight profile := by
  rw [pairEnergy_second_fibers, pairEnergy_second_fibers, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro first _
  have h := div_le_div_of_nonneg_right (inverse_square_le security (profile first)) ((primaryLaw security).nonneg first)
  simpa only [inverseSecond, mul_div_assoc] using h

def pairCertificateDensity (security : ℕ) (profile : Palette security → Palette security → ℝ)
    (first second : Palette security) : ℝ :=
  pairCertificateProfile security profile first second /
    ((primaryLaw security).weight first * (primaryLaw security).weight second)

def JointCanonical {Color : Type*} [Fintype Color] (profile : Color → Color → ℝ) : Prop :=
  (∀ first, ∑ second, profile first second = 0) ∧
    (∀ second, ∑ first, profile first second = 0)

theorem inverseFirst_canonical (security : ℕ) (profile : Palette security → Palette security → ℝ)
    (hcanonical : JointCanonical profile) : JointCanonical (inverseFirst security profile) := by
  constructor
  · intro first
    have hsum : (∑ second, (fun color => profile color second)) = 0 := by
      funext color
      simpa only [Finset.sum_apply, Pi.zero_apply] using hcanonical.1 color
    change (∑ second, (responseEquiv security).symm (fun color => profile color second) first) = 0
    rw [← Finset.sum_apply, ← map_sum, hsum, map_zero]
    rfl
  · intro second
    change (∑ first, (responseEquiv security).symm (fun color => profile color second) first) = 0
    rw [response_inverse_preserves_mass, hcanonical.2]

theorem inverseSecond_canonical (security : ℕ) (profile : Palette security → Palette security → ℝ)
    (hcanonical : JointCanonical profile) : JointCanonical (inverseSecond security profile) := by
  constructor
  · intro first
    change (∑ second, (responseEquiv security).symm (profile first) second) = 0
    rw [response_inverse_preserves_mass, hcanonical.1]
  · intro second
    have hsum : (∑ first, profile first) = 0 := by
      funext color
      simpa only [Finset.sum_apply, Pi.zero_apply] using hcanonical.2 color
    change (∑ first, (responseEquiv security).symm (profile first) second) = 0
    rw [← Finset.sum_apply, ← map_sum, hsum, map_zero]
    rfl

theorem pairCertificateProfile_canonical (security : ℕ) (profile : Palette security → Palette security → ℝ)
    (hcanonical : JointCanonical profile) : JointCanonical (pairCertificateProfile security profile) := by
  have h := inverseFirst_canonical security _ (inverseSecond_canonical security profile hcanonical)
  constructor
  · intro first
    simp only [pairCertificateProfile, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, h.1, mul_zero]
  · intro second
    simp only [pairCertificateProfile, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, h.2, mul_zero]

theorem pairCertificateDensity_centered_second (security : ℕ) (profile : Palette security → Palette security → ℝ)
    (hcanonical : JointCanonical profile) (first : Palette security) :
    (∑ second, (primaryLaw security).weight second * pairCertificateDensity security profile first second) = 0 := by
  have hpoint (second : Palette security) :
      (primaryLaw security).weight second * pairCertificateDensity security profile first second =
        pairCertificateProfile security profile first second / (primaryLaw security).weight first := by
    unfold pairCertificateDensity
    field_simp [(primaryReference_positive security first).ne', (primaryReference_positive security second).ne']
  simp only [hpoint, ← Finset.sum_div, (pairCertificateProfile_canonical security profile hcanonical).1, zero_div]

theorem pairCertificateDensity_centered_first (security : ℕ) (profile : Palette security → Palette security → ℝ)
    (hcanonical : JointCanonical profile) (second : Palette security) :
    (∑ first, (primaryLaw security).weight first * pairCertificateDensity security profile first second) = 0 := by
  have hpoint (first : Palette security) :
      (primaryLaw security).weight first * pairCertificateDensity security profile first second =
        pairCertificateProfile security profile first second / (primaryLaw security).weight second := by
    unfold pairCertificateDensity
    field_simp [(primaryReference_positive security first).ne', (primaryReference_positive security second).ne']
  simp only [hpoint, ← Finset.sum_div, (pairCertificateProfile_canonical security profile hcanonical).2, zero_div]

theorem pairCertificateDensity_profile (security : ℕ) (profile : Palette security → Palette security → ℝ)
    (first second : Palette security) :
    (primaryLaw security).weight first * (primaryLaw security).weight second *
      pairCertificateDensity security profile first second = pairCertificateProfile security profile first second := by
  unfold pairCertificateDensity
  exact mul_div_cancel₀ _ (mul_ne_zero (primaryReference_positive security first).ne'
    (primaryReference_positive security second).ne')

theorem pairCertificateDensity_energy (security : ℕ) (profile : Palette security → Palette security → ℝ) :
    (∑ first, ∑ second, (primaryLaw security).weight first * (primaryLaw security).weight second *
      pairCertificateDensity security profile first second ^ 2) ≤
      16 / activation security ^ 4 *
        BlockDensity.pairEnergy (primaryLaw security).weight (primaryLaw security).weight profile := by
  have hpoint (first second : Palette security) :
      (primaryLaw security).weight first * (primaryLaw security).weight second *
          pairCertificateDensity security profile first second ^ 2 =
        ((activation security)⁻¹ ^ 2) ^ 2 *
          (inverseFirst security (inverseSecond security profile) first second ^ 2 /
            ((primaryLaw security).weight first * (primaryLaw security).weight second)) := by
    unfold pairCertificateDensity pairCertificateProfile
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp [(primaryReference_positive security first).ne', (primaryReference_positive security second).ne']
  simp only [hpoint, ← Finset.mul_sum]
  calc
    _ ≤ ((activation security)⁻¹ ^ 2) ^ 2 *
        (4 * BlockDensity.pairEnergy (primaryLaw security).weight (primaryLaw security).weight (inverseSecond security profile)) :=
      mul_le_mul_of_nonneg_left (inverseFirst_energy security _) (sq_nonneg _)
    _ ≤ ((activation security)⁻¹ ^ 2) ^ 2 *
        (4 * (4 * BlockDensity.pairEnergy (primaryLaw security).weight (primaryLaw security).weight profile)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (inverseSecond_energy security profile) (by norm_num)) (sq_nonneg _)
    _ = _ := by ring

theorem pairCertificateDensity_norm (security : ℕ) (profile : Palette security → Palette security → ℝ) :
    Real.sqrt (∑ first, ∑ second, (primaryLaw security).weight first * (primaryLaw security).weight second *
      pairCertificateDensity security profile first second ^ 2) ≤
      (4 / activation security ^ 2) *
        Real.sqrt (BlockDensity.pairEnergy (primaryLaw security).weight (primaryLaw security).weight profile) := by
  have henergy : 0 ≤ BlockDensity.pairEnergy (primaryLaw security).weight (primaryLaw security).weight profile := by
    apply Finset.sum_nonneg
    intro first _
    apply Finset.sum_nonneg
    intro second _
    exact div_nonneg (sq_nonneg _) (mul_nonneg ((primaryLaw security).nonneg _) ((primaryLaw security).nonneg _))
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ 16 / activation security ^ 4 *
        BlockDensity.pairEnergy (primaryLaw security).weight (primaryLaw security).weight profile :=
      pairCertificateDensity_energy security profile
    _ = _ := by rw [mul_pow, Real.sq_sqrt henergy]; ring

end

end CurrentAFT.PrimaryPairInverse
