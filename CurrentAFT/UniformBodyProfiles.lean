import CurrentAFT.LocalReferenceEnergy
import CurrentAFT.BackgroundCertificates
import AFT.ProfileHilbert

/-! # Actual uniform-reference Hilbert deviations of every pre-root body role -/

namespace CurrentAFT.UniformBodyProfiles

open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy BackgroundCertificates FringeCertificate
open scoped BigOperators Classical

noncomputable section

abbrev Palette (security : ℕ) := LocalReferenceEnergy.Palette security

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.safeLaw
  ProposalPrimary.centerLaw LocalReferenceEnergy.uniformReference

def uniformVector (security : ℕ) (profile : Palette security → ℝ) : EuclideanSpace ℝ (Palette security) :=
  ProfileHilbert.whiten (uniformReference security).weight
    (fun color => profile color - (uniformReference security).weight color)

theorem uniformVector_norm_sq (security : ℕ) (profile : Palette security → ℝ) :
    ‖uniformVector security profile‖ ^ 2 =
      (Parameters.modulus security : ℝ) * ∑ color,
        (profile color - (Parameters.modulus security : ℝ)⁻¹) ^ 2 := by
  rw [uniformVector, ProfileHilbert.whiten_norm_sq _ _ (uniformReference security).nonneg]
  unfold profileSquareNorm
  simp only [uniformReference_weight, one_div, div_inv_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro color _
  ring

theorem uniformVector_law_norm_sq (security : ℕ) (law : FiniteDist (Palette security)) :
    ‖uniformVector security law.weight‖ ^ 2 =
      (Parameters.modulus security : ℝ) * ∑ color, law.weight color ^ 2 - 1 := by
  have hq := FirstResponse.modulus_pos security
  rw [uniformVector_norm_sq, Finset.mul_sum]
  have hpoint (color : Palette security) :
      (Parameters.modulus security : ℝ) * (law.weight color - (Parameters.modulus security : ℝ)⁻¹) ^ 2 =
      (Parameters.modulus security : ℝ) * law.weight color ^ 2 - 2 * law.weight color +
        (Parameters.modulus security : ℝ)⁻¹ := by field_simp; ring
  simp_rw [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [law.sum_one]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- The safe interval's exact chi-square deviation is its actual fringe
mass, rather than an estimate from its largest atom. -/
theorem safe_uniform_energy (security : ℕ) :
    ‖uniformVector security (safeLaw security).weight‖ ^ 2 = fringeMass security := by
  rw [uniformVector_law_norm_sq, fringeMass_height]
  congr 1
  have hsquare (color : Palette security) : (safeLaw security).weight color ^ 2 =
      safeHeight security * (safeLaw security).weight color := by
    rw [safeLaw_weight]
    split_ifs <;> ring
  simp_rw [hsquare, ← Finset.mul_sum, FiniteDist.sum_one, mul_one]

theorem safe_uniform_norm_le (security : ℕ) :
    ‖uniformVector security (safeLaw security).weight‖ ≤ 1 / (Parameters.base security : ℝ) ^ 31 := by
  have hb := FirstResponse.base_pos security
  have hsquare := (safe_uniform_energy security).trans_le (fringeMass_decay security)
  have hpower : (1 / (Parameters.base security : ℝ) ^ 31) ^ 2 =
      1 / (Parameters.base security : ℝ) ^ 62 := by ring
  have hnonneg := norm_nonneg (uniformVector security (safeLaw security).weight)
  have hright : 0 ≤ 1 / (Parameters.base security : ℝ) ^ 31 := by positivity
  nlinarith

theorem bodyCertificate_uniform_energy (security : ℕ) :
    ‖ProfileHilbert.whiten (uniformReference security).weight (bodyCertificateProfile security)‖ ^ 2 ≤
      16384 / (Parameters.base security : ℝ) ^ 62 := by
  rw [ProfileHilbert.whiten_norm_sq _ _ (uniformReference security).nonneg]
  have hpoint (color : Palette security) :
      bodyCertificateProfile security color ^ 2 / (uniformReference security).weight color ≤
        4 * ((centerLaw security).weight color * bodyCertificateDensity security color ^ 2) := by
    have hheight := centerLaw_height security color
    have hq := FirstResponse.modulus_pos security
    have hprofile := congrFun (bodyCertificateDensity_profile security) color
    rw [← hprofile, uniformReference_weight]
    simp only [div_eq_mul_inv, one_mul, inv_inv]
    have hscaled : (Parameters.modulus security : ℝ) * (centerLaw security).weight color ≤ 4 := by
      simpa only [mul_comm] using (le_div_iff₀ hq).mp hheight
    have h := mul_le_mul_of_nonneg_right hscaled
      (mul_nonneg ((centerLaw security).nonneg color) (sq_nonneg (bodyCertificateDensity security color)))
    convert h using 1
    ring
  unfold profileSquareNorm
  apply (Finset.sum_le_sum fun color _ => hpoint color).trans
  rw [← Finset.mul_sum]
  have h := mul_le_mul_of_nonneg_left (bodyCertificateDensity_square_decay security) (by norm_num : (0 : ℝ) ≤ 4)
  exact h.trans_eq (by ring)

theorem bodyCertificate_uniform_norm (security : ℕ) :
    ‖ProfileHilbert.whiten (uniformReference security).weight (bodyCertificateProfile security)‖ ≤
      128 / (Parameters.base security : ℝ) ^ 31 := by
  have h := bodyCertificate_uniform_energy security
  have hright : 0 ≤ 128 / (Parameters.base security : ℝ) ^ 31 := by
    have := FirstResponse.base_pos security; positivity
  have hsquare : (128 / (Parameters.base security : ℝ) ^ 31) ^ 2 =
      16384 / (Parameters.base security : ℝ) ^ 62 := by ring
  nlinarith [norm_nonneg (ProfileHilbert.whiten (uniformReference security).weight (bodyCertificateProfile security))]

/-- The actual compensated center has the same small uniform-reference
deviation scale as the true safe law. -/
theorem center_uniform_norm_le (security : ℕ) :
    ‖uniformVector security (centerLaw security).weight‖ ≤ 129 / (Parameters.base security : ℝ) ^ 31 := by
  have hsplit : uniformVector security (centerLaw security).weight =
      uniformVector security (safeLaw security).weight +
        ProfileHilbert.whiten (uniformReference security).weight (bodyCertificateProfile security) := by
    have hprofile : (fun color => (centerLaw security).weight color - (uniformReference security).weight color) =
        (fun color => (safeLaw security).weight color - (uniformReference security).weight color) +
          bodyCertificateProfile security := by
      funext color
      simp only [Pi.add_apply, bodyCertificateProfile]
      ring
    unfold uniformVector
    rw [hprofile, map_add]
  rw [hsplit]
  exact (norm_add_le _ _).trans ((add_le_add (safe_uniform_norm_le security)
    (bodyCertificate_uniform_norm security)).trans_eq (by ring))

/-- Every deterministic cyclic translation is an exact isometry in the
uniform profile Hilbert space, including atoms crossing the palette end. -/
theorem uniformVector_map_equiv_norm (security : ℕ) (law : FiniteDist (Palette security))
    (permutation : Equiv.Perm (Palette security)) :
    ‖uniformVector security (law.map permutation).weight‖ = ‖uniformVector security law.weight‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [uniformVector_norm_sq, uniformVector_norm_sq]
  simp only [FiniteDist.map_equiv_weight]
  congr 1
  exact permutation.symm.sum_comp (fun color =>
    (law.weight color - (Parameters.modulus security : ℝ)⁻¹) ^ 2)

theorem uniformVector_mix_norm_le {Choice : Type*} [Fintype Choice] (security : ℕ)
    (law : FiniteDist Choice) (channel : Choice → FiniteDist (Palette security))
    (bound : ℝ) (hchannel : ∀ choice, ‖uniformVector security (channel choice).weight‖ ≤ bound) :
    ‖uniformVector security (law.mix channel).weight‖ ≤ bound := by
  rw [uniformVector, ProfileHilbert.whiten_mixture_centered]
  exact FiniteConcentration.vectorMean_norm_le law _ bound hchannel

inductive BodyRole
  | free
  | attachment
  | queue

/-- Actual center law before the cyclic root is added. The attachment
averages its own protected leg scalar, and the common queue is fixed. -/
def preRootLaw (security : ℕ) (role : BodyRole) (queue : ℤ) : FiniteDist (Palette security) :=
  match role with
  | .free => centerLaw security
  | .attachment => (scalarLaw security).mix (fun scalar =>
      (safeLaw security).map (shiftEquiv security scalar.val))
  | .queue => (safeLaw security).map (shiftEquiv security queue)

def deviation (security : ℕ) : ℝ := 129 / (Parameters.base security : ℝ) ^ 31

theorem deviation_nonneg (security : ℕ) : 0 ≤ deviation security := by
  unfold deviation
  have := FirstResponse.base_pos security
  positivity

/-- All three genuine pre-root body roles share the same actual small
uniform-reference deviation, uniformly in the fixed common queue. -/
theorem preRootLaw_norm_le (security : ℕ) (role : BodyRole) (queue : ℤ) :
    ‖uniformVector security (preRootLaw security role queue).weight‖ ≤ deviation security := by
  have hsafe : ‖uniformVector security (safeLaw security).weight‖ ≤ deviation security := by
    apply (safe_uniform_norm_le security).trans
    exact div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 129) (by positivity)
  cases role with
  | free => exact center_uniform_norm_le security
  | attachment =>
    apply uniformVector_mix_norm_le
    intro scalar
    rw [uniformVector_map_equiv_norm]
    exact hsafe
  | queue =>
    rw [preRootLaw, uniformVector_map_equiv_norm]
    exact hsafe

end

end CurrentAFT.UniformBodyProfiles
