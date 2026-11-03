import CurrentAFT.CurrentSourceProtection
import AFT.Negligible

/-! # Negligibility of the actual complete-source protection error

The body includes the independent public closure edge, and the queue has
only one Gaussian input. The estimate concerns the whole product source
before any public Markov channel is applied.
-/
namespace CurrentAFT.CurrentSourceTail

open AFT GaussianSource CurrentSourceProtection
open Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1200000

def envelope (security : ℕ) : ℝ :=
  (1 + 4 * (Parameters.base security : ℝ) ^ 2 / Real.pi) *
    Real.exp (-(Real.pi / 8) * (Parameters.base security : ℝ) ^ 2)

theorem envelope_nonneg (security : ℕ) : 0 ≤ envelope security := by
  unfold envelope
  positivity

/-- A single common tail envelope covers both actual protected windows. -/
theorem clipping_le_envelope (security cutoff : ℕ)
    (hcutoff : (Parameters.base security : ℝ) ^ 2 / 2 ≤ (cutoff + 1 : ℕ)) :
    clippingProbability (width security) (cutoff + 1 : ℕ) (width_pos security) ≤
      envelope security := by
  have hb : (0 : ℝ) < Parameters.base security := by
    exact_mod_cast Parameters.base_pos security
  have hsquare := pow_le_pow_left₀ (by positivity :
    (0 : ℝ) ≤ (Parameters.base security : ℝ) ^ 2 / 2) hcutoff 2
  have hratio : Real.pi / 8 * (Parameters.base security : ℝ) ^ 2 ≤
      Real.pi * (cutoff + 1 : ℕ) ^ 2 / (2 * (Parameters.base security : ℝ) ^ 2) := by
    apply (le_div_iff₀ (by positivity :
      (0 : ℝ) < 2 * (Parameters.base security : ℝ) ^ 2)).mpr
    calc
      _ = Real.pi * ((Parameters.base security : ℝ) ^ 2 / 2) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsquare Real.pi_pos.le
  have hexponent :
      -Real.pi * (cutoff + 1 : ℕ) ^ 2 / (2 * (Parameters.base security : ℝ) ^ 2) ≤
        -(Real.pi / 8) * (Parameters.base security : ℝ) ^ 2 := by
    calc
      _ = -(Real.pi * (cutoff + 1 : ℕ) ^ 2 /
        (2 * (Parameters.base security : ℝ) ^ 2)) := by ring
      _ ≤ -(Real.pi / 8 * (Parameters.base security : ℝ) ^ 2) := neg_le_neg hratio
      _ = _ := by ring
  have htail := clippingProbability_le (width security) (cutoff + 1 : ℕ)
    (width_pos security) (by positivity)
  change clippingProbability _ _ _ ≤
    Real.exp (-Real.pi * (cutoff + 1 : ℕ) ^ 2 / (2 * (Parameters.base security : ℝ) ^ 2)) *
      (1 + 4 * (Parameters.base security : ℝ) ^ 2 / Real.pi) at htail
  exact htail.trans ((mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexponent)
    (by positivity)).trans_eq (by unfold envelope; ring))

theorem body_cutoff_lower (security : ℕ) :
    (Parameters.base security : ℝ) ^ 2 / 2 ≤
      (DiffuseProfiles.edgeCutoff security + 1 : ℕ) := by
  have hn : Parameters.sourceCutoff security ≤ 2 * (DiffuseProfiles.edgeCutoff security + 1) := by
    unfold DiffuseProfiles.edgeCutoff
    omega
  have hr : (Parameters.base security : ℝ) ^ 2 ≤
      2 * (DiffuseProfiles.edgeCutoff security + 1 : ℕ) := by
    exact_mod_cast hn
  linarith

theorem aux_cutoff_lower (security : ℕ) :
    (Parameters.base security : ℝ) ^ 2 / 2 ≤
      (Parameters.sourceCutoff security - 1 + 1 : ℕ) := by
  have hpositive := sourceCutoff_pos security
  have heq : Parameters.sourceCutoff security - 1 + 1 = Parameters.sourceCutoff security := by omega
  rw [heq]
  change (Parameters.base security : ℝ) ^ 2 / 2 ≤ ((Parameters.base security) ^ 2 : ℕ)
  push_cast
  nlinarith [sq_nonneg (Parameters.base security : ℝ)]

theorem budget_le_count_envelope (security : ℕ) :
    budget security ≤ sourceCount security * envelope security := by
  unfold budget
  have hb := mul_le_mul_of_nonneg_left
    (clipping_le_envelope security (DiffuseProfiles.edgeCutoff security) (body_cutoff_lower security))
    (Nat.cast_nonneg (Parameters.bodySize security) : (0 : ℝ) ≤ Parameters.bodySize security)
  have ha := mul_le_mul_of_nonneg_left
    (clipping_le_envelope security (Parameters.sourceCutoff security - 1) (aux_cutoff_lower security))
    (Nat.cast_nonneg (Parameters.legCount security * 2 + 1) :
      (0 : ℝ) ≤ (Parameters.legCount security * 2 + 1 : ℕ))
  exact (add_le_add hb ha).trans_eq (by unfold sourceCount; push_cast; ring)

theorem sourceCount_eq_dimension (security : ℕ) :
    sourceCount security = Parameters.dimension security + 1 := by
  unfold sourceCount Parameters.dimension
  omega

theorem sourceCount_upper (security : ℕ) :
    sourceCount security ≤ 131075 * Parameters.base security ^ 160 := by
  have hd := (Parameters.dimension_bounds security).2
  have hp : 1 ≤ Parameters.base security ^ 160 :=
    Nat.one_le_pow _ _ (by have := Parameters.base_ge_two security; omega)
  rw [sourceCount_eq_dimension]
  omega

theorem budget_polynomial_exponential (security : ℕ) :
    budget security ≤ (131075 * (1 + 4 / Real.pi)) *
      (Parameters.base security : ℝ) ^ 162 *
        Real.exp (-(Real.pi / 8) * (Parameters.base security : ℝ) ^ 2) := by
  have hb : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  have hsquare : (1 : ℝ) ≤ (Parameters.base security : ℝ) ^ 2 := one_le_pow₀ hb
  have hpref : 1 + 4 * (Parameters.base security : ℝ) ^ 2 / Real.pi ≤
      (1 + 4 / Real.pi) * (Parameters.base security : ℝ) ^ 2 := by
    calc
      _ ≤ (Parameters.base security : ℝ) ^ 2 +
        4 * (Parameters.base security : ℝ) ^ 2 / Real.pi := add_le_add hsquare le_rfl
      _ = _ := by ring
  have hc : (sourceCount security : ℝ) ≤ 131075 * (Parameters.base security : ℝ) ^ 160 := by
    exact_mod_cast sourceCount_upper security
  calc
    _ ≤ (sourceCount security : ℝ) * envelope security := budget_le_count_envelope security
    _ ≤ (131075 * (Parameters.base security : ℝ) ^ 160) * envelope security :=
      mul_le_mul_of_nonneg_right hc (envelope_nonneg security)
    _ ≤ (131075 * (Parameters.base security : ℝ) ^ 160) *
        (((1 + 4 / Real.pi) * (Parameters.base security : ℝ) ^ 2) *
          Real.exp (-(Real.pi / 8) * (Parameters.base security : ℝ) ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right hpref (Real.exp_pos _).le
    _ = _ := by rw [show (162 : ℕ) = 160 + 2 by rfl, pow_add]; ring

theorem budget_negligible : AFT.Negligible budget := by
  have hmain := (AFT.negligible_polynomial_stretched_exponential
    (131075 * (1 + 4 / Real.pi)) 162 2 (Real.pi / 8)
    (by positivity) (by norm_num) (by positivity)).comp_add 2
  apply hmain.of_eventually_le
  filter_upwards [] with security
  rw [abs_of_nonneg (budget_nonneg security), abs_of_nonneg (by positivity)]
  simpa only [Parameters.base, Nat.cast_add, Nat.cast_ofNat, Real.rpow_two] using
    budget_polynomial_exponential security

end
end CurrentAFT.CurrentSourceTail
