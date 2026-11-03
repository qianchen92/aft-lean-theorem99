import CurrentAFT.CycleDensity
import CurrentAFT.DiffuseProfiles
import CurrentAFT.IntegerCycleDensity

/-! # Protected-cycle root bound at the current public parameters -/

namespace CurrentAFT.CycleSelections

open AFT
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- The root-tag scale used in the current manuscript. -/
def currentRootTag (security : ℕ) : ℝ :=
  (Parameters.base security : ℝ) / (Parameters.scale security : ℝ) ^ 10

/-- Actual integer-difference support width at the chosen edge cutoff. -/
theorem current_root_support_width (security : ℕ) :
    4 * DiffuseProfiles.edgeCutoff security + 1 ≤ 2 * Parameters.base security ^ 2 := by
  unfold DiffuseProfiles.edgeCutoff Parameters.sourceCutoff
  have hdivision := Nat.div_mul_le_self (Parameters.base security ^ 2 - 1) 2
  have hbase := Parameters.base_ge_two security
  have hpower : 1 ≤ Parameters.base security ^ 2 := one_le_pow₀ (by omega)
  omega

attribute [local irreducible] Parameters.base Parameters.scale Parameters.bodySize
  Parameters.sourceWidth Parameters.sourceCutoff DiffuseProfiles.edgeCutoff

/-- The current body is larger than the root-support width at exactly the
root-tag scale, without a modulus-asymptotic assumption. -/
theorem current_root_ratio (security : ℕ) :
    Real.sqrt (4 * DiffuseProfiles.edgeCutoff security + 1 : ℝ) /
      Real.sqrt (Parameters.bodySize security : ℝ) ≤ currentRootTag security := by
  have hbase : (0 : ℝ) < Parameters.base security := by exact_mod_cast Parameters.base_pos security
  have hscale : (0 : ℝ) < Parameters.scale security := by
    unfold Parameters.scale
    exact_mod_cast pow_pos (Parameters.base_pos security) 8
  have hmodulus : (0 : ℝ) < Parameters.modulus security := by
    exact_mod_cast (Parameters.modulus_spec security).2.pos
  have hbody : (0 : ℝ) < Parameters.bodySize security := by
    unfold Parameters.bodySize
    push_cast
    positivity
  have hmodulusLower : 65536 * (Parameters.scale security : ℝ) ^ 8 ≤ Parameters.modulus security := by
    exact_mod_cast (Parameters.modulus_spec security).1
  have hwidth : (4 * DiffuseProfiles.edgeCutoff security + 1 : ℝ) ≤
      2 * (Parameters.base security : ℝ) ^ 2 := by exact_mod_cast current_root_support_width security
  have hbodyLower : 2 * (Parameters.scale security : ℝ) ^ 20 ≤ Parameters.bodySize security := by
    have h := mul_le_mul_of_nonneg_right hmodulusLower
      (pow_nonneg hscale.le 12)
    have hp : (Parameters.scale security : ℝ) ^ 8 * (Parameters.scale security : ℝ) ^ 12 =
        (Parameters.scale security : ℝ) ^ 20 := by rw [← pow_add]
    rw [mul_assoc, hp] at h
    rw [Parameters.bodySize, Nat.cast_mul, Nat.cast_pow]
    nlinarith [pow_nonneg hscale.le 20]
  have hsqrtBody := Real.sq_sqrt hbody.le
  have hsqrtWidth := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 4 * DiffuseProfiles.edgeCutoff security + 1)
  have hscaled : (4 * DiffuseProfiles.edgeCutoff security + 1 : ℝ) *
      ((Parameters.scale security : ℝ) ^ 10) ^ 2 ≤
        (Parameters.base security : ℝ) ^ 2 * Parameters.bodySize security := by
    rw [← pow_mul]
    calc
      _ ≤ (2 * (Parameters.base security : ℝ) ^ 2) * (Parameters.scale security : ℝ) ^ 20 :=
        mul_le_mul_of_nonneg_right hwidth (by positivity)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hbodyLower (sq_nonneg (Parameters.base security : ℝ))]
  have hcross : Real.sqrt (4 * DiffuseProfiles.edgeCutoff security + 1 : ℝ) *
      (Parameters.scale security : ℝ) ^ 10 ≤
        Parameters.base security * Real.sqrt (Parameters.bodySize security : ℝ) := by
    have hfirst : 0 ≤ Real.sqrt (4 * DiffuseProfiles.edgeCutoff security + 1 : ℝ) *
        (Parameters.scale security : ℝ) ^ 10 := by positivity
    have hsecond : 0 ≤ (Parameters.base security : ℝ) * Real.sqrt (Parameters.bodySize security : ℝ) := by positivity
    nlinarith
  unfold currentRootTag
  apply (div_le_div_iff₀ (Real.sqrt_pos.mpr hbody) (pow_pos hscale 10)).mpr
  exact hcross

/-- The explicit threshold `security ≥ 2D` simultaneously supplies enough
body vertices for every fixed order at most `D`. -/
theorem current_body_fixed_orders (maximum security : ℕ) (hsecurity : 2 * maximum ≤ security) :
    ∀ order ≤ maximum, 2 * order ≤ Parameters.bodySize security := by
  intro order horder
  have hbaseBody : Parameters.base security ≤ Parameters.bodySize security := by
    have hp : Parameters.base security ≤ Parameters.base security ^ 96 :=
      Nat.le_self_pow (by decide) _
    have hm : 1 ≤ Parameters.modulus security := (Parameters.modulus_spec security).2.one_le
    rw [Parameters.bodySize_eq]
    exact hp.trans (by simpa using Nat.mul_le_mul_right (Parameters.base security ^ 96) hm)
  have hsecurityBase : security ≤ Parameters.base security := by simp [Parameters.base]
  omega

/-- Actual current protected residue-root density at every admissible
fixed order, bounded by the manuscript's root tag. -/
theorem current_averaged_centered_norm_le (security order : ℕ)
    [NeZero (Parameters.modulus security)] (horder : 1 ≤ order)
    (hbody : 2 * order ≤ Parameters.bodySize security) :
    Real.sqrt ((FiniteDist.independent (fun _ : Fin order =>
      gaussianRootReference (Parameters.sourceWidth security) (DiffuseProfiles.edgeCutoff security)
        (Parameters.modulus security))).l2Sq
      (centeredRootDensity
        (averagedSelectedLaw (Parameters.bodySize security) order (Parameters.modulus security)
          (by omega) (DiffuseProfiles.edgeLaw security)
          (fun scalar => ((scalar : ℤ) : ZMod (Parameters.modulus security))))
        (fun _ => gaussianRootReference (Parameters.sourceWidth security) (DiffuseProfiles.edgeCutoff security)
          (Parameters.modulus security)))) ≤
      (((2 * (order + 1) : ℕ) : ℝ) ^ order) * currentRootTag security ^ order := by
  apply (averaged_centered_norm_le_tag (Parameters.bodySize security) order (Parameters.modulus security)
    (DiffuseProfiles.edgeCutoff security) (Parameters.sourceWidth security) horder hbody).trans
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) (current_root_ratio security) order) (by positivity)

/-- A concrete common threshold for every fixed root order up to `D`. -/
theorem current_root_threshold (maximum : ℕ) :
    ∃ threshold, ∀ security ≥ threshold, ∀ order, 1 ≤ order → order ≤ maximum →
      2 * order ≤ Parameters.bodySize security := by
  exact ⟨2 * maximum, fun security hsecurity order _ horder =>
    current_body_fixed_orders maximum security hsecurity order horder⟩

/-- The true integer root support never wraps at the current modulus. -/
theorem current_root_no_wrap (security : ℕ) :
    4 * DiffuseProfiles.edgeCutoff security < Parameters.modulus security := by
  have hbase := Parameters.base_ge_two security
  have hp : Parameters.base security ^ 2 ≤ Parameters.base security ^ 64 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hone : 1 ≤ Parameters.base security ^ 64 := one_le_pow₀ (by omega)
  have hwidth := current_root_support_width security
  have hmodulus := (Parameters.modulus_bounds security).1
  omega

/-- The chosen root tag is exactly the indicated negative base power. -/
theorem currentRootTag_eq (security : ℕ) :
    currentRootTag security = 1 / (Parameters.base security : ℝ) ^ 79 := by
  have hb : (0 : ℝ) < Parameters.base security := by exact_mod_cast Parameters.base_pos security
  rw [currentRootTag, Parameters.scale, Nat.cast_pow, ← pow_mul]
  field_simp

/-- Current pure parameter budget used by the rooted-transfer estimates. -/
theorem current_lambda_scale_budget (security : ℕ) :
    (Parameters.base security : ℝ) ^ 3 / (Parameters.scale security : ℝ) ^ 2 =
      1 / (Parameters.base security : ℝ) ^ 13 := by
  have hb : (0 : ℝ) < Parameters.base security := by exact_mod_cast Parameters.base_pos security
  rw [Parameters.scale, Nat.cast_pow, ← pow_mul]
  field_simp

/-- Actual norm, with primality supplying the residue alphabet internally. -/
def currentCenteredRootNorm (security order : ℕ) (horder : order ≤ Parameters.bodySize security) : ℝ := by
  letI : NeZero (Parameters.modulus security) := ⟨(Parameters.modulus_spec security).2.ne_zero⟩
  exact Real.sqrt ((FiniteDist.independent (fun _ : Fin order =>
    gaussianRootReference (Parameters.sourceWidth security) (DiffuseProfiles.edgeCutoff security)
      (Parameters.modulus security))).l2Sq
    (centeredRootDensity
      (averagedSelectedLaw (Parameters.bodySize security) order (Parameters.modulus security)
        horder (DiffuseProfiles.edgeLaw security)
        (fun scalar => ((scalar : ℤ) : ZMod (Parameters.modulus security))))
      (fun _ => gaussianRootReference (Parameters.sourceWidth security) (DiffuseProfiles.edgeCutoff security)
        (Parameters.modulus security))))

/-- One explicit parameter threshold simultaneously proves the actual
root-norm estimate for all positive fixed orders at most `D`. -/
theorem current_all_fixed_orders (maximum : ℕ) :
    ∃ threshold, ∀ security ≥ threshold, ∀ order, 1 ≤ order → order ≤ maximum →
      ∃ hroom : order ≤ Parameters.bodySize security,
        currentCenteredRootNorm security order hroom ≤
          (((2 * (order + 1) : ℕ) : ℝ) ^ order) * currentRootTag security ^ order := by
  refine ⟨2 * maximum, ?_⟩
  intro security hsecurity order hpositive horder
  have hbody := current_body_fixed_orders maximum security hsecurity order horder
  refine ⟨by omega, ?_⟩
  letI : NeZero (Parameters.modulus security) := ⟨(Parameters.modulus_spec security).2.ne_zero⟩
  exact current_averaged_centered_norm_le security order hpositive hbody

/-- The actual protected integer-root norm on its exact difference window. -/
def currentIntegerRootNorm (security order : ℕ) (horder : order ≤ Parameters.bodySize security) : ℝ :=
  Real.sqrt ((FiniteDist.independent (fun _ : Fin order =>
    integerRootReference (Parameters.sourceWidth security) (DiffuseProfiles.edgeCutoff security))).l2Sq
    (centeredRootDensity
      (integerAveragedSelectedLaw (Parameters.bodySize security) order (DiffuseProfiles.edgeCutoff security)
        (Parameters.sourceWidth security) horder)
      (fun _ => integerRootReference (Parameters.sourceWidth security) (DiffuseProfiles.edgeCutoff security))))

/-- The exact support bijection proves the current integer norm estimate
from the already established residue estimate without any loss. -/
theorem current_integer_root_norm_le (security order : ℕ) (hpositive : 1 ≤ order)
    (hbody : 2 * order ≤ Parameters.bodySize security) :
    currentIntegerRootNorm security order (by omega) ≤
      (((2 * (order + 1) : ℕ) : ℝ) ^ order) * currentRootTag security ^ order := by
  letI : NeZero (Parameters.modulus security) := ⟨(Parameters.modulus_spec security).2.ne_zero⟩
  unfold currentIntegerRootNorm
  rw [← integer_centered_energy_eq_residue (Parameters.bodySize security) order
    (DiffuseProfiles.edgeCutoff security) (Parameters.modulus security)
    (Parameters.sourceWidth security) (by omega) (current_root_no_wrap security)]
  exact current_averaged_centered_norm_le security order hpositive hbody

/-- One common explicit threshold proves the full integer-root conclusion
simultaneously at every positive fixed order at most `D`. -/
theorem current_integer_all_fixed_orders (maximum : ℕ) :
    ∃ threshold, ∀ security ≥ threshold, ∀ order, 1 ≤ order → order ≤ maximum →
      ∃ hroom : order ≤ Parameters.bodySize security,
        currentIntegerRootNorm security order hroom ≤
          (((2 * (order + 1) : ℕ) : ℝ) ^ order) * currentRootTag security ^ order := by
  refine ⟨2 * maximum, ?_⟩
  intro security hsecurity order hpositive horder
  have hbody := current_body_fixed_orders maximum security hsecurity order horder
  exact ⟨by omega, current_integer_root_norm_le security order hpositive hbody⟩

end

end CurrentAFT.CycleSelections
