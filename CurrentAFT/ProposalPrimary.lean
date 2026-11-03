import CurrentAFT.DiffuseProfiles
import CurrentAFT.FirstResponse

/-!
# The current proposal's actual primary numerator

The protected Gaussian roots and scalar are used before forming cyclic
body profiles. The diffuse profiles retain the true integer slices. The
primary numerator is the current two-profile balancing equation, without
the frozen V7 beta repair. Positivity is derived from its scalar deletion
budget; the actual budget is a separate arithmetic expression, not an
assumed operator norm or an assumed calibrated solution.
-/

namespace CurrentAFT.ProposalPrimary

open AFT DiffuseProfiles
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 800000
attribute [local irreducible] Parameters.base DiffuseProfiles.actualProfile
  DiffuseProfiles.signProfile DiffuseProfiles.activation DiffuseProfiles.actualSeedLaw

instance currentModulusNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩

theorem safe_clearance (security : ℕ) :
    4 * Parameters.safeMargin security < Parameters.modulus security := by
  have hb : 1 ≤ Parameters.base security := by have := Parameters.base_ge_two security; omega
  have hc : Parameters.sourceCutoff security ≤ Parameters.base security ^ 64 :=
    Nat.pow_le_pow_right hb (by omega)
  have hp : 0 < Parameters.base security ^ 64 := pow_pos (Parameters.base_pos security) _
  have hq := (Parameters.modulus_bounds security).1
  unfold Parameters.safeMargin
  omega

def safeLaw (security : ℕ) : FiniteDist (Fin (Parameters.modulus security)) :=
  TrimmedSlice.finiteLaw (Parameters.modulus security) (Parameters.safeMargin security) 0
    (by positivity) (by have := safe_clearance security; simp only [abs_zero]; omega)

def safeHeight (security : ℕ) : ℝ :=
  1 / ((Parameters.modulus security : ℝ) - 2 * Parameters.safeMargin security)

theorem safeHeight_pos (security : ℕ) : 0 < safeHeight security := by
  unfold safeHeight
  apply one_div_pos.mpr
  have h := Nat.cast_lt (α := ℝ).mpr (safe_clearance security)
  push_cast at h
  linarith

theorem safeLaw_upper (security : ℕ) (color : Fin (Parameters.modulus security)) :
    (safeLaw security).weight color ≤ safeHeight security := by
  rw [safeLaw, TrimmedSlice.finiteLaw_weight]
  have h := TrimmedSlice.law_le_of_shift_bound (Parameters.modulus security)
    (Parameters.safeMargin security) 0 0 color.val (by simp)
    (by have := safe_clearance security; omega)
  simpa only [safeHeight, Int.cast_natCast, Int.cast_zero, sub_zero] using h

/-- Cyclic translation of the actual finite palette, as an explicit equivalence. -/
noncomputable def shiftEquiv (security : ℕ) (shift : ℤ) :
    Fin (Parameters.modulus security) ≃ Fin (Parameters.modulus security) :=
  (ZMod.finEquiv (Parameters.modulus security)).toEquiv.trans
    ((Equiv.addRight (shift : ZMod (Parameters.modulus security))).trans
      (ZMod.finEquiv (Parameters.modulus security)).toEquiv.symm)

/-- `false` gives the root-convolved safe law; `true` also includes the
independent protected leg/queue scalar convolution. -/
def bodyLaw (security : ℕ) (includeScalar : Bool) :
    FiniteDist (Fin (Parameters.modulus security)) :=
  (actualSeedLaw security).mix fun seed => (safeLaw security).map
    (shiftEquiv security (actualBlur security seed + if includeScalar then actualSecond security seed else 0))

theorem bodyLaw_upper (security : ℕ) (includeScalar : Bool)
    (color : Fin (Parameters.modulus security)) :
    (bodyLaw security includeScalar).weight color ≤ safeHeight security := by
  unfold bodyLaw
  simp only [FiniteDist.mix_weight, FiniteDist.map_equiv_weight]
  calc
    _ ≤ ∑ seed, (actualSeedLaw security).weight seed * safeHeight security :=
      Finset.sum_le_sum fun seed _ =>
        mul_le_mul_of_nonneg_left (safeLaw_upper security _) ((actualSeedLaw security).nonneg seed)
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

def diffuseMean (security : ℕ) : Fin (Parameters.modulus security) → ℝ :=
  fun color => (actualProfile security true color + actualProfile security false color) / 2

theorem diffuseMean_nonneg (security : ℕ) (color : Fin (Parameters.modulus security)) :
    0 ≤ diffuseMean security color := by
  unfold diffuseMean DiffuseProfiles.actualProfile
  apply div_nonneg _ (by norm_num)
  exact add_nonneg (profile_nonneg _ _ _ _ _ _ _ _) (profile_nonneg _ _ _ _ _ _ _ _)

theorem diffuseMean_mass (security : ℕ) : ∑ color, diffuseMean security color = 1 := by
  simp only [diffuseMean, ← Finset.sum_div, Finset.sum_add_distrib, actualProfile_mass]
  norm_num

theorem diffuseMean_upper (security : ℕ) (color : Fin (Parameters.modulus security)) :
    diffuseMean security color ≤
      1 / ((Parameters.modulus security : ℝ) - deletion security) := by
  unfold diffuseMean
  linarith [actualProfile_upper security true color, actualProfile_upper security false color]

def freeMass (security : ℕ) : ℝ :=
  Parameters.bodySize security - Parameters.legCount security - Parameters.modulus security

def markMass (security : ℕ) : ℝ := Parameters.legCount security * activation security

theorem markMass_pos (security : ℕ) : 0 < markMass security := by
  apply mul_pos _ (activation_pos security)
  exact Nat.cast_pos.mpr (by rw [Parameters.legCount_eq]; exact pow_pos (Parameters.base_pos security) _)

theorem population_room (security : ℕ) :
    Parameters.modulus security + 2 * Parameters.legCount security ≤ Parameters.bodySize security := by
  have hb : 1 ≤ Parameters.base security := by have := Parameters.base_ge_two security; omega
  have hq := (Parameters.modulus_bounds security).1
  have hpow : Parameters.base security ^ 32 ≤ Parameters.base security ^ 64 :=
    Nat.pow_le_pow_right hb (by omega)
  have hfour : 4 * Parameters.base security ^ 32 ≤ Parameters.modulus security := by omega
  have hlegs : 4 * Parameters.legCount security ≤ Parameters.bodySize security := by
    have h := Nat.mul_le_mul_right (Parameters.base security ^ 96) hfour
    simpa only [Parameters.legCount_eq, Parameters.bodySize_eq, mul_assoc, ← pow_add] using h
  have htwo : 2 ≤ Parameters.base security ^ 96 := by
    have h := Nat.le_self_pow (show 96 ≠ 0 by omega) (Parameters.base security)
    have := Parameters.base_ge_two security
    omega
  have hbody : 2 * Parameters.modulus security ≤ Parameters.bodySize security := by
    have h := Nat.mul_le_mul_left (Parameters.modulus security) htwo
    simpa only [Parameters.bodySize_eq, mul_comm _ 2] using h
  omega

theorem freeMass_nonneg (security : ℕ) : 0 ≤ freeMass security := by
  have h := Nat.cast_le (α := ℝ).mpr (population_room security)
  push_cast at h
  unfold freeMass
  linarith

/-- The manuscript's actual primary balancing numerator. -/
def primaryProfile (security : ℕ) : Fin (Parameters.modulus security) → ℝ :=
  fun color =>
    ((Parameters.dimension security : ℝ) / Parameters.modulus security -
      (freeMass security + markMass security) * (bodyLaw security false).weight color -
      ((Parameters.legCount security : ℝ) + Parameters.modulus security) *
        (bodyLaw security true).weight color -
      2 * Parameters.legCount security * (1 - activation security) * diffuseMean security color) /
      markMass security

theorem primaryProfile_mass (security : ℕ) : ∑ color, primaryProfile security color = 1 := by
  have hq : (Parameters.modulus security : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Parameters.modulus_spec security).2.ne_zero
  have hmark := (markMass_pos security).ne'
  have ha := (activation_pos security).ne'
  have hl : (Parameters.legCount security : ℝ) ≠ 0 :=
    (mul_ne_zero_iff.mp hmark).1
  simp only [primaryProfile, ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum,
    FiniteDist.sum_one, diffuseMean_mass, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  unfold freeMass markMass
  simp only [Parameters.dimension, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  field_simp [hq, hl, ha]
  ring

/-- A computable scalar deletion budget for the actual numerator. -/
def baselineLoss (security : ℕ) : ℝ :=
  (((Parameters.bodySize security : ℝ) + markMass security) *
      (2 * Parameters.safeMargin security)) /
      (markMass security * ((Parameters.modulus security : ℝ) - 2 * Parameters.safeMargin security)) +
    2 * (1 - activation security) * deletion security /
      (activation security * ((Parameters.modulus security : ℝ) - deletion security))

theorem primaryProfile_lower (security : ℕ) (color : Fin (Parameters.modulus security)) :
    (1 - baselineLoss security) / Parameters.modulus security ≤ primaryProfile security color := by
  have hmark := markMass_pos security
  have hq : (0 : ℝ) < Parameters.modulus security :=
    Nat.cast_pos.mpr (Parameters.modulus_spec security).2.pos
  have hsafe : (0 : ℝ) < Parameters.modulus security - 2 * Parameters.safeMargin security := by
    have h := Nat.cast_lt (α := ℝ).mpr (safe_clearance security)
    push_cast at h
    linarith
  have hdiff : (0 : ℝ) < Parameters.modulus security - deletion security :=
    sub_pos.mpr (Nat.cast_lt.mpr (deletion_clearance security))
  have hc0 : 0 ≤ freeMass security + markMass security :=
    add_nonneg (freeMass_nonneg security) hmark.le
  have hc1 : 0 ≤ (Parameters.legCount security : ℝ) + Parameters.modulus security := by positivity
  have hc2 : 0 ≤ 2 * (Parameters.legCount security : ℝ) * (1 - activation security) := by
    exact mul_nonneg (by positivity) (by linarith [activation_le_half security])
  have h0 := mul_le_mul_of_nonneg_left (bodyLaw_upper security false color) hc0
  have h1 := mul_le_mul_of_nonneg_left (bodyLaw_upper security true color) hc1
  have h2 := mul_le_mul_of_nonneg_left (diffuseMean_upper security color) hc2
  rw [mul_one_div] at h2
  have hidentity : ((1 - baselineLoss security) / Parameters.modulus security) * markMass security =
      (Parameters.dimension security : ℝ) / Parameters.modulus security -
        (freeMass security + markMass security) * safeHeight security -
        ((Parameters.legCount security : ℝ) + Parameters.modulus security) * safeHeight security -
        2 * Parameters.legCount security * (1 - activation security) /
          ((Parameters.modulus security : ℝ) - deletion security) := by
    unfold baselineLoss safeHeight freeMass markMass
    simp only [Parameters.dimension, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    have ha := (activation_pos security).ne'
    have hl : (Parameters.legCount security : ℝ) ≠ 0 :=
      (mul_ne_zero_iff.mp (markMass_pos security).ne').1
    field_simp
    ring
  unfold primaryProfile
  apply (le_div_iff₀ hmark).mpr
  rw [hidentity]
  linarith

end

end CurrentAFT.ProposalPrimary
