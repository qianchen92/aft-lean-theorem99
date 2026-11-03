import CurrentAFT.CycleMeanMGF
import CurrentAFT.UniformBodyProfiles
import CurrentAFT.BackgroundRates
import CurrentAFT.NormalizedMeanAlgebra

/-!
# Actual current-family protected-cycle mean exponential moment

All profile and source inputs below are the actual current center,
safe-interval, protected scalar, and protected edge laws. The fixed role
assignment, independent body permutation, and common queue are arbitrary.
The sufficient security threshold may depend on the fixed exponential
constant, and the resulting bound is uniform in all those fixed data.
-/

namespace CurrentAFT.ActualCycleMeanMGF

open AFT FiniteConcentration DiffuseProfiles ProposalPrimary UniformBodyProfiles
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] CycleMeanMGF.classicalFinDecidableEq
attribute [local irreducible] Parameters.base Parameters.scale
  BackgroundRates.radius UniformBodyProfiles.deviation

abbrev Edge (security : ℕ) := GaussianSource.Window (edgeCutoff security)
abbrev BodyIndex (security : ℕ) := Fin (Parameters.bodySize security)
abbrev ProfileSpace (security : ℕ) := EuclideanSpace ℝ (UniformBodyProfiles.Palette security)

/-- Actual translated body-profile deviation at one latent pair. -/
def response (security : ℕ) (roles : BodyIndex security → BodyRole) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security)) (vertex : BodyIndex security)
    (pair : Edge security × Edge security) : ProfileSpace security :=
  uniformVector security ((preRootLaw security (roles (permutation vertex)) queue).map
    (shiftEquiv security (pair.2.val - pair.1.val))).weight

theorem response_norm_le (security : ℕ) (roles : BodyIndex security → BodyRole) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security)) (vertex : BodyIndex security)
    (pair : Edge security × Edge security) :
    ‖response security roles queue permutation vertex pair‖ ≤ deviation security := by
  rw [response, uniformVector_map_equiv_norm]
  exact preRootLaw_norm_le security _ queue

def realizedResponse (security : ℕ) (roles : BodyIndex security → BodyRole) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security) :
    BodyIndex security → ProfileSpace security :=
  fun vertex => response security roles queue permutation vertex
    (latent ((finRotate (Parameters.bodySize security)).symm vertex), latent vertex)

def meanResponse (security : ℕ) (roles : BodyIndex security → BodyRole) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security)) : BodyIndex security → ProfileSpace security :=
  fun vertex => vectorMean ((edgeLaw security).prod (edgeLaw security))
    (response security roles queue permutation vertex)

/-- The true normalized root fluctuation, with each local profile centered
by its actual pair-law average and with the complete closing cycle. -/
def fluctuation (security : ℕ) (roles : BodyIndex security → BodyRole) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security) :
    ProfileSpace security :=
  NormalizedMeanAlgebra.euclideanCenteredSum (NormalizedMeanAlgebra.normalizationScale security)
    (realizedResponse security roles queue permutation latent)
    (meanResponse security roles queue permutation)

/-- Literal finite Gaussian expectation, with the dependent product-space
enumeration fixed before the current population parameters are inserted. -/
def squareMoment (security : ℕ) (roles : BodyIndex security → BodyRole) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security)) (parameter : ℝ) : ℝ :=
  CycleMeanMGF.normalizedCycleMoment (Parameters.bodySize security) (Parameters.dimension security)
    (edgeLaw security) (response security roles queue permutation) parameter

theorem bodySize_ge_two (security : ℕ) : 2 ≤ Parameters.bodySize security := by
  have hq := (Parameters.modulus_spec security).2.two_le
  have hpower : 0 < Parameters.base security ^ 96 := pow_pos (Parameters.base_pos security) _
  have hmul := Nat.le_mul_of_pos_right (Parameters.modulus security) hpower
  rw [← Parameters.bodySize_eq] at hmul
  omega

theorem bodySize_le_dimension (security : ℕ) : Parameters.bodySize security ≤ Parameters.dimension security := by
  rw [Parameters.dimension]
  omega

/-- Actual protected Gaussian cycle MGF, with only a numerical scalar
smallness condition. The profile norm bound is fully instantiated. -/
theorem fluctuation_square_mgf (security : ℕ) (roles : BodyIndex security → BodyRole) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security)) (parameter : ℝ) (hparameter : 0 ≤ parameter)
    (hsmall : 576 * parameter * deviation security ^ 2 < 1) :
    squareMoment security roles queue permutation parameter ≤
      Real.exp (72 * parameter * deviation security ^ 2) *
        (Real.sqrt (1 - 576 * parameter * deviation security ^ 2))⁻¹ := by
  exact CycleMeanMGF.normalizedCycleMoment_le (Hilbert := ProfileSpace security)
    (Parameters.bodySize security) (Parameters.dimension security) (bodySize_ge_two security)
    (bodySize_le_dimension security) (edgeLaw security) (response security roles queue permutation)
    (deviation security) parameter (deviation_nonneg security) hparameter
    (response_norm_le security roles queue permutation) hsmall

/-- The actual radius/profile product decays with sixty spare base powers;
no conditional moment or full Fock estimate is assumed here. -/
theorem radius_deviation_budget (security : ℕ) (constant : ℝ) (hconstant : 0 ≤ constant) :
    (constant * BackgroundRates.radius security ^ 2) * deviation security ^ 2 ≤
      16641 * constant / (Parameters.base security : ℝ) ^ 60 := by
  have hb := FirstResponse.base_pos security
  have hradius : 0 ≤ BackgroundRates.radius security := by
    unfold BackgroundRates.radius
    exact Real.rpow_nonneg hb.le _
  have hsquare := pow_le_pow_left₀ hradius (BackgroundRates.radius_le_base security) 2
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsquare hconstant)
    (sq_nonneg (deviation security))
  apply h.trans_eq
  rw [deviation]
  field_simp
  ring

/-- Every fixed multiple of the current radius has a uniform actual
cycle-mean square-exponential moment for all sufficiently large security.
The bound covers arbitrary fixed roles, queue values, and permutations. -/
theorem current_cycle_mean_mgf_eventually (constant : ℝ) (hconstant : 0 ≤ constant) :
    ∃ threshold : ℕ, ∀ security ≥ threshold,
      ∀ roles : BodyIndex security → BodyRole, ∀ queue : ℤ,
        ∀ permutation : Equiv.Perm (BodyIndex security),
          squareMoment security roles queue permutation
            (constant * BackgroundRates.radius security ^ 2) ≤ 2 * Real.exp 1 := by
  refine ⟨Nat.ceil (1152 * 16641 * constant) + 1, ?_⟩
  intro security hsecurity roles queue permutation
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  have hthreshold : 1152 * 16641 * constant ≤ (Parameters.base security : ℝ) := by
    have hceil := Nat.le_ceil (1152 * 16641 * constant)
    have hn : Nat.ceil (1152 * 16641 * constant) ≤ Parameters.base security := by
      have hbase : security ≤ Parameters.base security := by rw [Parameters.base]; omega
      omega
    exact hceil.trans (by exact_mod_cast hn)
  have hpower : (Parameters.base security : ℝ) ≤ (Parameters.base security : ℝ) ^ 60 :=
    le_self_pow₀ hb1 (by decide)
  have hlarge : 1152 * 16641 * constant ≤ (Parameters.base security : ℝ) ^ 60 := hthreshold.trans hpower
  have hparameter : 0 ≤ constant * BackgroundRates.radius security ^ 2 := mul_nonneg hconstant (sq_nonneg _)
  have hbudget : 576 * ((constant * BackgroundRates.radius security ^ 2) * deviation security ^ 2) ≤ 1 / 2 := by
    apply (mul_le_mul_of_nonneg_left (radius_deviation_budget security constant hconstant) (by norm_num : (0 : ℝ) ≤ 576)).trans
    calc
      _ = (576 * 16641 * constant) / (Parameters.base security : ℝ) ^ 60 := by ring
      _ ≤ 1 / 2 := (div_le_iff₀ (pow_pos hb 60)).mpr (by nlinarith [hlarge])
  have h := fluctuation_square_mgf security roles queue permutation
    (constant * BackgroundRates.radius security ^ 2) hparameter (by nlinarith [hbudget])
  apply h.trans
  have hexp : Real.exp (72 * (constant * BackgroundRates.radius security ^ 2) * deviation security ^ 2) ≤
      Real.exp 1 := Real.exp_le_exp.mpr (by nlinarith [hbudget])
  have hdenominator : (1 / 2 : ℝ) ≤ 1 - 576 * (constant * BackgroundRates.radius security ^ 2) * deviation security ^ 2 := by
    nlinarith [hbudget]
  have hsqrt : (1 / 2 : ℝ) ≤ Real.sqrt (1 - 576 * (constant * BackgroundRates.radius security ^ 2) * deviation security ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [hdenominator]
  have hinv : (Real.sqrt (1 - 576 * (constant * BackgroundRates.radius security ^ 2) * deviation security ^ 2))⁻¹ ≤ 2 := by
    apply (inv_le_iff_one_le_mul₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hsqrt)).mpr
    linarith
  exact (mul_le_mul hexp hinv (inv_nonneg.mpr (Real.sqrt_nonneg _)) (Real.exp_nonneg _)).trans_eq (by ring)

end

end CurrentAFT.ActualCycleMeanMGF
