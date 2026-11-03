import AFT.IndependentPositiveActivity
import AFT.ActualOutputChannels

/-! # The actual positive singleton factor for a reserved body -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration Filter SafeConvolution
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance independentBodyPositiveFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance independentBodyPositiveSubtypeDecEq (s : Finset (Fin 1)) : DecidableEq s := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- The real calibrated center followed by its independent conditional-root
marginal. The common queue is absent at the reserved input positions. -/
def independentBodyPositiveProfile (C : ℝ) (n : ℕ) (beta : ℝ)
    (output : Fin (Parameters.modulus n)) : ℝ :=
  ∑ input,(actualBodyLaw C n beta).weight input*actualBodyChannel n input output

def independentBodyPositiveMass (C : ℝ) (n : ℕ) (beta : ℝ)
    (word : Fin 1 → Fin (Parameters.modulus n)) : ℝ :=
  independentBodyPositiveProfile C n beta (word 0)

theorem independentBodyPositiveProfile_nonneg (C : ℝ) (n : ℕ) (beta : ℝ) (output) :
    0 ≤ independentBodyPositiveProfile C n beta output :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (FiniteDist.nonneg _ _) (actualBodyChannel_nonneg _ _ _)

theorem independentBodyPositiveProfile_mass (C : ℝ) (n : ℕ) (beta : ℝ) :
    (∑ output,independentBodyPositiveProfile C n beta output)=1 := by
  unfold independentBodyPositiveProfile
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum,actualBodyChannel_mass,mul_one,FiniteDist.sum_one]

theorem independentBodyPositiveMass_mass (C : ℝ) (n : ℕ) (beta : ℝ) :
    (∑ word,independentBodyPositiveMass C n beta word)=1 := by
  rw [← (Equiv.funUnique (Fin 1) (Fin (Parameters.modulus n))).symm.sum_comp]
  simpa only [independentBodyPositiveMass,Equiv.funUnique_symm_apply,uniqueElim_const] using
    independentBodyPositiveProfile_mass C n beta

theorem independentBodyPositiveMass_marginal (C : ℝ) (n : ℕ) (beta : ℝ) (slot : Fin 1) (color) :
    (∑ word,if word slot=color then independentBodyPositiveMass C n beta word else 0)=
      independentBodyPositiveProfile C n beta color := by
  rw [← (Equiv.funUnique (Fin 1) (Fin (Parameters.modulus n))).symm.sum_comp]
  simp only [independentBodyPositiveMass,Equiv.funUnique_symm_apply,uniqueElim_const]
  simp

/-- The bound follows from the true center height and the exact convolution
with a probability; it does not replace the calibrated center by the core. -/
theorem independentBodyPositiveProfile_bound_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ color,independentBodyPositiveProfile C n (beta n) color ≤
      16*(actualPrimaryLaw C n (beta n)).weight color := by
  filter_upwards [actual_body_center_probability_eventually C hC beta hbeta,
    actual_reference_laws_eventually C hC beta hbeta,
    actual_primary_law_quarter_lower_eventually C hC beta hbeta]
    with n hb hl hp color
  have hP (input) : (actualBodyLaw C n (beta n)).weight input ≤ 4/(Parameters.modulus n : ℝ) := by
    rw [hl.2.1]
    have hh := (actualCoreLaw_bounds n).1 input
    have he := (hb.2.1 input).2
    simp only [div_eq_mul_inv] at hh ⊢
    linarith
  have hconv : independentBodyPositiveProfile C n (beta n) color ≤ 4/(Parameters.modulus n : ℝ) := by
    unfold independentBodyPositiveProfile
    rw [actualBodyChannel_profile,convolution_apply]
    calc
      _ ≤ ∑ shift,(actualRootLaw n).weight shift*(4/(Parameters.modulus n : ℝ)) :=
        Finset.sum_le_sum fun shift _ => mul_le_mul_of_nonneg_left (hP _) (FiniteDist.nonneg _ _)
      _ = _ := by rw [← Finset.sum_mul,FiniteDist.sum_one,one_mul]
  apply hconv.trans
  convert mul_le_mul_of_nonneg_left (hp color) (by norm_num : (0:ℝ)≤16) using 1
  ring

theorem independentBodyPositive_activity_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ selected : Finset (Fin 1),selected ≠ ∅ →
    ∀ rate : ℝ,0 ≤ rate → rate ≤ 1 →
    MixedKernel.activity (fun _ : selected => rate)
      (fun _ : selected => actualPrimaryLaw C n (beta n))
      (LocalTensors.referenceRestrictedComponent (fun _ : Fin 1 => actualPrimaryLaw C n (beta n))
        (fun _ : Fin 1 => actualReferenceLaw C n (beta n))
        (independentBodyPositiveMass C n (beta n)) selected) ≤ 48*rate := by
  filter_upwards [independentBodyPositiveProfile_bound_eventually C hC beta hbeta,
    actual_reference_laws_eventually C hC beta hbeta,
    actual_primary_probability_eventually C hC beta hbeta,
    actual_reference_primary_density_eventually C hC beta hbeta]
    with n hb hl hp hr selected hs rate hrate hrate1
  have hcard : selected.card=1 := by
    have hle := Finset.card_le_univ selected
    have hpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
    simp only [Fintype.card_fin] at hle
    omega
  have hp0 (color) : 0 < (actualPrimaryLaw C n (beta n)).weight color := by rw [hl.1]; exact hp.1 color
  have hcompare (slot : Fin 1) (color) : (actualReferenceLaw C n (beta n)).weight color ≤
      8*(actualPrimaryLaw C n (beta n)).weight color := by
    have hh := (div_le_iff₀ (hp.1 color)).mp ((le_abs_self _).trans (hr.1 color))
    simpa only [hl.1,hl.2.2] using hh
  have hm (slot : Fin 1) (color) :
      (∑ word,if word slot=color then independentBodyPositiveMass C n (beta n) word else 0) ≤
        16*(actualPrimaryLaw C n (beta n)).weight color := by
    rw [independentBodyPositiveMass_marginal]
    exact hb color
  have hh := LocalTensors.referenceRestrictedComponent_linear_activity_le
    (fun _ : Fin 1 => actualPrimaryLaw C n (beta n))
    (fun _ : Fin 1 => actualReferenceLaw C n (beta n)) (fun _ => hp0)
    (independentBodyPositiveMass C n (beta n))
    (fun word => independentBodyPositiveProfile_nonneg C n (beta n) (word 0))
    (independentBodyPositiveMass_mass C n (beta n)) 8 16 rate (by norm_num) (by norm_num)
    hrate hrate1 hcompare hm selected hcard
  exact hh.trans_eq (by ring)

end
end AFT.V7Calibration
