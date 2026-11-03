import AFT.BetaGridHistogram
import AFT.BetaGridTails
import AFT.BetaFiniteSampler
import AFT.RootErrorAlgebra

/-! # Computable beta grid precision and legality thresholds for V7 -/
namespace AFT.V7Calibration
open GaussianSource BetaReference Filter MeasureTheory
open scoped BigOperators Topology

/-- A rational cutoff computed from the public security parameter alone. -/
def betaGridStart (n : ℕ) : ℕ := ⌈((2^n : ℕ) : ℚ)/(n : ℚ)^32⌉₊

noncomputable section

def betaGridCutoff (n : ℕ) : ℝ := (betaGridStart n : ℝ)/(2^n : ℕ)
def betaGridMesh (n : ℕ) : ℝ := 1/(2^n : ℕ)
def betaGridRejectedMass (n : ℕ) : ℝ :=
  ∫ x : ℝ in (0 : ℝ)..betaGridCutoff n,
    density (Parameters.legs n) (Parameters.dimension n-Parameters.legs n-1) x

theorem betaGridMesh_negligible : Negligible betaGridMesh := by
  have hh := negligible_geometric_population 1 (1/2) (by norm_num) (by norm_num) (by norm_num)
    (fun n => n) (Eventually.of_forall fun _ => le_rfl)
  have he : betaGridMesh=(fun n => (1 : ℝ)*(1/2 : ℝ)^n) := by
    funext n
    simp only [betaGridMesh,one_mul,Nat.cast_pow,Nat.cast_ofNat]
    rw [div_pow,one_pow]
  rw [he]
  exact hh

theorem betaGridCutoff_bounds (n : ℕ) (hn : 1 ≤ n) :
    1/(n : ℝ)^32 ≤ betaGridCutoff n ∧ betaGridCutoff n ≤ 1/(n : ℝ)^32+betaGridMesh n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hMp : (0 : ℝ) < (2^n : ℕ) := by positivity
  have hlo : ((2^n : ℕ) : ℝ)/(n : ℝ)^32 ≤ (betaGridStart n : ℝ) := by
    have hh := (Rat.cast_le (K:=ℝ)).mpr (Nat.le_ceil (((2^n : ℕ) : ℚ)/(n : ℚ)^32))
    simpa only [Rat.cast_div,Rat.cast_pow,Rat.cast_natCast,betaGridStart] using hh
  have hhi : (betaGridStart n : ℝ) ≤ ((2^n : ℕ) : ℝ)/(n : ℝ)^32+1 := by
    have hh := (Rat.cast_le (K:=ℝ)).mpr (Nat.ceil_lt_add_one (show (0 : ℚ) ≤ ((2^n : ℕ) : ℚ)/(n : ℚ)^32 by positivity)).le
    simpa only [Rat.cast_add,Rat.cast_one,Rat.cast_div,Rat.cast_pow,Rat.cast_natCast,betaGridStart] using hh
  constructor
  · unfold betaGridCutoff
    apply (le_div_iff₀ hMp).mpr
    simpa only [div_eq_mul_inv,one_mul,mul_one,mul_comm] using hlo
  · unfold betaGridCutoff betaGridMesh
    apply (div_le_iff₀ hMp).mpr
    calc
      _ ≤ ((2^n : ℕ) : ℝ)/(n : ℝ)^32+1 := hhi
      _ = _ := by field_simp

theorem beta_grid_legal_eventually (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ n in atTop,0 < betaGridStart n ∧ betaGridStart n < 2^n ∧
      actualBetaCutoff C n ≤ betaGridCutoff n ∧
      1/(n : ℝ)^32 ≤ betaGridCutoff n ∧ betaGridCutoff n ≤ 2/(n : ℝ)^32 := by
  filter_upwards [actual_beta_cutoff_eventually C hC,betaGridMesh_negligible 32,eventually_ge_atTop 40]
    with n hc hm hn
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
  have hM : (0 : ℝ) < (2^n : ℕ) := by positivity
  have hb := betaGridCutoff_bounds n hn1
  rw [abs_of_nonneg (by unfold betaGridMesh; positivity)] at hm
  have hu : betaGridCutoff n ≤ 2/(n : ℝ)^32 := hb.2.trans ((add_le_add (le_refl (1/(n : ℝ)^32)) hm).trans_eq (show 1/(n : ℝ)^32+1/(n : ℝ)^32=2/(n : ℝ)^32 by ring))
  have hp : 0 < betaGridCutoff n := (by positivity : (0 : ℝ) < 1/(n : ℝ)^32).trans_le hb.1
  have hsmall : 2/(n : ℝ)^32 < 1 := by
    apply (div_lt_one (by positivity)).mpr
    exact (by norm_num : (2 : ℝ) < 2^32).trans_le (pow_le_pow_left₀ (by norm_num) hn2 32)
  have hlegal : actualBetaCutoff C n ≤ betaGridCutoff n := by
    apply hc.2.2.1.trans
    apply le_trans _ hb.1
    apply (div_le_div_iff₀ (pow_pos hn0 33) (pow_pos hn0 32)).mpr
    have hn40 : (40 : ℝ) ≤ n := by exact_mod_cast hn
    rw [pow_succ]
    nlinarith [mul_le_mul_of_nonneg_right hn40 (pow_nonneg hn0.le 32)]
  refine ⟨?_,?_,hlegal,hb.1,hu⟩
  · have hnum : (0 : ℝ) < betaGridStart n := (div_pos_iff.mp hp).elim And.left
        (fun h => False.elim ((not_lt_of_ge hM.le) h.2))
    exact_mod_cast hnum
  · exact_mod_cast ((div_lt_one hM).mp (hu.trans_lt hsmall))

theorem beta_grid_normalized_cutoff_eventually (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ n in atTop,Real.exp 1*(Parameters.dimension n : ℝ)*betaGridCutoff n/(Parameters.legs n+1 : ℕ) ≤ 1/(n : ℝ) := by
  filter_upwards [beta_grid_legal_eventually C hC,eventually_ge_atTop (max 2 ⌈4*Real.exp 1⌉₊)] with n hc hn
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hN : (Parameters.dimension n : ℝ) ≤ 2*(n : ℝ)^60 := by exact_mod_cast
    (by simpa only [Parameters.security_eq n hn2] using (Parameters.dimension_bounds n).2)
  have hK : (n : ℝ)^30 ≤ (Parameters.legs n+1 : ℕ) := by
    simp only [Parameters.legs,Parameters.security_eq n hn2,Nat.cast_add,Nat.cast_pow,Nat.cast_one]
    linarith
  have hconstant : 4*Real.exp 1 ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hn)
  calc
    _ ≤ (Real.exp 1*(2*(n : ℝ)^60)*(2/(n : ℝ)^32))/(n : ℝ)^30 :=
      div_le_div₀ (by positivity)
        (mul_le_mul (mul_le_mul_of_nonneg_left hN (by positivity)) hc.2.2.2.2
          (by unfold betaGridCutoff; positivity) (by positivity)) (by positivity) hK
    _ = 4*Real.exp 1/(n : ℝ)^2 := by field_simp; ring
    _ ≤ (n : ℝ)/(n : ℝ)^2 := div_le_div_of_nonneg_right hconstant (by positivity)
    _ = _ := by field_simp

theorem betaGridRejectedMass_negligible : Negligible betaGridRejectedMass := by
  have hpop : ∀ᶠ n in atTop,n ≤ Parameters.legs n+1 := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hh : n ≤ n^30 := by simpa only [pow_one] using pow_le_pow_right₀ (by omega : 1 ≤ n) (by omega : 1 ≤ 30)
    simpa only [Parameters.legs,Parameters.security_eq n hn] using hh.trans (Nat.le_succ _)
  have hh := negligible_growing_power 0 (fun n : ℕ => 1/(n : ℝ)) (fun n => Parameters.legs n+1)
    (Eventually.of_forall fun n => by positivity) (Eventually.of_forall fun _ => le_rfl) hpop
  apply hh.of_eventually_le
  filter_upwards [beta_grid_legal_eventually 1 le_rfl,beta_grid_normalized_cutoff_eventually 1 le_rfl] with n hc hnorm
  have hpop : Parameters.legs n+(Parameters.dimension n-Parameters.legs n-1)+1=Parameters.dimension n := by
    have hi := Parameters.population_identity n
    have hb := Parameters.bodies_positive n
    omega
  have hcut0 : 0 ≤ betaGridCutoff n := by unfold betaGridCutoff; positivity
  have hcut1 : betaGridCutoff n ≤ 1 := (div_le_one (by positivity)).mpr (by exact_mod_cast hc.2.1.le)
  have hnonneg : 0 ≤ betaGridRejectedMass n := by
    apply intervalIntegral.integral_nonneg hcut0
    intro x hx
    have hx0 := hx.1
    have hx1 := hx.2.trans hcut1
    unfold density
    exact mul_nonneg (by positivity) (pow_nonneg (sub_nonneg.mpr hx1) _)
  rw [abs_of_nonneg hnonneg,abs_of_nonneg (by positivity),pow_zero,one_mul]
  apply lower_tail_le_geometric _ _ _ _ hcut0 hcut1
  simpa only [hpop] using hnorm

end
end AFT.V7Calibration
