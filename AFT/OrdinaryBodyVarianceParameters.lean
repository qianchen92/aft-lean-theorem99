import AFT.OrdinaryBodyVariance
import AFT.BodyFringeParameters

/-! # Sharp ordinary-root bounds for the actual calibrated body channel -/
namespace AFT.V7Calibration
open GaussianSource Filter
open scoped BigOperators Classical Topology
noncomputable section

def ordinaryRootDeltaConstant : ℝ := 2*(Real.exp (2*Real.pi)/1000)
def ordinaryRootRowConstant : ℝ := 256*ordinaryRootDeltaConstant+512*ordinaryRootDeltaConstant^2
def ordinaryRootEnergyConstant : ℝ := 768*ordinaryRootDeltaConstant+384*ordinaryRootDeltaConstant^2

theorem ordinary_root_variance_scalar_bounds (C : ℝ) (n : ℕ) (hC : 1 ≤ C) (hn : 2 ≤ n)
    (ha : v7Activation C n ≤ (Real.exp (2*Real.pi)/1000)/(n : ℝ)^(17/4 : ℝ)) :
    64*(1+bodyCompensation n C)^2*bodyCompensation n C+
      512*(bodyCompensation n C)^2*(n : ℝ)^16 ≤ ordinaryRootRowConstant/(n : ℝ)^(137/4 : ℝ) ∧
    64*(1+bodyCompensation n C)^2*bodyCompensation n C*v7RootCutoff n/Parameters.modulus n+
      384*(bodyCompensation n C)^2/(n : ℝ)^22 ≤ ordinaryRootEnergyConstant/(n : ℝ)^(289/4 : ℝ) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn0 : (0 : ℝ) < n := by positivity
  have hd := bodyCompensation_power_bound n C hn ha
  change bodyCompensation n C ≤ ordinaryRootDeltaConstant/(n : ℝ)^(137/4 : ℝ) at hd
  have hdb := bodyCompensation_anchor_bound C n hC (by omega)
  have hd0 := hdb.1
  have hd1 := hdb.2.1
  have hD : 0 ≤ ordinaryRootDeltaConstant := by unfold ordinaryRootDeltaConstant; positivity
  have hs : (1+bodyCompensation n C)^2 ≤ 4 := by nlinarith
  have hsq : (bodyCompensation n C)^2 ≤ (ordinaryRootDeltaConstant/(n : ℝ)^(137/4 : ℝ))^2 :=
    (sq_le_sq₀ hd0 (by positivity)).mpr hd
  have hrowanchor : (bodyCompensation n C)^2*(n : ℝ)^16 ≤
      ordinaryRootDeltaConstant^2/(n : ℝ)^(137/4 : ℝ) := by
    have hp : (n : ℝ)^16 ≤ (n : ℝ)^(137/4 : ℝ) := by
      simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : ((16:ℕ):ℝ) ≤ 137/4)
    calc
      _ ≤ (ordinaryRootDeltaConstant/(n : ℝ)^(137/4 : ℝ))^2*(n : ℝ)^(137/4 : ℝ) :=
        mul_le_mul hsq hp (by positivity) (sq_nonneg _)
      _ = _ := by field_simp
  have hfullanchor : (bodyCompensation n C)^2/(n : ℝ)^22 ≤
      ordinaryRootDeltaConstant^2/(n : ℝ)^(289/4 : ℝ) := by
    have hp : (n : ℝ)^(289/4 : ℝ) ≤ ((n : ℝ)^(137/4 : ℝ))^2*(n : ℝ)^22 := by
      calc
        _ ≤ (n : ℝ)^(181/2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
        _ = _ := by
          rw [← Real.rpow_natCast,← Real.rpow_mul hn0.le,← Real.rpow_natCast,← Real.rpow_add hn0]
          norm_num
    calc
      _ ≤ (ordinaryRootDeltaConstant/(n : ℝ)^(137/4 : ℝ))^2/(n : ℝ)^22 :=
        div_le_div_of_nonneg_right hsq (by positivity)
      _ = ordinaryRootDeltaConstant^2/(((n : ℝ)^(137/4 : ℝ))^2*(n : ℝ)^22) := by ring
      _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hp
  have hq : (n : ℝ)^40 ≤ Parameters.modulus n := by
    exact_mod_cast (by simpa only [Parameters.security_eq n hn] using (Parameters.modulus_bounds n).1)
  have hcut : (v7RootCutoff n : ℝ) ≤ 3*(n : ℝ)^2 := by
    exact_mod_cast (show v7RootCutoff n ≤ 3*n^2 by unfold v7RootCutoff; omega)
  have hcore : bodyCompensation n C*v7RootCutoff n/Parameters.modulus n ≤
      3*ordinaryRootDeltaConstant/(n : ℝ)^(289/4 : ℝ) := by
    calc
      _ ≤ (ordinaryRootDeltaConstant/(n : ℝ)^(137/4 : ℝ))*(3*(n : ℝ)^2)/(n : ℝ)^40 :=
        div_le_div₀ (by positivity) (mul_le_mul hd hcut (by positivity) (by positivity)) (by positivity) hq
      _ = _ := by
        have he : (n : ℝ)^(289/4 : ℝ)=(n : ℝ)^(137/4 : ℝ)*(n : ℝ)^38 := by
          rw [← Real.rpow_natCast,← Real.rpow_add hn0]
          norm_num
        rw [he]
        field_simp
  refine ⟨?_,?_⟩
  · have hfirst : 64*(1+bodyCompensation n C)^2*bodyCompensation n C ≤
        256*ordinaryRootDeltaConstant/(n : ℝ)^(137/4 : ℝ) := by
      have hh := mul_le_mul (mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ) ≤ 64)) hd hd0 (by norm_num)
      exact hh.trans_eq (by ring)
    have hh := add_le_add hfirst (mul_le_mul_of_nonneg_left hrowanchor (by norm_num : (0:ℝ) ≤ 512))
    unfold ordinaryRootRowConstant
    convert hh using 1 <;> ring
  · have hfirst : 64*(1+bodyCompensation n C)^2*bodyCompensation n C*v7RootCutoff n/Parameters.modulus n ≤
        768*ordinaryRootDeltaConstant/(n : ℝ)^(289/4 : ℝ) := by
      have hh := mul_le_mul (mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ) ≤ 64)) hcore
        (by positivity : 0 ≤ bodyCompensation n C*v7RootCutoff n/Parameters.modulus n) (by norm_num)
      convert hh using 1 <;> ring
    have hh := add_le_add hfirst (mul_le_mul_of_nonneg_left hfullanchor (by norm_num : (0:ℝ) ≤ 384))
    unfold ordinaryRootEnergyConstant
    convert hh using 1 <;> ring

theorem actual_root_body_variance_power_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
      (∀ color, rootBodyVariance n (actualBodyCenter C n (beta n)) color /
        (actualPrimaryLaw C n (beta n)).weight color^2 ≤ ordinaryRootRowConstant/(n : ℝ)^(137/4 : ℝ)) ∧
      (∑ color, rootBodyVariance n (actualBodyCenter C n (beta n)) color /
        (actualPrimaryLaw C n (beta n)).weight color) ≤ ordinaryRootEnergyConstant/(n : ℝ)^(289/4 : ℝ) := by
  filter_upwards [actual_root_body_variance_eventually C hC beta hbeta,
    v7Activation_upper_rpow_eventually C hC,eventually_ge_atTop 2] with n hb ha hn
  have hh := ordinary_root_variance_scalar_bounds C n hC hn ha
  exact ⟨fun color => (hb.1 color).trans hh.1,hb.2.trans hh.2⟩


/-- With no leg or queue offset, the actual probability-valued body channel
is exactly the centered integer translation of the calibrated center. -/
theorem actual_ordinary_root_profile_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ root : Window (v7RootCutoff n),
      centeredRootBodyProfile C n (beta n) 0 root = rootCenteredShift n root (actualBodyCenter C n (beta n)) := by
  filter_upwards [actual_shifted_body_law_eventually C hC beta hbeta] with n hb
  have hs (root : Window (v7RootCutoff n)) :
      (actualShiftedBodyLaw C n (beta n) root).weight = integerShiftProfile n (actualBodyCenter C n (beta n)) root := by
    apply (hb root ?_).1
    have hh := abs_le.mpr (Finset.mem_Icc.mp root.property)
    have ht : v7RootCutoff n ≤ maxBodyShift C n := by unfold maxBodyShift; omega
    exact hh.trans (by exact_mod_cast ht)
  intro root
  funext color
  simp only [centeredRootBodyProfile,add_zero]
  simp_rw [hs]
  rfl

/-- The sharp ordinary-root Hilbert and one-fixed operator budgets apply
to the real finite probability channel, for every root input function. -/
theorem actual_root_body_channel_ordinary_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ input : Window (v7RootCutoff n) → ℝ,
      profileSquareNorm (actualPrimaryLaw C n (beta n)).weight (actualRootBodyChannel C n (beta n) 0 input) ≤
        (ordinaryRootEnergyConstant/(n : ℝ)^(289/4 : ℝ))*(bodyRootReference n).l2Sq input ∧
      (∀ color,(actualRootBodyChannel C n (beta n) 0 input color/(actualPrimaryLaw C n (beta n)).weight color)^2 ≤
        (ordinaryRootRowConstant/(n : ℝ)^(137/4 : ℝ))*(bodyRootReference n).l2Sq input) ∧
      (∑ color,actualRootBodyChannel C n (beta n) 0 input color)=0 := by
  filter_upwards [actual_root_body_variance_power_eventually C hC beta hbeta,
    actual_ordinary_root_profile_eventually C hC beta hbeta] with n hb he input
  have hE := FiniteDist.l2Sq_nonneg (bodyRootReference n) input
  refine ⟨?_,?_,rootProfileChannel_mass_zero _ _ (centeredRootBodyProfile_mass C n (beta n) 0) input⟩
  · apply (rootProfileChannel_energy_le (bodyRootReference n) (actualPrimaryLaw C n (beta n)).weight
      (centeredRootBodyProfile C n (beta n) 0) (FiniteDist.nonneg _) input).trans
    apply mul_le_mul_of_nonneg_right _ hE
    simp_rw [he]
    rw [← rootBodyVariance_profile_energy]
    exact hb.2
  · intro color
    apply (rootProfileChannel_row_square_le (bodyRootReference n) (actualPrimaryLaw C n (beta n)).weight
      (centeredRootBodyProfile C n (beta n) 0) input color).trans
    apply mul_le_mul_of_nonneg_right _ hE
    simp_rw [he]
    exact hb.1 color

end
end AFT.V7Calibration
