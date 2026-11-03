import AFT.BetaGridConditional
import AFT.BetaTypical

/-! # Genuine beta tail bounds survive finite upward grid rounding -/
namespace AFT.BetaReference
open MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem event_mono {State : Type*} [Fintype State] (law : FiniteDist State)
    (first second : State → Prop) (h : ∀ state,first state → second state) :
    law.eventMass first ≤ law.eventMass second := by
  apply Finset.sum_le_sum
  intro state _
  by_cases hf : first state
  · simp only [hf,h state hf,if_true,le_refl]
  · simp only [hf,if_false]
    split_ifs
    · exact law.nonneg state
    · rfl

private theorem event_not {State : Type*} [Fintype State] (law : FiniteDist State) (event : State → Prop) :
    law.eventMass (fun state => ¬event state)=1-law.eventMass event := by
  have he : law.eventMass (fun state => ¬event state)+law.eventMass event=1 := by
    rw [FiniteDist.eventMass,FiniteDist.eventMass,← Finset.sum_add_distrib,← law.sum_one]
    apply Finset.sum_congr rfl
    intro state _
    split_ifs <;> simp_all
  linarith

theorem gridLaw_head_mass (K n M J : ℕ) (hM : 0 < M) (hJM : J ≤ M) :
    (gridLaw K n M hM).eventMass (fun j => j.val < J)=
      ∫ x : ℝ in (0 : ℝ)..(J : ℝ)/M,density K n x := by
  have he := event_not (gridLaw K n M hM) (fun j => J ≤ j.val)
  simp only [not_le] at he
  rw [he,gridLaw_tail_mass K n M J hM hJM]
  have hd : Continuous (density K n) := by unfold density; fun_prop
  have hh := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    (hd.intervalIntegrable 0 ((J : ℝ)/M)) (hd.intervalIntegrable ((J : ℝ)/M) 1)
  rw [density_integral_one] at hh
  linarith

private theorem density_mono_interval (K n : ℕ) (a b c d : ℝ)
    (hc : 0 ≤ c) (hca : c ≤ a) (hab : a ≤ b) (hbd : b ≤ d) (hd : d ≤ 1) :
    (∫ x : ℝ in a..b,density K n x) ≤ ∫ x : ℝ in c..d,density K n x := by
  apply intervalIntegral.integral_mono_interval hca hab hbd
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 : 0 ≤ x := hc.trans hx.1.le
    have hx1 : x ≤ 1 := hx.2.trans hd
    unfold density
    exact mul_nonneg (by positivity) (pow_nonneg (sub_nonneg.mpr hx1) _)
  · exact (by unfold density; fun_prop : Continuous (density K n)).intervalIntegrable _ _

/-- Upward rounding cannot increase a lower-tail probability. -/
theorem gridLaw_lower_tail_le (K n M : ℕ) (hM : 0 < M) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (gridLaw K n M hM).eventMass (fun j => ((j.val+1 : ℕ) : ℝ)/M < a) ≤
      ∫ x : ℝ in (0 : ℝ)..a,density K n x := by
  let J := ⌊(M : ℝ)*a⌋₊
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hJM : J ≤ M := Nat.floor_le_of_le (by nlinarith)
  have hJbound : (J : ℝ)/M ≤ a := (div_le_iff₀ hMp).mpr ((Nat.floor_le (mul_nonneg hMp.le ha)).trans_eq (mul_comm _ _))
  have hm := event_mono (gridLaw K n M hM)
    (fun j => ((j.val+1 : ℕ) : ℝ)/M < a) (fun j => j.val < J) (fun j hj => by
      have hj' : j.val+1 ≤ J := Nat.le_floor (by simpa only [mul_comm] using ((div_lt_iff₀ hMp).mp hj).le)
      omega)
  rw [gridLaw_head_mass K n M J hM hJM] at hm
  exact hm.trans (density_mono_interval K n 0 ((J : ℝ)/M) 0 a le_rfl le_rfl (by positivity) hJbound ha1)

/-- The only upper-tail loss is one grid mesh. -/
theorem gridLaw_upper_tail_le (K n M : ℕ) (hM : 0 < M) (a buffered : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ buffered) (hbuffer : buffered+1/M ≤ a) :
    (gridLaw K n M hM).eventMass (fun j => a < ((j.val+1 : ℕ) : ℝ)/M) ≤
      ∫ x : ℝ in buffered..1,density K n x := by
  let J := ⌊(M : ℝ)*a⌋₊
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hJM : J ≤ M := Nat.floor_le_of_le (by nlinarith)
  have hJbound : buffered ≤ (J : ℝ)/M := by
    apply (le_div_iff₀ hMp).mpr
    have hh := Nat.lt_floor_add_one ((M : ℝ)*a)
    have hbuf := (div_le_iff₀ hMp).mp (show 1/M ≤ a-buffered by linarith)
    dsimp only [J]
    nlinarith
  have hm := event_mono (gridLaw K n M hM)
    (fun j => a < ((j.val+1 : ℕ) : ℝ)/M) (fun j => J ≤ j.val) (fun j hj => by
      by_contra hh
      have hh' : (j.val+1 : ℝ) ≤ J := by exact_mod_cast (by omega : j.val+1 ≤ J)
      have hf := Nat.floor_le (mul_nonneg hMp.le ha)
      have hj' := (lt_div_iff₀ hMp).mp hj
      push_cast at hj'
      dsimp only [J] at hh'
      nlinarith)
  rw [gridLaw_tail_mass K n M J hM hJM] at hm
  exact hm.trans (density_mono_interval K n ((J : ℝ)/M) 1 buffered 1 hb hJbound
    ((div_le_one hMp).mpr (by exact_mod_cast hJM)) le_rfl le_rfl)

/-- Both final typical inequalities hold outside the genuine buffered
continuous-beta tail; no state-space or histogram factor is introduced. -/
theorem gridLaw_typical_rejection_le (K n M : ℕ) (hM : 0 < M)
    (hN : 2*K ≤ K+n+1) (hmesh : (1 : ℝ)/M ≤ (K : ℝ)/(2*(K+n+1 : ℕ))) :
    (gridLaw K n M hM).eventMass (fun j =>
      ¬((K : ℝ)/(2*(K+n+1 : ℕ)) ≤ ((j.val+1 : ℕ) : ℝ)/M ∧
        ((j.val+1 : ℕ) : ℝ)/M ≤ 2*(K : ℝ)/(K+n+1 : ℕ))) ≤
      (∫ x : ℝ in (0 : ℝ)..(K : ℝ)/(2*(K+n+1 : ℕ)),density K n x)+
      (∫ x : ℝ in 3*(K : ℝ)/(2*(K+n+1 : ℕ))..1,density K n x) := by
  have hNp : (0 : ℝ) < (K+n+1 : ℕ) := by positivity
  have hNR : 2*(K : ℝ) ≤ (K+n+1 : ℕ) := by exact_mod_cast hN
  have hlo := gridLaw_lower_tail_le K n M hM ((K : ℝ)/(2*(K+n+1 : ℕ))) (by positivity)
    ((div_le_one (by positivity)).mpr (by linarith))
  have hhi := gridLaw_upper_tail_le K n M hM (2*(K : ℝ)/(K+n+1 : ℕ))
    (3*(K : ℝ)/(2*(K+n+1 : ℕ))) (by positivity) ((div_le_one hNp).mpr hNR) (by positivity)
    (by have he : 3*(K : ℝ)/(2*(K+n+1 : ℕ))+(K : ℝ)/(2*(K+n+1 : ℕ))=2*(K : ℝ)/(K+n+1 : ℕ) := by ring
        linarith)
  have hu : (gridLaw K n M hM).eventMass (fun j =>
      ¬((K : ℝ)/(2*(K+n+1 : ℕ)) ≤ ((j.val+1 : ℕ) : ℝ)/M ∧
        ((j.val+1 : ℕ) : ℝ)/M ≤ 2*(K : ℝ)/(K+n+1 : ℕ))) ≤
      (gridLaw K n M hM).eventMass (fun j => ((j.val+1 : ℕ) : ℝ)/M < (K : ℝ)/(2*(K+n+1 : ℕ)))+
      (gridLaw K n M hM).eventMass (fun j => 2*(K : ℝ)/(K+n+1 : ℕ) < ((j.val+1 : ℕ) : ℝ)/M) := by
    rw [FiniteDist.eventMass,FiniteDist.eventMass,FiniteDist.eventMass,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    simp only [not_and_or,not_le]
    by_cases hl : ((j.val+1 : ℕ) : ℝ)/M < (K : ℝ)/(2*(K+n+1 : ℕ)) <;>
      by_cases hh : 2*(K : ℝ)/(K+n+1 : ℕ) < ((j.val+1 : ℕ) : ℝ)/M <;>
      simp only [hl,hh,or_true,or_false,if_true,if_false,zero_add,add_zero] <;>
      linarith [(gridLaw K n M hM).nonneg j]

  exact hu.trans (add_le_add hlo hhi)

end
end AFT.BetaReference
