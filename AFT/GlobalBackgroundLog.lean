import AFT.GlobalMeanOutput

/-! # The actual global background logarithm as a finite literal input table -/

namespace AFT.V7Calibration
open GaussianSource Filter RepresentedPolynomial
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance globalBackgroundLogFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance globalBackgroundLogSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _

def blockBackgroundLinear (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (index : blockIndex n) (queue : ℤ) : Table (InputSeed (Fin (Parameters.modulus n))) :=
  match index with
  | .inl _ => localBackgroundLinear C n beta queue operator
  | .inr _ => inversePrimaryTable (actualPrimaryLaw C n beta) (actualBodyLaw C n beta)
      (v7Activation C n) operator (bodyMeanTable C n beta queue)

def blockBackgroundError (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (index : blockIndex n) (queue : ℤ) : Table (InputSeed (Fin (Parameters.modulus n))) :=
  match index with
  | .inl _ => localBackgroundError C n beta queue operator
  | .inr _ => blockBackgroundLinear C n beta operator index queue

def actualBackgroundLog (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (sample : Window (queueCutoff n) × Equiv.Perm (blockIndex n)) (cutoff : ℕ) :
    Table (InputSeed (Fin (Parameters.modulus n))) :=
  inversePrimaryTable (actualPrimaryLaw C n beta) (actualBodyLaw C n beta)
      (v7Activation C n) operator (globalMeanTable C n beta sample)+
    ∑ index, (logarithm (blockBackgroundError C n beta operator index (actualQueueShifts n sample index)) cutoff-
      blockBackgroundLinear C n beta operator index (actualQueueShifts n sample index))

def backgroundLogConstant (C : ℝ) : ℝ :=
  8*bodyMeanInputConstant+localHigherConstant C+2*localErrorConstant C^2+4*bodyMeanInputConstant^2

theorem blockBackgroundLinear_hasOrder (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (index : blockIndex n) (queue : ℤ) :
    HasOrder (fun seed => seed.primaryOrder+seed.bodyOrder) 1 (blockBackgroundLinear C n beta operator index queue) := by
  cases index with
  | inl _ => exact localBackgroundLinear_hasOrder C n beta queue operator
  | inr _ => exact inversePrimaryTable_hasOrder _ _ _ _ _ _ (bodyMeanTable_hasOrder C n beta queue)

theorem blockBackgroundError_hasOrder (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (index : blockIndex n) (queue : ℤ) :
    HasOrder (fun seed => seed.primaryOrder+seed.bodyOrder) 1 (blockBackgroundError C n beta operator index queue) := by
  cases index with
  | inl _ =>
    exact hasOrder_add _ _ _ _ (localBackgroundLinear_hasOrder C n beta queue operator)
      (hasOrder_mono _ 1 2 _ (localBackgroundHigher_hasOrder C n beta queue operator) (by decide))
  | inr _ => exact blockBackgroundLinear_hasOrder C n beta operator _ queue

theorem actualBackgroundLog_hasOrder (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (sample : Window (queueCutoff n) × Equiv.Perm (blockIndex n)) (cutoff : ℕ) :
    HasOrder (fun seed => seed.primaryOrder+seed.bodyOrder) 1 (actualBackgroundLog C n beta operator sample cutoff) := by
  apply hasOrder_add
  · exact inversePrimaryTable_hasOrder _ _ _ _ _ _ (globalMeanTable_hasOrder C n beta sample)
  · apply hasOrder_sum
    intro index _
    exact hasOrder_sub _ _ _ _ (hasOrder_logarithm _ _ _ (blockBackgroundError_hasOrder C n beta operator index _))
      (blockBackgroundLinear_hasOrder C n beta operator index _)

/-- Summing the specified local linear tables gives the literal population
linear table before replacing it by the smaller queue-centered certificate. -/
theorem blockBackgroundLinear_sum (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (sample : Window (queueCutoff n) × Equiv.Perm (blockIndex n)) :
    (∑ index,blockBackgroundLinear C n beta operator index (actualQueueShifts n sample index)) =
      inversePrimaryTable (actualPrimaryLaw C n beta) (actualBodyLaw C n beta)
        (v7Activation C n) operator (globalLinearTable C n beta sample) := by
  let T := inversePrimaryTable (actualPrimaryLaw C n beta) (actualBodyLaw C n beta) (v7Activation C n) operator
  have hc (x : ℝ) : T (MvPolynomial.C x) = MvPolynomial.C x := T.commutes x
  change _ = T _
  rw [globalLinearTable,map_add,map_sum,map_mul,hc]
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp only [blockBackgroundLinear,localBackgroundLinear,localPrimaryMeanInputTable,
    localAttachedMeanInputTable,blockBodyMeanTable,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin]
  simp only [nsmul_eq_mul,map_natCast]
  dsimp only [T]
  ring

/-- The finite literal input certificate has exactly the same leading output
as the complete local background logarithm; the global first-degree cancellation
is proved in the actual physical output algebra. -/
theorem actual_background_log_output_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap = actualResponse C n → ∀ sample cutoff,
      actualLeadingOutput C n (beta n) (actualBackgroundLog C n (beta n) operator sample cutoff) =
      actualLeadingOutput C n (beta n) (backgroundLogarithm
        (fun index => blockBackgroundError C n (beta n) operator index (actualQueueShifts n sample index)) Finset.univ cutoff) := by
  filter_upwards [actual_global_mean_output_eventually C hC beta hbeta] with n hm operator hop sample cutoff
  unfold actualBackgroundLog backgroundLogarithm
  rw [map_add,map_sum,hm operator hop sample]
  simp only [map_sub,Finset.sum_sub_distrib]
  simp_rw [← map_sum]
  rw [blockBackgroundLinear_sum]
  ring


/-- Every actual queue, every retained body pool, and every finite cutoff
share one concrete calibrated inverse and the same global activity budget. -/
theorem actual_background_log_activity_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n ∧ Parameters.legs n ≤ 2*pool n) :
    ∀ᶠ n in atTop, ∃ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap = actualResponse C n ∧ ∀ bodyPool : ℕ, Parameters.bodies n ≤ 2*bodyPool →
      ∀ sample cutoff, 1 ≤ cutoff →
      activity (inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (pool n) bodyPool ((n : ℝ)^2))
        (actualBackgroundLog C n (beta n) operator sample cutoff) ≤ backgroundLogConstant C/(n : ℝ)^2 := by
  have hlarge : ∀ᶠ n : ℕ in atTop, 2*bodyMeanInputConstant ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (2*bodyMeanInputConstant))
  filter_upwards [actual_local_log_remainder_eventually C hC beta pool htypical,
    actual_global_mean_input_eventually C hC beta pool htypical,
    actual_body_mean_input_table_eventually C hC beta pool htypical,hlarge,eventually_ge_atTop 2]
    with n hl hg hb hlarge hn
  obtain ⟨operator,hop,hl⟩ := hl
  obtain ⟨other,hother,hg⟩ := hg
  have heq : other = operator := actualResponse_equiv_unique C n other operator hother hop
  subst other
  obtain ⟨other,hother,hb⟩ := hb
  have heq : other = operator := actualResponse_equiv_unique C n other operator hother hop
  subst other
  refine ⟨operator,hop,?_⟩
  intro bpool hbp sample cutoff hcut
  let w := inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (pool n) bpool ((n : ℝ)^2)
  have hw : ∀ seed, 0 ≤ w seed := fun seed => inputWeight_nonneg _ _ _ _ _ seed (sq_nonneg _)
  have hx : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hx0 : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hx
  have hB : 0 ≤ bodyMeanInputConstant := (local_background_constants_nonneg C).1
  have hH : 0 ≤ localHigherConstant C := (local_background_constants_nonneg C).2.2.2.2.1
  have hm : (Parameters.legs n : ℝ) = (n : ℝ)^30 := by
    simp only [Parameters.legs,Parameters.security_eq n hn,Nat.cast_pow]
  have hcount : ((Parameters.bodies n-Parameters.legs n : ℕ) : ℝ) ≤ 2*(n : ℝ)^60 := by
    have hh : Parameters.bodies n-Parameters.legs n ≤ 2*n^60 :=
      (Nat.sub_le _ _).trans ((show Parameters.bodies n ≤ Parameters.dimension n from Nat.sub_le _ _).trans
        (by simpa only [Parameters.security_eq n hn] using (Parameters.dimension_bounds n).2))
    exact_mod_cast hh
  have hleg (leg : Fin (Parameters.legs n)) :
      activity w (logarithm (blockBackgroundError C n (beta n) operator (.inl leg)
        (actualQueueShifts n sample (.inl leg))) cutoff-
        blockBackgroundLinear C n (beta n) operator (.inl leg) (actualQueueShifts n sample (.inl leg))) ≤
      (localHigherConstant C+2*localErrorConstant C^2)/(n : ℝ)^32 := by
    have hh := (hl bpool hbp _ (actualQueueShifts_bound n sample (.inl leg))).2 cutoff hcut
    rw [hm] at hh
    calc
      _ ≤ ((localHigherConstant C+2*localErrorConstant C^2)/(n : ℝ)^2)/(n : ℝ)^30 :=
        (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using hh)
      _ = _ := by field_simp
  have hbody (body : Fin (Parameters.bodies n-Parameters.legs n)) :
      activity w (logarithm (blockBackgroundError C n (beta n) operator (.inr body)
        (actualQueueShifts n sample (.inr body))) cutoff-
        blockBackgroundLinear C n (beta n) operator (.inr body) (actualQueueShifts n sample (.inr body))) ≤
      2*bodyMeanInputConstant^2/(n : ℝ)^92 := by
    let table := blockBackgroundLinear C n (beta n) operator (.inr body) (actualQueueShifts n sample (.inr body))
    have hb' : activity w table ≤ bodyMeanInputConstant/(n : ℝ)^46 := by
      apply hb bpool hbp
      have hq := actualQueueShifts_bound n sample (.inr body)
      unfold maxBodyShift
      omega
    have hsmall : activity w table ≤ 1/2 := by
      apply hb'.trans
      apply (div_le_iff₀ (by positivity)).mpr
      have hp : (n : ℝ) ≤ (n : ℝ)^46 := by simpa only [pow_one] using pow_le_pow_right₀ hx (by decide : 1 ≤ 46)
      linarith
    have hs := (sq_le_sq₀ (activity_nonneg w hw table) (by positivity : 0 ≤ bodyMeanInputConstant/(n : ℝ)^46)).mpr hb'
    have hlog := activity_logarithm_sub_linear_le w hw table 0 cutoff hcut (by simpa only [add_zero] using hsmall)
    simp only [add_zero,activity_zero,zero_add] at hlog
    apply hlog.trans
    calc
      _ ≤ 2*(bodyMeanInputConstant/(n : ℝ)^46)^2 := mul_le_mul_of_nonneg_left hs (by norm_num)
      _ = _ := by field_simp
  have hsum : activity w (∑ index, (logarithm (blockBackgroundError C n (beta n) operator index
      (actualQueueShifts n sample index)) cutoff-blockBackgroundLinear C n (beta n) operator index
      (actualQueueShifts n sample index))) ≤
      (localHigherConstant C+2*localErrorConstant C^2)/(n : ℝ)^2+4*bodyMeanInputConstant^2/(n : ℝ)^32 := by
    apply (activity_sum_le w hw _ _).trans
    rw [Fintype.sum_sum_type]
    apply (add_le_add (Finset.sum_le_sum fun leg _ => hleg leg)
      (Finset.sum_le_sum fun body _ => hbody body)).trans
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,hm]
    calc
      _ ≤ (n : ℝ)^30*((localHigherConstant C+2*localErrorConstant C^2)/(n : ℝ)^32)+
          (2*(n : ℝ)^60)*(2*bodyMeanInputConstant^2/(n : ℝ)^92) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hcount (by positivity))
      _ = _ := by field_simp; ring
  change activity w _ ≤ _
  apply (activity_add_le w hw _ _).trans
  apply (add_le_add (hg bpool hbp sample) hsum).trans
  have hg' : 8*bodyMeanInputConstant/(n : ℝ)^6 ≤ 8*bodyMeanInputConstant/(n : ℝ)^2 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_right₀ hx (by decide : 2 ≤ 6))
  have hb' : 4*bodyMeanInputConstant^2/(n : ℝ)^32 ≤ 4*bodyMeanInputConstant^2/(n : ℝ)^2 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_right₀ hx (by decide : 2 ≤ 32))
  exact (add_le_add hg' (add_le_add le_rfl hb')).trans_eq (by unfold backgroundLogConstant; ring)

end
end AFT.V7Calibration
