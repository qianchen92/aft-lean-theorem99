import AFT.AttachedMeanTable
import AFT.EndpointTable
import AFT.RepresentedLogRemainder

/-! # Actual local background input polynomials, with all inverse costs retained -/

namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
variable {Seed : Type*}

theorem hasOrder_add (order : Seed → ℕ) (minimum : ℕ) (first second : Table Seed)
    (hf : HasOrder order minimum first) (hs : HasOrder order minimum second) :
    HasOrder order minimum (first+second) := by
  intro powers hp
  rw [MvPolynomial.coeff_add,hf powers hp,hs powers hp,zero_add]

theorem activity_product_decay (w : Seed → ℝ) (hw : ∀ seed, 0 ≤ w seed)
    (first second : Table Seed) (x A B : ℝ) (i j k : ℕ) (hx : 1 ≤ x) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : activity w first ≤ A/x^i) (hs : activity w second ≤ B/x^j) (horder : k ≤ i+j) :
    activity w (first*second) ≤ A*B/x^k := by
  apply (activity_mul_le w hw first second).trans
  calc
    _ ≤ (A/x^i)*(B/x^j) := mul_le_mul hf hs (activity_nonneg w hw _) (by positivity)
    _ = A*B/x^(i+j) := by rw [pow_add]; ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_left (mul_nonneg hA hB) (by positivity)
      exact pow_le_pow_right₀ hx horder

end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open GaussianSource Filter RepresentedPolynomial
open scoped BigOperators Classical Topology
noncomputable section

def localPrimaryMeanInputTable (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ)) :=
  inversePrimaryTable (actualPrimaryLaw C n beta) (actualBodyLaw C n beta) (v7Activation C n) operator (pairMeanTable C n beta)

def localAttachedMeanInputTable (C : ℝ) (n : ℕ) (beta : ℝ) (queue : ℤ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ)) :=
  inversePrimaryTable (actualPrimaryLaw C n beta) (actualBodyLaw C n beta) (v7Activation C n) operator (attachedMeanTable C n beta queue)

def localCovarianceInputTable (C : ℝ) (n : ℕ) (beta : ℝ) (queue : ℤ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ)) :=
  inversePrimaryTable (actualPrimaryLaw C n beta) (actualBodyLaw C n beta) (v7Activation C n) operator (actualCovarianceTable C n beta queue)

def localBackgroundLinear (C : ℝ) (n : ℕ) (beta : ℝ) (queue : ℤ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ)) :=
  localPrimaryMeanInputTable C n beta operator+localAttachedMeanInputTable C n beta queue operator

def localBackgroundHigher (C : ℝ) (n : ℕ) (beta : ℝ) (queue : ℤ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ)) :=
  actualEndpointHigherTable C n beta operator+
    localPrimaryMeanInputTable C n beta operator*localAttachedMeanInputTable C n beta queue operator+
    actualEndpointHigherTable C n beta operator*localAttachedMeanInputTable C n beta queue operator+
    localCovarianceInputTable C n beta queue operator

def localBackgroundError (C : ℝ) (n : ℕ) (beta : ℝ) (queue : ℤ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ)) :=
  localBackgroundLinear C n beta queue operator+localBackgroundHigher C n beta queue operator

def localLinearConstant (C : ℝ) : ℝ := pairMeanInputConstant C+bodyMeanInputConstant

def localHigherConstant (C : ℝ) : ℝ := endpointAggregateConstant C+
  pairMeanInputConstant C*bodyMeanInputConstant+endpointAggregateConstant C*bodyMeanInputConstant+268435456

def localErrorConstant (C : ℝ) : ℝ := localLinearConstant C+localHigherConstant C

/-- The formal local input has the exact product-plus-covariance structure;
its factors retain the true shared-source residual table. -/
theorem localBackgroundError_factorization (C : ℝ) (n : ℕ) (beta : ℝ) (queue : ℤ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ)) :
    1+localBackgroundError C n beta queue operator =
      (1+localPrimaryMeanInputTable C n beta operator+actualEndpointHigherTable C n beta operator)*
      (1+localAttachedMeanInputTable C n beta queue operator)+localCovarianceInputTable C n beta queue operator := by
  unfold localBackgroundError localBackgroundLinear localBackgroundHigher
  ring

theorem localBackgroundLinear_hasOrder (C : ℝ) (n : ℕ) (beta : ℝ) (queue : ℤ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ)) :
    HasOrder (fun seed => seed.primaryOrder+seed.bodyOrder) 1 (localBackgroundLinear C n beta queue operator) := by
  apply hasOrder_add
  · exact inversePrimaryTable_hasOrder _ _ _ _ _ _ (pairMeanTable_hasOrder C n beta)
  · exact inversePrimaryTable_hasOrder _ _ _ _ _ _ (attachedMeanTable_hasOrder C n beta queue)

theorem localBackgroundHigher_hasOrder (C : ℝ) (n : ℕ) (beta : ℝ) (queue : ℤ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ)) :
    HasOrder (fun seed => seed.primaryOrder+seed.bodyOrder) 2 (localBackgroundHigher C n beta queue operator) := by
  have hp : HasOrder (fun seed => seed.primaryOrder+seed.bodyOrder) 1 (localPrimaryMeanInputTable C n beta operator) :=
    inversePrimaryTable_hasOrder _ _ _ _ _ _ (pairMeanTable_hasOrder C n beta)
  have hb : HasOrder (fun seed => seed.primaryOrder+seed.bodyOrder) 1 (localAttachedMeanInputTable C n beta queue operator) :=
    inversePrimaryTable_hasOrder _ _ _ _ _ _ (attachedMeanTable_hasOrder C n beta queue)
  have he := actualEndpointHigherTable_hasOrder C n beta operator
  apply hasOrder_add
  · apply hasOrder_add
    · exact hasOrder_add _ _ _ _ he (hasOrder_mul _ 1 1 _ _ hp hb)
    · exact hasOrder_mono _ 2 3 _ (hasOrder_mul _ 2 1 _ _ he hb) (by decide)
  · exact inversePrimaryTable_hasOrder _ _ _ _ _ _ (actualCovarianceTable_hasOrder C n beta queue)

/-- The same actual inverse supplies all local means, endpoint completion,
and the complete active/inactive shared-source covariance. -/
theorem actual_local_input_components_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n ∧ Parameters.legs n ≤ 2*pool n) :
    ∀ᶠ n in atTop, ∃ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap = actualResponse C n ∧ ∀ bodyPool : ℕ, Parameters.bodies n ≤ 2*bodyPool →
      ∀ queue : ℤ, |queue| ≤ queueCutoff n →
      let w := inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (pool n) bodyPool ((n : ℝ)^2)
      activity w (localPrimaryMeanInputTable C n (beta n) operator) ≤ pairMeanInputConstant C/(n : ℝ)^16 ∧
      activity w (localAttachedMeanInputTable C n (beta n) queue operator) ≤ bodyMeanInputConstant/(n : ℝ)^46 ∧
      activity w (actualEndpointHigherTable C n (beta n) operator) ≤ endpointAggregateConstant C/(n : ℝ)^32 ∧
      activity w (localCovarianceInputTable C n (beta n) queue operator) ≤ 268435456/(n : ℝ)^32 := by
  have hbeta := htypical.mono fun _ h => And.intro h.1 h.2.1
  filter_upwards [actual_primary_seed_inverse_eventually C hC beta pool htypical,
    actual_endpoint_higher_table_eventually C hC beta pool htypical,
    actual_pair_mean_table_raw_eventually C hC beta hbeta,
    actual_attached_mean_table_raw_eventually C hC beta hbeta,
    actual_covariance_table_mixed_activity_eventually C hC beta hbeta,
    actual_reference_laws_eventually C hC beta hbeta,htypical,eventually_ge_atTop 2]
    with n hi he hp hb hc hl ht hn
  obtain ⟨operator,hop,hi⟩ := hi
  obtain ⟨other,hother,he⟩ := he
  have heq : other = operator := actualResponse_equiv_unique C n other operator hother hop
  subst other
  refine ⟨operator,hop,?_⟩
  intro bpool hbp queue hq
  dsimp only
  let primary := actualPrimaryLaw C n (beta n)
  let body := actualBodyLaw C n (beta n)
  let w := inputWeight primary body (pool n) bpool ((n : ℝ)^2)
  have hi' := inversePrimaryTable_activity_le primary body (pool n) bpool ((n : ℝ)^2) (v7Activation C n)
    (sq_nonneg _) operator (hi body bpool ((n : ℝ)^2) (sq_nonneg _))
  have hp' := (hi' (pairMeanTable C n (beta n))).trans (hp primary body hl.1 hl.2.1 (pool n) bpool ht.2.2 hbp)
  have hb' := (hi' (attachedMeanTable C n (beta n) queue)).trans (hb primary body hl.1 hl.2.1 (pool n) bpool ht.2.2 hbp queue hq)
  have hc' := (mul_le_mul_of_nonneg_left (hi' (actualCovarianceTable C n (beta n) queue)) (Nat.cast_nonneg (Parameters.legs n))).trans
    (hc queue primary body hl.1 (pool n) ht.2.2 bpool ((n : ℝ)^2) (sq_nonneg _))
  have he' := he bpool hbp
  have hx0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm : (Parameters.legs n : ℝ) = (n : ℝ)^30 := by simp only [Parameters.legs,Parameters.security_eq n hn,Nat.cast_pow]
  rw [hm] at he' hc'
  refine ⟨hp',hb',?_,?_⟩
  · calc
      _ ≤ (endpointAggregateConstant C/(n : ℝ)^2)/(n : ℝ)^30 :=
        (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using he')
      _ = _ := by field_simp
  · calc
      _ ≤ (268435456/(n : ℝ)^2)/(n : ℝ)^30 :=
        (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using hc')
      _ = _ := by field_simp


theorem local_background_constants_nonneg (C : ℝ) :
    0 ≤ bodyMeanInputConstant ∧ 0 ≤ pairMeanInputConstant C ∧ 0 ≤ endpointAggregateConstant C ∧
      0 ≤ localLinearConstant C ∧ 0 ≤ localHigherConstant C ∧ 0 ≤ localErrorConstant C := by
  have hb : 0 ≤ bodyMeanInputConstant := by unfold bodyMeanInputConstant bodyMeanRelativeConstant; positivity
  have hp : 0 ≤ pairMeanInputConstant C := by unfold pairMeanInputConstant bodyMeanRelativeConstant; positivity
  have he : 0 ≤ endpointAggregateConstant C := by
    unfold endpointAggregateConstant pairResidualMixedConstant pairReferenceMixedConstant pairNeumannConstant
      markedAggregateConstant markedFringeAggregateConstant bodyMeanRelativeConstant
    positivity
  have hl : 0 ≤ localLinearConstant C := add_nonneg hp hb
  have hh : 0 ≤ localHigherConstant C := by
    unfold localHigherConstant
    positivity
  exact ⟨hb,hp,he,hl,hh,add_nonneg hl hh⟩

theorem local_background_activity_bounds (C : ℝ) (n : ℕ) (beta : ℝ) (queue : ℤ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (w : InputSeed (Fin (Parameters.modulus n)) → ℝ) (hw : ∀ seed, 0 ≤ w seed) (hn : 1 ≤ (n : ℝ))
    (hp : activity w (localPrimaryMeanInputTable C n beta operator) ≤ pairMeanInputConstant C/(n : ℝ)^16)
    (hb : activity w (localAttachedMeanInputTable C n beta queue operator) ≤ bodyMeanInputConstant/(n : ℝ)^46)
    (he : activity w (actualEndpointHigherTable C n beta operator) ≤ endpointAggregateConstant C/(n : ℝ)^32)
    (hc : activity w (localCovarianceInputTable C n beta queue operator) ≤ 268435456/(n : ℝ)^32) :
    activity w (localBackgroundLinear C n beta queue operator) ≤ localLinearConstant C/(n : ℝ)^16 ∧
    activity w (localBackgroundHigher C n beta queue operator) ≤ localHigherConstant C/(n : ℝ)^32 ∧
    activity w (localBackgroundError C n beta queue operator) ≤ localErrorConstant C/(n : ℝ)^16 := by
  obtain ⟨hB,hP,hE,hL,hH,hK⟩ := local_background_constants_nonneg C
  have hb' : bodyMeanInputConstant/(n : ℝ)^46 ≤ bodyMeanInputConstant/(n : ℝ)^16 :=
    div_le_div_of_nonneg_left hB (by positivity) (pow_le_pow_right₀ hn (by decide : 16 ≤ 46))
  have hl : activity w (localBackgroundLinear C n beta queue operator) ≤ localLinearConstant C/(n : ℝ)^16 :=
    (activity_add_le w hw _ _).trans ((add_le_add hp (hb.trans hb')).trans_eq (by unfold localLinearConstant; ring))
  have hpb := activity_product_decay w hw _ _ (n : ℝ) (pairMeanInputConstant C) bodyMeanInputConstant
    16 46 32 hn hP hB hp hb (by decide)
  have heb := activity_product_decay w hw _ _ (n : ℝ) (endpointAggregateConstant C) bodyMeanInputConstant
    32 46 32 hn hE hB he hb (by decide)
  have hh : activity w (localBackgroundHigher C n beta queue operator) ≤ localHigherConstant C/(n : ℝ)^32 := by
    unfold localBackgroundHigher
    apply (activity_add_le w hw _ _).trans
    apply (add_le_add (activity_add_le w hw _ _) le_rfl).trans
    apply (add_le_add (add_le_add (activity_add_le w hw _ _) le_rfl) le_rfl).trans
    exact (add_le_add (add_le_add (add_le_add he hpb) heb) hc).trans_eq (by unfold localHigherConstant; ring)
  refine ⟨hl,hh,?_⟩
  have hh' : localHigherConstant C/(n : ℝ)^32 ≤ localHigherConstant C/(n : ℝ)^16 :=
    div_le_div_of_nonneg_left hH (by positivity) (pow_le_pow_right₀ hn (by decide : 16 ≤ 32))
  exact (activity_add_le w hw _ _).trans ((add_le_add hl (hh.trans hh')).trans_eq (by unfold localErrorConstant; ring))

/-- The full actual local logarithm is small only after retaining its
specified first-degree table. This estimate is uniform in the cutoff. -/
theorem actual_local_log_remainder_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n ∧ Parameters.legs n ≤ 2*pool n) :
    ∀ᶠ n in atTop, ∃ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap = actualResponse C n ∧ ∀ bodyPool : ℕ, Parameters.bodies n ≤ 2*bodyPool →
      ∀ queue : ℤ, |queue| ≤ queueCutoff n →
      let w := inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (pool n) bodyPool ((n : ℝ)^2)
      activity w (localBackgroundError C n (beta n) queue operator) ≤ 1/2 ∧
      ∀ cutoff : ℕ, 1 ≤ cutoff →
      (Parameters.legs n : ℝ)*activity w
        (logarithm (localBackgroundError C n (beta n) queue operator) cutoff-
          localBackgroundLinear C n (beta n) queue operator) ≤
        (localHigherConstant C+2*localErrorConstant C^2)/(n : ℝ)^2 := by
  have hlarge : ∀ᶠ n : ℕ in atTop, 2*localErrorConstant C ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (2*localErrorConstant C))
  filter_upwards [actual_local_input_components_eventually C hC beta pool htypical,hlarge,eventually_ge_atTop 2]
    with n hc hlarge hn
  obtain ⟨operator,hop,hc⟩ := hc
  refine ⟨operator,hop,?_⟩
  intro bpool hbp queue hq
  dsimp only
  let w := inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (pool n) bpool ((n : ℝ)^2)
  have hw : ∀ seed, 0 ≤ w seed := fun seed => inputWeight_nonneg _ _ _ _ _ seed (sq_nonneg _)
  have hx : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hx0 : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hx
  obtain ⟨hp,hb,he,hcov⟩ := hc bpool hbp queue hq
  obtain ⟨hl,hh,herror⟩ := local_background_activity_bounds C n (beta n) queue operator w hw hx hp hb he hcov
  have hsmall : activity w (localBackgroundError C n (beta n) queue operator) ≤ 1/2 := by
    apply herror.trans
    apply (div_le_iff₀ (by positivity)).mpr
    have hpow : (n : ℝ) ≤ (n : ℝ)^16 := by simpa only [pow_one] using pow_le_pow_right₀ hx (by decide : 1 ≤ 16)
    linarith
  refine ⟨hsmall,?_⟩
  intro cutoff hcut
  have hlog := activity_logarithm_sub_linear_le w hw (localBackgroundLinear C n (beta n) queue operator)
    (localBackgroundHigher C n (beta n) queue operator) cutoff hcut hsmall
  have hK := (local_background_constants_nonneg C).2.2.2.2.2
  have hsquare := (sq_le_sq₀ (activity_nonneg w hw _) (by positivity : 0 ≤ localErrorConstant C/(n : ℝ)^16)).mpr herror
  have hlog' : activity w (logarithm (localBackgroundError C n (beta n) queue operator) cutoff-
      localBackgroundLinear C n (beta n) queue operator) ≤ localHigherConstant C/(n : ℝ)^32+
      2*(localErrorConstant C/(n : ℝ)^16)^2 :=
    hlog.trans (add_le_add hh (mul_le_mul_of_nonneg_left hsquare (by norm_num)))
  apply (mul_le_mul_of_nonneg_left hlog' (Nat.cast_nonneg (Parameters.legs n))).trans_eq
  simp only [Parameters.legs,Parameters.security_eq n hn,Nat.cast_pow]
  field_simp

end
end AFT.V7Calibration
