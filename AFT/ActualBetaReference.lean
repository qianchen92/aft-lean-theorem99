import AFT.ActualBetaCutoff
import AFT.BetaHistogram

/-! # The actual positive V7 reference mixed over its legal beta interval -/
namespace AFT.V7Calibration
open GaussianSource BetaReference HistogramGenerating Filter MeasureTheory
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] actualModulusNeZero

def actualReferenceBoundaryLaw (C : ℝ) (n : ℕ) : FiniteDist (Fin (Parameters.modulus n)) :=
  probabilityOr (actualBoundaryProfile C n) (actualCoreLaw n)

theorem actual_reference_boundary_rate (C : ℝ) (n : ℕ) (beta : ℝ)
    (hr : v7Activation C n≠0) (hb : beta≠0) :
    actualReferenceBoundaryRate C n beta=actualBoundaryFraction C n/beta := by
  unfold actualReferenceBoundaryRate actualBoundaryFraction repairedBoundaryMass
  field_simp

theorem actual_reference_boundary_law_eventually (C : ℝ) (hC : 1≤C) :
    ∀ᶠ n in atTop,(actualReferenceInteriorLaw C n).weight=actualInteriorProfile C n ∧
      (actualReferenceBoundaryLaw C n).weight=actualBoundaryProfile C n := by
  filter_upwards [actual_boundary_profiles_eventually C hC] with n hu
  have hI (color) : 0≤actualInteriorProfile C n color := by unfold actualInteriorProfile uniformFiniteProfile; split_ifs <;> positivity
  have hB (color) : 0≤actualBoundaryProfile C n color := by unfold actualBoundaryProfile uniformFiniteProfile; split_ifs <;> positivity
  exact ⟨probabilityOr_weight _ _ ⟨hI,hu.2.2.1⟩,probabilityOr_weight _ _ ⟨hB,hu.2.2.2⟩⟩


theorem actual_reference_marked_legal_eventually (C : ℝ) (hC : 1≤C) :
    ∀ᶠ n in atTop,∀ beta : ℝ,actualBetaCutoff C n≤beta →
      0<beta ∧ 0≤actualBoundaryFraction C n/beta ∧ actualBoundaryFraction C n/beta≤1 ∧
      (actualReferenceMarkedLaw C n beta).weight=actualReferenceMarkedProfile C n beta := by
  filter_upwards [actual_beta_cutoff_eventually C hC,actual_reference_boundary_law_eventually C hC,
    actual_boundary_profiles_eventually C hC,eventually_ge_atTop 1] with n hc hl hu hn beta hbeta
  have hb : 0<beta := hc.1.trans_le hbeta
  have ht0 : 0≤actualBoundaryFraction C n/beta := div_nonneg (by unfold actualBoundaryFraction; positivity) hb.le
  have ht1 : actualBoundaryFraction C n/beta≤1 := (div_le_one hb).mpr (hc.2.1.trans hbeta)
  have hr : v7Activation C n≠0 := (activation_positive _ _ _ _ (legFeatureCount_positive C n hC hn)).ne'
  have he := actual_reference_boundary_rate C n beta hr hb.ne'
  have hnonneg (color) : 0≤actualReferenceMarkedProfile C n beta color := by
    simp only [actualReferenceMarkedProfile,Pi.add_apply,Pi.smul_apply,smul_eq_mul,he]
    rw [← hl.1,← hl.2]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) ((actualReferenceInteriorLaw C n).nonneg color))
      (mul_nonneg ht0 ((actualReferenceBoundaryLaw C n).nonneg color))
  have hmass : (∑ color,actualReferenceMarkedProfile C n beta color)=1 := by
    simp only [actualReferenceMarkedProfile,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib,
      ← Finset.mul_sum,hu.2.2.1,hu.2.2.2]
    ring
  exact ⟨hb,ht0,ht1,probabilityOr_weight _ _ ⟨hnonneg,hmass⟩⟩


theorem actual_reference_uniform_eventually (C : ℝ) (hC : 1≤C) :
    ∀ᶠ n in atTop,∀ hzero : 0≤actualBoundaryFraction C n,∀ hone : actualBoundaryFraction C n≤1,
      convexLaw (actualReferenceInteriorLaw C n) (actualReferenceBoundaryLaw C n)
        (actualBoundaryFraction C n) hzero hone=FiniteDist.uniform (Fin (Parameters.modulus n)) := by
  filter_upwards [actual_reference_boundary_law_eventually C hC,actual_boundary_profiles_eventually C hC]
    with n hl hu hzero hone
  let boundary := boundaryPalette (Parameters.modulus n) (boundaryHalf C n)
  have hB : (boundary.card : ℝ)≠0 := by exact_mod_cast ne_of_gt hu.1.card_pos
  have hI : (boundaryᶜ.card : ℝ)≠0 := by exact_mod_cast ne_of_gt hu.2.1.card_pos
  have hq : (Parameters.modulus n : ℝ)≠0 := by exact_mod_cast (Parameters.modulus_prime n).ne_zero
  have hsum : (boundary.card : ℝ)+boundaryᶜ.card=Parameters.modulus n := by
    exact_mod_cast (show boundary.card+boundaryᶜ.card=Parameters.modulus n by simpa only [Fintype.card_fin] using boundary.card_add_card_compl)
  ext color
  change (1-actualBoundaryFraction C n)*(actualReferenceInteriorLaw C n).weight color+
    actualBoundaryFraction C n*(actualReferenceBoundaryLaw C n).weight color=_
  rw [hl.1,hl.2]
  change (1-(boundary.card : ℝ)/Parameters.modulus n)*uniformFiniteProfile boundaryᶜ color+
    ((boundary.card : ℝ)/Parameters.modulus n)*uniformFiniteProfile boundary color=(Fintype.card (Fin (Parameters.modulus n)) : ℝ)⁻¹
  simp only [Fintype.card_fin,uniformFiniteProfile,Finset.mem_compl]
  by_cases hc : color∈boundary
  · simp only [hc,not_true_eq_false,if_false,if_true,mul_zero,zero_add]
    field_simp
  · simp only [hc,not_false_eq_true,if_false,if_true,mul_zero,add_zero]
    field_simp
    linarith

theorem actual_reference_slot_card (n : ℕ) :
    Fintype.card (Fin (Parameters.dimension n-Parameters.legs n) ⊕ Fin (Parameters.legs n))≤Parameters.dimension n := by
  simp only [Fintype.card_sum,Fintype.card_fin]
  have h := Parameters.population_identity n
  omega

local instance actualBetaReferenceFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def reinstanceFiniteDist {α : Type*} {first : Fintype α} (second : Fintype α)
    (law : @FiniteDist α first) : @FiniteDist α second := by
  cases Subsingleton.elim first second
  exact law

@[simp] theorem reinstanceFiniteDist_weight {α : Type*} {first : Fintype α} (second : Fintype α)
    (law : @FiniteDist α first) : @FiniteDist.weight α second (reinstanceFiniteDist second law)=@FiniteDist.weight α first law := by
  unfold reinstanceFiniteDist
  cases Subsingleton.elim first second
  rfl

def actualPositiveReferenceHistogram (C : ℝ) (n : ℕ) (beta : ℝ) : FiniteDist (Histogram (Parameters.dimension n) (Fin (Parameters.modulus n))) :=
  (reinstanceFiniteDist inferInstance (actualPositiveReferenceLaw C n beta)).map (boundedHistogram (Parameters.dimension n) (actual_reference_slot_card n))

theorem actual_reference_histogram_eventually (C : ℝ) (hC : 1≤C) :
    ∀ᶠ n in atTop,∀ beta : ℝ,actualBetaCutoff C n≤beta →
      actualPositiveReferenceHistogram C n beta=referenceHistogram (Parameters.dimension n) (Parameters.legs n)
        (by have h := Parameters.population_identity n; omega)
        (actualReferenceInteriorLaw C n) (actualReferenceBoundaryLaw C n) (actualBoundaryFraction C n/beta) := by
  filter_upwards [actual_reference_marked_legal_eventually C hC,actual_reference_boundary_law_eventually C hC,
    eventually_ge_atTop 1] with n hm hl hn beta hb
  have hh := hm beta hb
  have hr : v7Activation C n≠0 := (activation_positive _ _ _ _ (legFeatureCount_positive C n hC hn)).ne'
  have he := actual_reference_boundary_rate C n beta hr hh.1.ne'
  have heq : actualReferenceMarkedLaw C n beta=
      convexLaw (actualReferenceInteriorLaw C n) (actualReferenceBoundaryLaw C n)
        (actualBoundaryFraction C n/beta) hh.2.1 hh.2.2.1 := by
    ext color
    simp only [hh.2.2.2]
    change actualReferenceMarkedProfile C n beta color=(1-actualBoundaryFraction C n/beta)*(actualReferenceInteriorLaw C n).weight color+
      (actualBoundaryFraction C n/beta)*(actualReferenceBoundaryLaw C n).weight color
    rw [hl.1,hl.2]
    simp only [actualReferenceMarkedProfile,Pi.add_apply,Pi.smul_apply,smul_eq_mul,he]
  rw [referenceHistogram,dif_pos ⟨hh.2.1,hh.2.2.1⟩]
  ext hist
  simp only [actualPositiveReferenceHistogram,FiniteDist.map_weight,reinstanceFiniteDist_weight]
  apply Finset.sum_congr (by ext word; simp)
  intro word _
  split_ifs
  · unfold actualPositiveReferenceLaw splitLabelLaw
    change (∏ slot : Fin (Parameters.dimension n-Parameters.legs n) ⊕ Fin (Parameters.legs n), _)=
      ∏ slot : Fin (Parameters.dimension n-Parameters.legs n) ⊕ Fin (Parameters.legs n),_
    apply Finset.prod_congr rfl
    intro slot _
    cases slot <;> simp only [Sum.elim_inl,Sum.elim_inr,heq]
  · rfl

/-- The outer continuous mixture is a concrete probability on complete
histograms. Its distance from the true uniform multinomial is negligible. -/
theorem actual_beta_uniform_histogram_eventually (C : ℝ) (hC : 1≤C) :
    ∀ᶠ n in atTop,∃ mixed : FiniteDist (Histogram (Parameters.dimension n) (Fin (Parameters.modulus n))),
      (∀ hist,mixed.weight hist=
        (∫ beta : ℝ in actualBetaCutoff C n..1,(actualPositiveReferenceHistogram C n beta).weight hist*
          BetaReference.density (Parameters.legs n) (Parameters.dimension n-Parameters.legs n-1) beta)/
        (∫ beta : ℝ in actualBetaCutoff C n..1,
          BetaReference.density (Parameters.legs n) (Parameters.dimension n-Parameters.legs n-1) beta)) ∧
      FiniteDist.TVBound mixed
        ((FiniteDist.independent fun _ : Fin (Parameters.dimension n) => FiniteDist.uniform (Fin (Parameters.modulus n))).map histogram)
        (actualBetaRejectedMass C n) := by
  filter_upwards [actual_beta_cutoff_eventually C hC,actual_boundary_fraction_eventually C hC,
    actual_reference_histogram_eventually C hC,actual_reference_uniform_eventually C hC] with n hc hb hh hu
  have hpop : Parameters.legs n+(Parameters.dimension n-Parameters.legs n-1)+1=Parameters.dimension n := by
    have h := Parameters.population_identity n
    have hp := Parameters.bodies_positive n
    omega
  have hm := inverse_beta_histogram_tv_dimension (Parameters.dimension n) (Parameters.legs n) (Parameters.dimension n-Parameters.legs n-1) hpop
    (actualReferenceInteriorLaw C n) (actualReferenceBoundaryLaw C n)
    (actualBoundaryFraction C n) (actualBetaCutoff C n) hb.1 hc.2.1 hc.2.2.2
  obtain ⟨mixed,hmixed,htv⟩ := hm
  refine ⟨mixed,?_,?_⟩
  · intro hist
    rw [hmixed]
    congr 1
    apply intervalIntegral.integral_congr
    intro beta hbeta
    rw [Set.uIcc_of_le hc.2.2.2.le] at hbeta
    dsimp only
    rw [hh beta hbeta.1]
  · simpa only [hu] using htv

end
end AFT.V7Calibration
