import AFT.ActualPositiveReference
import AFT.BackgroundQueueCertificate

/-! # The true shared-queue background and the positive reference have the same boundary law -/
namespace AFT.V7Calibration
open GaussianSource Filter RepresentedPolynomial
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def actualBoundaryPolynomial (C : ℝ) (n : ℕ) :
    Table (Fin (Parameters.modulus n)) →ₐ[ℝ] Table (Fin (Parameters.modulus n)) :=
  boundaryPolynomial (boundaryPalette (Parameters.modulus n) (boundaryHalf C n))ᶜ
    (actualInteriorProfile C n)

theorem actual_interior_collapse_properties_eventually (C : ℝ) (hC : 1≤C) :
    ∀ᶠ n in atTop,
      (∀ color∉(boundaryPalette (Parameters.modulus n) (boundaryHalf C n))ᶜ,
        actualInteriorProfile C n color=0) ∧
      (∑ color∈(boundaryPalette (Parameters.modulus n) (boundaryHalf C n))ᶜ,
        actualInteriorProfile C n color)=1 := by
  filter_upwards [actual_boundary_profiles_eventually C hC] with n hp
  constructor
  · intro color hc
    exact if_neg hc
  · let interior := (boundaryPalette (Parameters.modulus n) (boundaryHalf C n))ᶜ
    have hcard : (interior.card : ℝ)≠0 := by exact_mod_cast ne_of_gt hp.2.1.card_pos
    change (∑ color∈interior,uniformFiniteProfile interior color)=1
    calc
      _ = ∑ _color∈interior,(interior.card : ℝ)⁻¹ := Finset.sum_congr rfl (fun color hc => if_pos hc)
      _ = 1 := by simp [hcard]

theorem actual_reference_marked_boundary_fixed_eventually (C : ℝ) (hC : 1≤C) :
    ∀ᶠ n in atTop,∀ beta : ℝ,
      boundaryCollapse (boundaryPalette (Parameters.modulus n) (boundaryHalf C n))ᶜ
        (actualInteriorProfile C n) (actualReferenceMarkedProfile C n beta)=
      actualReferenceMarkedProfile C n beta := by
  filter_upwards [actual_interior_collapse_properties_eventually C hC] with n hp beta
  apply boundaryCollapse_eq_self_of_interior_multiple _ _ _ hp.2
    (1-actualReferenceBoundaryRate C n beta)
  intro color hc
  have hb := Finset.mem_compl.mp hc
  simp only [actualReferenceMarkedProfile,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
    actualBoundaryProfile,uniformFiniteProfile,hb,if_false,mul_zero,add_zero]

theorem actual_boundary_interior_factor_eventually (C : ℝ) (hC : 1≤C) :
    ∀ᶠ n in atTop,∀ beta : ℝ,
      boundaryInteriorFactor (boundaryPalette (Parameters.modulus n) (boundaryHalf C n))ᶜ
        (actualInteriorProfile C n) (actualReferenceMean C n beta)=
      singleGenerating (actualReferenceMean C n beta) (actualInteriorProfile C n) := by
  filter_upwards [actual_reference_mean_boundary_fixed_eventually C hC,
    actual_boundary_profiles_eventually C hC] with n hr hp beta
  rw [singleGenerating_mass_one _ _ hp.2.2.1]
  simp only [boundaryInteriorFactor,boundaryPolynomial,profilePolynomialMap_profileForm,hr beta,map_sub]
  ring

theorem actual_triple_boundary_polynomial_eventually (C : ℝ) (hC : 1≤C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n)≤beta n ∧
      beta n≤2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ queue : ℤ,|queue| ≤ queueCutoff n →
      actualBoundaryPolynomial C n (tripleGenerating (actualReferenceMean C n (beta n))
        (actualLocalTriple C n (beta n) queue)) =
      singleGenerating (actualReferenceMean C n (beta n)) (actualReferenceMarkedProfile C n (beta n))*
        singleGenerating (actualReferenceMean C n (beta n)) (actualInteriorProfile C n)^2 := by
  filter_upwards [actual_interior_collapse_properties_eventually C hC,
    actual_boundary_interior_factor_eventually C hC,actual_local_triple_boundary_eventually C hC beta hbeta,
    actual_triple_pair_marginal_eventually C hC beta hbeta,actual_pair_first_boundary_eventually C hC,
    actual_primary_boundary_eventually C hC,actual_local_pair_mass_eventually C hC beta hbeta,
    actual_reference_marked_boundary_fixed_eventually C hC,
    actual_reference_mean_boundary_fixed_eventually C hC,
    actual_positive_reference_laws_eventually C hC beta hbeta] with n hi hfactor hs hm hb hp hmass hmarked href hlaws queue hq
  let marginal := fun first => ∑ second,∑ third,actualLocalTriple C n (beta n) queue first second third
  have hme : marginal = fun first => ∑ second,localPairMixture C n (beta n) first second := by
    funext first
    simp only [marginal,hm queue hq]
  have hmarkedMass : (∑ color,actualReferenceMarkedProfile C n (beta n) color)=1 := by
    rw [← hlaws.2.2.2]
    exact FiniteDist.sum_one _
  have hcollapse : boundaryCollapse (boundaryPalette (Parameters.modulus n) (boundaryHalf C n))ᶜ
      (actualInteriorProfile C n) marginal=actualReferenceMarkedProfile C n (beta n) := by
    rw [← hmarked (beta n)]
    apply boundaryCollapse_eq_of_same_boundary
    · rw [hme,hmass,hmarkedMass]
    · intro color hc
      have hc' : color∈boundaryPalette (Parameters.modulus n) (boundaryHalf C n) := by
        simpa only [Finset.mem_compl,not_not] using hc
      rw [hme]
      dsimp only
      rw [hb (beta n) color hc',hp (beta n) color hc']
      simp only [actualReferenceMarkedProfile,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
        actualInteriorProfile,actualBoundaryProfile,uniformFiniteProfile,Finset.mem_compl,hc',
        not_true_eq_false,if_false,if_true,mul_zero,zero_add,actualReferenceBoundaryRate]
      ring
  change boundaryPolynomial _ _ _ = _
  rw [boundaryPolynomial_triple_companions _ _ _ _ hi.1 hi.2]
  · rw [hfactor (beta n),boundaryPolynomial_single_mass_one _ _ _ _ (by simp only [hm queue hq]; exact hmass),
      hcollapse,href (beta n),singleGenerating_mass_one _ _ hmarkedMass,map_sub]
    ring
  · intro first second third hne
    constructor
    · apply Finset.mem_compl.mpr
      intro hc
      exact hne (hs queue hq first second third (Or.inl hc))
    · apply Finset.mem_compl.mpr
      intro hc
      exact hne (hs queue hq first second third (Or.inr hc))

theorem actual_body_boundary_polynomial_eventually (C : ℝ) (hC : 1≤C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n)≤beta n ∧
      beta n≤2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ queue : ℤ,|queue| ≤ queueCutoff n →
      actualBoundaryPolynomial C n (singleGenerating (actualReferenceMean C n (beta n))
        (attachedBodyAtSource C n (beta n) queue 0)) =
      singleGenerating (actualReferenceMean C n (beta n)) (actualInteriorProfile C n) := by
  filter_upwards [actual_interior_collapse_properties_eventually C hC,
    actual_boundary_interior_factor_eventually C hC,actual_attached_body_boundary_eventually C hC beta hbeta,
    actual_attached_body_mass_eventually C hC beta hbeta] with n hi hf hs hm queue hq
  have hm' := hm queue hq (windowZero (legCutoff C n-1))
  change (∑ color,attachedBodyAtSource C n (beta n) queue 0 color)=1 at hm'
  change boundaryPolynomial _ _ _ = _
  rw [boundaryPolynomial_single_interior _ _ _ _ hi.1 hi.2,hm',map_one,one_mul,hf (beta n)]
  intro color hc
  apply hs queue hq (windowZero (legCutoff C n-1)) color
  simpa only [Finset.mem_compl,not_not] using hc

/-- The same queue sample is retained in every factor. The complete boundary
polynomial is exactly the inhomogeneous positive reference, independently of
that queue sample. -/
theorem actual_background_product_boundary_eventually (C : ℝ) (hC : 1≤C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n)≤beta n ∧
      beta n≤2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ sample,
      actualBoundaryPolynomial C n
        (∏ index,blockPhysicalPolynomial C n (beta n) index (actualQueueShifts n sample index)) =
      actualPositiveReferencePolynomial C n (beta n) := by
  filter_upwards [actual_triple_boundary_polynomial_eventually C hC beta hbeta,
    actual_body_boundary_polynomial_eventually C hC beta hbeta] with n ht hb sample
  rw [map_prod]
  have he (index : blockIndex n) : actualBoundaryPolynomial C n
      (blockPhysicalPolynomial C n (beta n) index (actualQueueShifts n sample index)) =
      match index with
      | .inl _ => singleGenerating (actualReferenceMean C n (beta n)) (actualReferenceMarkedProfile C n (beta n))*
          singleGenerating (actualReferenceMean C n (beta n)) (actualInteriorProfile C n)^2
      | .inr _ => singleGenerating (actualReferenceMean C n (beta n)) (actualInteriorProfile C n) := by
    cases index with
    | inl index => exact ht _ (actualQueueShifts_bound n sample (.inl index))
    | inr index => exact hb _ (actualQueueShifts_bound n sample (.inr index))
  simp_rw [he]
  rw [Fintype.prod_sum_type]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_pow,← pow_mul]
  have hn : 2*Parameters.legs n+(Parameters.bodies n-Parameters.legs n)=
      Parameters.dimension n-Parameters.legs n := by
    have hp := Parameters.population_identity n
    have hm := Parameters.legs_le_half_bodies n
    omega
  change _ = singleGenerating (actualReferenceMean C n (beta n)) (actualInteriorProfile C n)^_*_
  rw [mul_assoc,← pow_add,hn,mul_comm]

local instance actualBackgroundBoundaryFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance actualBackgroundBoundarySumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _

/-- The genuine background and genuine positive beta reference agree after
recording the entire boundary histogram; the average precedes inversion. -/
theorem actual_background_boundary_eventually (C : ℝ) (hC : 1≤C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n)≤beta n ∧
      beta n≤2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
      actualBoundaryPolynomial C n (actualBackgroundPolynomial C n (beta n)) =
      actualPositiveReferencePolynomial C n (beta n) := by
  filter_upwards [actual_background_product_boundary_eventually C hC beta hbeta] with n hp
  unfold actualBackgroundPolynomial
  have he := map_queueAverage (actualBoundaryPolynomial C n)
    (FiniteDist.retype (actualQueuePlacementLaw n))
    (fun sample => ∏ index,blockPhysicalPolynomial C n (beta n) index (actualQueueShifts n sample index))
  exact he.trans ((congrArg (queueAverage (FiniteDist.retype (actualQueuePlacementLaw n)))
    (funext hp)).trans (queueAverage_const _ _))

end
end AFT.V7Calibration
