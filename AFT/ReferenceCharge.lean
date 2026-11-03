import AFT.ActualBetaReference
import AFT.MixtureConditioning
import AFT.V7Charge
import AFT.JointPairOutput

/-! # Charge probabilities of the true inhomogeneous beta reference -/
namespace AFT
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace HistogramGenerating
variable {G Slot : Type*} [Fintype G] [AddCommGroup G] [Fintype Slot]

def histogramCharge (N : ℕ) (hist : Histogram N G) : G := ∑ color,(hist color : ℕ) • color

theorem histogramCharge_boundedHistogram (N : ℕ) (hcard : Fintype.card Slot≤N) (word : Slot → G) :
    histogramCharge N (boundedHistogram N hcard word)=∑ slot,word slot := by
  change (∑ color,counts word color • color)=_
  simp only [counts,Finsupp.finset_sum_apply,Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro slot _
  simp [Finsupp.single_apply]

theorem histogramCharge_histogram (N : ℕ) (word : Fin N → G) :
    histogramCharge N (histogram word)=∑ slot,word slot := by
  rw [← boundedHistogram_fin N word]
  exact histogramCharge_boundedHistogram _ _ _
end HistogramGenerating

namespace FiniteDist
variable {G : Type*} [Fintype G] [AddCommGroup G]

/-- An arbitrary independent summand does not enlarge a uniform pointwise
charge error. Its distribution may have zero atoms. -/
theorem convolution_uniform_error_le (first second : FiniteDist G) (error : ℝ)
    (herror : ∀ point,|second.weight point-(Fintype.card G : ℝ)⁻¹|≤error) (point : G) :
    |(first.convolution second).weight point-(Fintype.card G : ℝ)⁻¹|≤error := by
  have he : (first.convolution second).weight point-(Fintype.card G : ℝ)⁻¹=
      ∑ x,first.weight x*(second.weight (point-x)-(Fintype.card G : ℝ)⁻¹) := by
    simp only [convolution,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,first.sum_one,one_mul]
  rw [he]
  calc
    _ ≤ ∑ x,|first.weight x*(second.weight (point-x)-(Fintype.card G : ℝ)⁻¹)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x,first.weight x*|second.weight (point-x)-(Fintype.card G : ℝ)⁻¹| := by
      simp only [abs_mul,abs_of_nonneg (first.nonneg _)]
    _ ≤ ∑ x,first.weight x*error := Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (herror _) (first.nonneg _)
    _ = error := by rw [← Finset.sum_mul,first.sum_one,one_mul]

/-- Exact sum law for the two physical populations of the beta reference. -/
theorem independent_sum_sumtype (left right : FiniteDist G) (n m : ℕ) :
    (independent (Sum.elim (fun _ : Fin n => left) (fun _ : Fin m => right))).map
      (fun word => ∑ slot,word slot)=(right.sumLaw m).convolution (left.sumLaw n) := by
  let e := (Equiv.prodComm (Fin m → G) (Fin n → G)).trans
    (Equiv.sumArrowEquivProdArrow (Fin n) (Fin m) G).symm
  have hsplit : independent (Sum.elim (fun _ : Fin n => left) (fun _ : Fin m => right))=
      ((independent (fun _ : Fin m => right)).prod (independent (fun _ : Fin n => left))).map e := by
    ext word
    rw [map_equiv_weight]
    simp only [independent,prod_weight,Fintype.prod_sum_type,Sum.elim_inl,Sum.elim_inr]
    change (∏ i,left.weight (word (.inl i)))*(∏ j,right.weight (word (.inr j)))=_
    exact mul_comm _ _
  rw [hsplit,map_map,convolution_eq_sum_map,← independent_sum_map,← independent_sum_map,
    ← prod_map_functions,map_map]
  congr 1
  funext word
  simp only [e,Equiv.trans_apply,Equiv.prodComm_apply,Fintype.sum_sum_type]
  change (∑ i,word.2 i)+(∑ j,word.1 j)=(∑ j,word.1 j)+(∑ i,word.2 i)
  exact add_comm _ _

end FiniteDist
namespace V7Calibration
open GaussianSource Filter HistogramGenerating
open scoped Topology
attribute [local instance] actualModulusNeZero

theorem actual_interior_uniformDeviation_eventually (C : ℝ) (hC : 1≤C) :
    ∀ᶠ n in atTop,(actualReferenceInteriorLaw C n).uniformDeviation=2*actualBoundaryFraction C n := by
  filter_upwards [actual_reference_boundary_law_eventually C hC,actual_boundary_profiles_eventually C hC]
    with n hl hu
  let boundary := boundaryPalette (Parameters.modulus n) (boundaryHalf C n)
  have he : actualReferenceInteriorLaw C n=FiniteDist.uniformSafe boundaryᶜ hu.2.1 := by
    ext color
    rw [show (actualReferenceInteriorLaw C n).weight color=actualInteriorProfile C n color from congrFun hl.1 color]
    simp only [actualInteriorProfile,uniformFiniteProfile,FiniteDist.uniformSafe,boundary]
  rw [he,FiniteDist.uniformSafe_deviation]
  simp only [Fintype.card_fin,actualBoundaryFraction]
  have hq : (Parameters.modulus n : ℝ)≠0 := by exact_mod_cast (Parameters.modulus_prime n).ne_zero
  have hsum : (boundary.card : ℝ)+boundaryᶜ.card=Parameters.modulus n := by
    exact_mod_cast (show boundary.card+boundaryᶜ.card=Parameters.modulus n by simpa only [Fintype.card_fin] using boundary.card_add_card_compl)
  change 2*(1-(boundaryᶜ.card : ℝ)/Parameters.modulus n)=2*((boundary.card : ℝ)/Parameters.modulus n)
  field_simp
  linarith

local instance referenceChargeFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def actualReferenceChargeError (C : ℝ) (n : ℕ) : ℝ :=
  Parameters.modulus n*(2*actualBoundaryFraction C n)^(Parameters.dimension n-Parameters.legs n)

/-- The complete histogram retains exactly the charge of the physical
coordinate vector. The unused population is genuinely interior-uniform. -/
theorem actual_reference_histogram_charge (C : ℝ) (n : ℕ) (beta : ℝ) (required : Fin (Parameters.modulus n)) :
    (actualPositiveReferenceHistogram C n beta).eventMass
      (fun hist => histogramCharge (Parameters.dimension n) hist=required)=
    (((actualReferenceMarkedLaw C n beta).sumLaw (Parameters.legs n)).convolution
      ((actualReferenceInteriorLaw C n).sumLaw (Parameters.dimension n-Parameters.legs n))).weight required := by
  rw [actualPositiveReferenceHistogram,FiniteDist.eventMass_map]
  simp only [histogramCharge_boundedHistogram,FiniteDist.eventMass,reinstanceFiniteDist_weight]
  have hh := congrArg (fun law : FiniteDist (Fin (Parameters.modulus n)) => law.weight required)
    (FiniteDist.independent_sum_sumtype (actualReferenceInteriorLaw C n) (actualReferenceMarkedLaw C n beta)
      (Parameters.dimension n-Parameters.legs n) (Parameters.legs n))
  convert hh using 1
  apply Finset.sum_congr (by ext word; simp)
  intro word _
  split_ifs
  · change (∏ slot : Fin (Parameters.dimension n-Parameters.legs n) ⊕ Fin (Parameters.legs n), _)=∏ slot : Fin (Parameters.dimension n-Parameters.legs n) ⊕ Fin (Parameters.legs n),_
    apply Finset.prod_congr rfl
    intro slot _
    cases slot <;> rfl
  · rfl

/-- Charge flattening is uniform over every beta value, including all legal
grid values, because the `N-m` interior coordinates are unchanged. -/
theorem actual_reference_charge_eventually (C : ℝ) (hC : 1≤C) :
    ∀ᶠ n in atTop,∀ beta : ℝ,∀ required : Fin (Parameters.modulus n),
      |(Parameters.modulus n : ℝ)*(actualPositiveReferenceHistogram C n beta).eventMass
        (fun hist => histogramCharge (Parameters.dimension n) hist=required)-1|≤actualReferenceChargeError C n := by
  filter_upwards [actual_interior_uniformDeviation_eventually C hC] with n hu beta required
  have hh := FiniteDist.convolution_uniform_error_le
    ((actualReferenceMarkedLaw C n beta).sumLaw (Parameters.legs n))
    ((actualReferenceInteriorLaw C n).sumLaw (Parameters.dimension n-Parameters.legs n))
    ((actualReferenceInteriorLaw C n).uniformDeviation^(Parameters.dimension n-Parameters.legs n))
    (fun point => FiniteDist.sumLaw_deviation_le _ _ point) required
  rw [hu,← actual_reference_histogram_charge] at hh
  have hq : (Parameters.modulus n : ℝ)≠0 := by exact_mod_cast (Parameters.modulus_prime n).ne_zero
  have h := mul_le_mul_of_nonneg_left hh (show (0 : ℝ)≤Parameters.modulus n by positivity)
  simp only [Fintype.card_fin] at h
  have habs := abs_mul (Parameters.modulus n : ℝ)
    ((actualPositiveReferenceHistogram C n beta).eventMass
      (fun hist => histogramCharge (Parameters.dimension n) hist=required)-(Parameters.modulus n : ℝ)⁻¹)
  rw [abs_of_nonneg (show (0 : ℝ)≤Parameters.modulus n by positivity),mul_sub,mul_inv_cancel₀ hq] at habs
  rw [← habs] at h
  exact h


/-- The uniform charge discrepancy remains negligible with the actual V7
population and modulus, without assumptions on a sampled beta sequence. -/
theorem actual_reference_charge_error_negligible (C : ℝ) (hC : 1≤C) :
    Negligible (actualReferenceChargeError C) := by
  let base := fun n => 2*actualBoundaryFraction C n
  have hbase0 : ∀ᶠ n in atTop,0≤base n := Filter.Eventually.of_forall fun n => by dsimp [base,actualBoundaryFraction]; positivity
  have hbase : ∀ᶠ n in atTop,base n≤1/(n : ℝ) := by
    filter_upwards [actual_boundary_fraction_eventually C hC,eventually_ge_atTop 80] with n hb hn
    have hn0 : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
    have hn80 : (80 : ℝ)≤n := by exact_mod_cast hn
    have hp37 : (80 : ℝ)≤(n : ℝ)^37 := hn80.trans (le_self_pow₀ (by linarith) (by norm_num))
    have hh : 80/(n : ℝ)^38≤1/n := by
      apply (div_le_div_iff₀ (pow_pos hn0 _) hn0).mpr
      have he : (n : ℝ)^38=(n : ℝ)^37*n := by ring
      rw [he]
      nlinarith
    apply le_trans _ hh
    calc
      base n≤2*(40/(n : ℝ)^38) := mul_le_mul_of_nonneg_left hb.2 (by norm_num)
      _=80/(n : ℝ)^38 := by ring
  have hpop : ∀ᶠ n in atTop,n≤Parameters.dimension n-Parameters.legs n := by
    filter_upwards [bodies_after_deletions_grow 0] with n hn
    have hp := Parameters.population_identity n
    omega
  have hh := negligible_growing_power 41 base (fun n => Parameters.dimension n-Parameters.legs n) hbase0 hbase hpop
  apply hh.of_eventually_le
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn2 : (2 : ℝ)≤n := by exact_mod_cast hn
  have hq : (Parameters.modulus n : ℝ)≤2*(n : ℝ)^40 := by
    exact_mod_cast (show Parameters.modulus n≤2*n^40 by simpa only [Parameters.security_eq n hn] using (Parameters.modulus_bounds n).2)
  have hcoef : (Parameters.modulus n : ℝ)≤(n : ℝ)^41 := by
    rw [pow_succ]
    exact hq.trans (by nlinarith [mul_le_mul_of_nonneg_right hn2 (show 0≤(n : ℝ)^40 by positivity)])
  rw [abs_of_nonneg (by unfold actualReferenceChargeError actualBoundaryFraction; positivity),
    abs_of_nonneg (by dsimp [base,actualBoundaryFraction]; positivity)]
  exact mul_le_mul_of_nonneg_right hcoef (by dsimp [base,actualBoundaryFraction]; positivity)

end V7Calibration

end
end AFT
