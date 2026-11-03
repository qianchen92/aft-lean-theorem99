import AFT.PhysicalBlockMass
import AFT.MarkedOutput
import AFT.BodyPhysicalSupport

/-! # Exact boundary support of the true local physical laws -/
namespace AFT.V7Calibration
open GaussianSource Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem inactivePairAtSource_zero_boundary (C : ℝ) (n : ℕ) (source : ℤ)
    (first second : Fin (Parameters.modulus n))
    (h : first∈boundaryPalette (Parameters.modulus n) (boundaryHalf C n) ∨
      second∈boundaryPalette (Parameters.modulus n) (boundaryHalf C n)) :
    inactivePairAtSource C n source first second=0 := by
  have hz (start : ℤ) : TrimmedSlice.averagedPair (Parameters.modulus n) (boundaryHalf C n)
      start source (Parameters.anchorWidth n) first second=0 := by
    unfold TrimmedSlice.averagedPair
    apply Finset.sum_eq_zero
    intro offset _
    have hpair : TrimmedSlice.orderedPairSlice (Parameters.modulus n) (boundaryHalf C n) (offset-source) first second=0 := by
      rcases h with hf | hs
      · have hout := (mem_boundaryPalette _ _ _).mp hf
        unfold TrimmedSlice.orderedPairSlice TrimmedSlice.law
        rw [if_neg (by intro hh; have hh := (TrimmedSlice.mem_slice _ _ _ _).mp hh; omega),zero_mul]
      · rw [TrimmedSlice.orderedPairSlice_symmetric]
        have hout := (mem_boundaryPalette _ _ _).mp hs
        unfold TrimmedSlice.orderedPairSlice TrimmedSlice.law
        rw [if_neg (by intro hh; have hh := (TrimmedSlice.mem_slice _ _ _ _).mp hh; omega),zero_mul]
    rw [hpair,mul_zero]
  simp only [inactivePairAtSource,TrimmedSlice.mixedPair,hz,mul_zero,Finset.sum_const_zero,add_zero,zero_div]

theorem actual_attached_body_boundary_eventually (C : ℝ) (hC : 1≤C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n)≤beta n ∧
      beta n≤2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ queue : ℤ,|queue| ≤ queueCutoff n →
      ∀ source : Window (legCutoff C n-1),∀ color∈boundaryPalette (Parameters.modulus n) (boundaryHalf C n),
        attachedBodyAtSource C n (beta n) queue source color=0 := by
  filter_upwards [actual_body_center_probability_eventually C hC beta hbeta] with n hb queue hq source color hc
  have hc := (mem_boundaryPalette _ _ _).mp hc
  unfold attachedBodyAtSource
  apply Finset.sum_eq_zero
  intro root _
  have hr := abs_le.mpr (Finset.mem_Icc.mp root.property)
  have hs := abs_le.mpr (Finset.mem_Icc.mp source.property)
  have hshift : |(root : ℤ)+(source : ℤ)+queue| ≤ maxBodyShift C n := by
    have hh := (abs_add_le ((root : ℤ)+source) queue).trans
      (add_le_add ((abs_add_le (root : ℤ) source).trans (add_le_add hr hs)) (le_refl |queue|))
    have hh' := hh.trans (add_le_add le_rfl hq)
    simpa only [maxBodyShift,Nat.cast_add] using hh'
  rw [integerShiftProfile_support n _ hb.2.2 _ color (by unfold boundaryHalf at hc; omega),mul_zero]

theorem actual_marked_pair_boundary_eventually (C : ℝ) (hC : 1≤C) :
    ∀ᶠ n in atTop,∀ beta : ℝ,∀ first second : Fin (Parameters.modulus n),
      second∈boundaryPalette (Parameters.modulus n) (boundaryHalf C n) →
      actualMarkedPair C n beta first second=0 := by
  filter_upwards [actual_full_anchor_safe_eventually C hC,body_support_scales_eventually C hC]
    with n ha hs beta first second hsecond
  have hc := (mem_boundaryPalette _ _ _).mp hsecond
  unfold actualMarkedPair
  rw [(ha first).2 second.val (by omega),mul_zero]

theorem actual_local_triple_boundary_eventually (C : ℝ) (hC : 1≤C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n)≤beta n ∧
      beta n≤2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ queue : ℤ,|queue| ≤ queueCutoff n →
      ∀ first second third : Fin (Parameters.modulus n),
        (second∈boundaryPalette (Parameters.modulus n) (boundaryHalf C n) ∨
          third∈boundaryPalette (Parameters.modulus n) (boundaryHalf C n)) →
        actualLocalTriple C n (beta n) queue first second third=0 := by
  filter_upwards [actual_attached_body_boundary_eventually C hC beta hbeta,
    actual_marked_pair_boundary_eventually C hC] with n hb hm queue hq first second third hout
  unfold actualLocalTriple
  rcases hout with hs | ht
  · simp only [inactivePairAtSource_zero_boundary C n _ first second (Or.inr hs),mul_zero,zero_mul,
      Finset.sum_const_zero,hm _ _ _ hs,add_zero]
  · simp only [hb queue hq _ third ht,mul_zero,Finset.sum_const_zero]
    have hz := hb queue hq (windowZero (legCutoff C n-1)) third ht
    change attachedBodyAtSource C n (beta n) queue 0 third=0 at hz
    rw [hz,mul_zero,zero_add]

theorem actual_pair_first_boundary_eventually (C : ℝ) (hC : 1≤C) :
    ∀ᶠ n in atTop,∀ beta : ℝ,∀ first∈boundaryPalette (Parameters.modulus n) (boundaryHalf C n),
      (∑ second,localPairMixture C n beta first second)=v7Activation C n*actualPrimary C n beta first := by
  filter_upwards [actual_full_anchor_safe_eventually C hC] with n ha beta first hf
  simp only [localPairMixture,averagedInactivePair,actualMarkedPair,
    inactivePairAtSource_zero_boundary C n _ first _ (Or.inl hf),mul_zero,Finset.sum_const_zero,
    zero_add,← Finset.mul_sum,(ha first).1,mul_one]

theorem actual_triple_pair_marginal_eventually (C : ℝ) (hC : 1≤C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n)≤beta n ∧
      beta n≤2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ queue : ℤ,|queue| ≤ queueCutoff n →∀ first second,
      (∑ third,actualLocalTriple C n (beta n) queue first second third)=localPairMixture C n (beta n) first second := by
  filter_upwards [actual_attached_body_mass_eventually C hC beta hbeta] with n hb queue hq first second
  have hz := hb queue hq (windowZero (legCutoff C n-1))
  change (∑ color,attachedBodyAtSource C n (beta n) queue 0 color)=1 at hz
  unfold actualLocalTriple
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,Finset.sum_comm]
  simp_rw [← Finset.mul_sum,hb queue hq,hz,mul_one]
  rfl

end
end AFT.V7Calibration
