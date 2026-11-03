import AFT.CenteredGaussianTail
import AFT.CountableConditioning
import AFT.FiniteMassOn

/-! # The rational-centered fair-bit step approximates the full integer law -/
namespace AFT.RationalNumerics
open GaussianSource
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

def centeredScalarMass (width : ℝ) (center : ℚ) (point : ℤ) : ℝ :=
  shiftedWeight width center point/theta width center

theorem centeredScalarMass_nonneg (width : ℝ) (center : ℚ) (hw : 0<width) (point : ℤ) :
    0≤centeredScalarMass width center point := div_nonneg (Real.exp_pos _).le (theta_pos width center hw).le

theorem centeredScalarMass_summable (width : ℝ) (center : ℚ) (hw : 0<width) :
    Summable (centeredScalarMass width center) := (summable_shiftedWeight width center hw).div_const _

theorem centeredScalarMass_sum (width : ℝ) (center : ℚ) (hw : 0<width) :
    (∑' point,centeredScalarMass width center point)=1 := by
  simp only [centeredScalarMass,tsum_div_const]
  exact div_self (theta_pos width center hw).ne'

def centeredRetainedWeight (width : ℝ) (center : ℚ) (cutoff : ℕ) (point : ℤ) : ℝ :=
  if point-centeredGaussianAnchor center∈Finset.Icc (-(cutoff : ℤ)) (cutoff : ℤ) then shiftedWeight width center point else 0

theorem centeredRetainedWeight_nonneg (width : ℝ) (center : ℚ) (cutoff : ℕ) (point : ℤ) :
    0≤centeredRetainedWeight width center cutoff point := by
  unfold centeredRetainedWeight
  split_ifs
  · exact (Real.exp_pos _).le
  · rfl

theorem centeredRetainedWeight_le (width : ℝ) (center : ℚ) (cutoff : ℕ) (point : ℤ) :
    centeredRetainedWeight width center cutoff point≤shiftedWeight width center point := by
  unfold centeredRetainedWeight
  split_ifs
  · rfl
  · exact (Real.exp_pos _).le

theorem centeredRetainedWeight_sum (width : ℝ) (center : ℚ) (cutoff : ℕ) :
    (∑' point,centeredRetainedWeight width center cutoff point)=∑ offset,centeredWindowMass width center cutoff offset := by
  let embedding : Window cutoff → ℤ := fun offset => centeredGaussianAnchor center+offset
  have hi : Function.Injective embedding := by
    intro first second he
    apply Subtype.ext
    exact add_left_cancel he
  have hsupport : Function.support (centeredRetainedWeight width center cutoff)⊆Set.range embedding := by
    intro point hp
    have hh : point-centeredGaussianAnchor center∈Finset.Icc (-(cutoff : ℤ)) (cutoff : ℤ) := by
      by_contra hn
      exact hp (if_neg hn)
    exact ⟨⟨point-centeredGaussianAnchor center,hh⟩,by dsimp only [embedding];omega⟩
  rw [←hi.tsum_eq hsupport,tsum_fintype]
  apply Finset.sum_congr rfl
  intro offset _
  simp only [centeredRetainedWeight,embedding,add_sub_cancel_left,if_pos offset.property]
  rfl

theorem centeredWindowLaw_massOn (width : ℝ) (center : ℚ) (cutoff : ℕ) (point : ℤ) :
    FiniteDist.massOn (centeredWindowLaw width center cutoff) (fun offset => centeredGaussianAnchor center+offset) point=
      centeredRetainedWeight width center cutoff point/(∑' x,centeredRetainedWeight width center cutoff x) := by
  rw [centeredRetainedWeight_sum]
  by_cases hi : point-centeredGaussianAnchor center∈Finset.Icc (-(cutoff : ℤ)) (cutoff : ℤ)
  · let offset : Window cutoff := ⟨point-centeredGaussianAnchor center,hi⟩
    have he (other : Window cutoff) : centeredGaussianAnchor center+(other : ℤ)=point ↔ other=offset := by
      constructor
      · intro hh;apply Subtype.ext;dsimp only [offset];omega
      · intro hh;subst other;dsimp only [offset];omega
    simp only [FiniteDist.massOn,he,Finset.sum_ite_eq',Finset.mem_univ,if_true,
      centeredRetainedWeight,if_pos hi,centeredWindowLaw,FiniteDist.normalize,centeredWindowMass]
    congr 2
    dsimp only [offset]
    omega
  · have he (other : Window cutoff) : centeredGaussianAnchor center+(other : ℤ)≠point := by
      intro hh
      apply hi
      have hh' : point-centeredGaussianAnchor center=(other : ℤ) := by omega
      exact hh' ▸ other.property
    simp only [FiniteDist.massOn,he,if_false,Finset.sum_const_zero,centeredRetainedWeight,if_neg hi,zero_div]

/-- Uniform clipping error against the complete integer line, with the
finite sampler centered at the actual rational floor. -/
theorem centeredWindowLaw_countable_tv (width : ℝ) (center : ℚ) (cutoff : ℕ)
    (hw : 1≤width) (hc : 1≤cutoff) :
    (∑' point,|centeredScalarMass width center point-
      FiniteDist.massOn (centeredWindowLaw width center cutoff) (fun offset => centeredGaussianAnchor center+offset) point|)/2≤
      810*width*Real.exp (-Real.pi*((cutoff : ℝ)-1)^2/(2*width^2)) := by
  have hw0 := lt_of_lt_of_le zero_lt_one hw
  have hs := summable_shiftedWeight width center hw0
  have hr := Summable.of_nonneg_of_le (centeredRetainedWeight_nonneg width center cutoff)
    (centeredRetainedWeight_le width center cutoff) hs
  have hp : 0<∑' point,centeredRetainedWeight width center cutoff point := by
    rw [centeredRetainedWeight_sum]
    exact (Real.exp_pos _).trans_le (centeredWindowMass_sum_lower width center cutoff hw)
  have htv := normalized_deleted_total_variation (shiftedWeight width center) (centeredRetainedWeight width center cutoff)
    (fun _ => (Real.exp_pos _).le) (centeredRetainedWeight_nonneg width center cutoff)
    (centeredRetainedWeight_le width center cutoff) hs hp
  have hd : theta width center-(∑' point,centeredRetainedWeight width center cutoff point)≤
      centeredClippingMass width center cutoff := by
    change (∑' point,shiftedWeight width center point)-(∑' point,centeredRetainedWeight width center cutoff point)≤_
    rw [←hs.tsum_sub hr]
    apply ((hs.sub hr).tsum_le_tsum _ (summable_centeredClippingMass width center cutoff hw0))
    intro point
    unfold centeredRetainedWeight
    by_cases hinside : point-centeredGaussianAnchor center∈Finset.Icc (-(cutoff : ℤ)) (cutoff : ℤ)
    · rw [if_pos hinside,sub_self]
      split_ifs
      · exact (Real.exp_pos _).le
      · rfl
    · rw [if_neg hinside,sub_zero]
      have habs : (cutoff : ℤ)≤|point-centeredGaussianAnchor center| := by
        have hh := hinside
        simp only [Finset.mem_Icc,not_and_or,not_le] at hh
        rcases hh with hh | hh
        · exact (neg_le_abs _).trans' (by omega)
        · exact (le_abs_self _).trans' hh.le
      have hreal : (cutoff : ℝ)≤|(point : ℝ)-(centeredGaussianAnchor center : ℝ)| := by exact_mod_cast habs
      rw [if_pos hreal]
  have hh := htv.trans (div_le_div_of_nonneg_right hd (theta_pos width center hw0).le)
  have hfinal := hh.trans (centeredClippingProbability_le width center cutoff hw (by exact_mod_cast hc))
  simpa only [centeredScalarMass,centeredWindowLaw_massOn,theta,abs_sub_comm] using hfinal

/-- The whole computed scalar step, after arbitrary finite postprocessing,
approximates the unbounded Gaussian, including both numerical and tail error. -/
theorem centeredTicketLaw_channel_tv {Output : Type*} [Fintype Output]
    (squaredWidth center : ℚ) (width : ℝ) (cutoff bits : ℕ)
    (hw : 1≤width) (hsquare : (squaredWidth : ℝ)=width^2) (hc : 1≤cutoff)
    (channel : ℤ → FiniteDist Output) :
    FiniteDist.TVBound
      ((centeredTicketLaw squaredWidth center cutoff bits).mix (fun offset => channel (centeredGaussianAnchor center+offset)))
      (FiniteDist.countableMix (centeredScalarMass width center) (centeredScalarMass_nonneg width center (lt_of_lt_of_le zero_lt_one hw))
        (centeredScalarMass_summable width center (lt_of_lt_of_le zero_lt_one hw))
        (centeredScalarMass_sum width center (lt_of_lt_of_le zero_lt_one hw)) channel)
      (1/(2 : ℝ)^bits+810*width*Real.exp (-Real.pi*((cutoff : ℝ)-1)^2/(2*width^2))) := by
  have hfinite : FiniteDist.TVBound (centeredTicketLaw squaredWidth center cutoff bits)
      (centeredWindowLaw width center cutoff) (1/(2 : ℝ)^bits) := by
    apply (FiniteDist.tvBound_iff_totalVariation_le _ _ _).mpr
    rw [FiniteDist.totalVariation_eq_half_l1]
    have he := centeredTicketLaw_l1 squaredWidth center width cutoff bits hw hsquare
    linarith [show (0 : ℝ)≤1/(2 : ℝ)^bits by positivity]
  have hclip := FiniteDist.countableMix_massOn_tvBound (centeredScalarMass width center)
    (centeredScalarMass_nonneg width center (lt_of_lt_of_le zero_lt_one hw))
    (centeredScalarMass_summable width center (lt_of_lt_of_le zero_lt_one hw))
    (centeredScalarMass_sum width center (lt_of_lt_of_le zero_lt_one hw))
    (centeredWindowLaw width center cutoff) (fun offset => centeredGaussianAnchor center+offset) channel _
    (centeredWindowLaw_countable_tv width center cutoff hw hc)
  intro event
  exact (abs_sub_le _ _ _).trans (add_le_add
    ((hfinite.mix (fun offset => channel (centeredGaussianAnchor center+offset))) event)
    (by simpa only [abs_sub_comm] using hclip event))

end
end AFT.RationalNumerics
