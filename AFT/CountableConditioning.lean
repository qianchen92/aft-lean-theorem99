import AFT.CountableNormalizedTilt

/-! # Normalization after genuine countable mass deletion -/
namespace AFT
open scoped BigOperators

/-- Deleting any nonnegative part of a countable mass and renormalizing
changes its probability law by at most the deleted fraction. -/
theorem normalized_deleted_total_variation {State : Type*}
    (full retained : State → ℝ) (_hfull : ∀ state,0≤ full state)
    (hretained : ∀ state,0≤ retained state) (hle : ∀ state,retained state≤ full state)
    (hfull_sum : Summable full) (hretained_pos : 0<∑' state,retained state) :
    (∑' state,|retained state/(∑' x,retained x)-full state/(∑' x,full x)|)/2≤
      ((∑' state,full state)-(∑' state,retained state))/(∑' state,full state) := by
  let total := ∑' state,full state
  let kept := ∑' state,retained state
  have hs := Summable.of_nonneg_of_le hretained hle hfull_sum
  have htotal : kept≤ total := hs.tsum_le_tsum hle hfull_sum
  have hkpos : 0< kept := hretained_pos
  have htpos : 0< total := hretained_pos.trans_le htotal
  have hp (state : State) :
      |retained state/kept-full state/total|≤
        (full state-retained state)/total+retained state*((total-kept)/(total*kept)) := by
    have ha : retained state/kept-retained state/total≥0 :=
      sub_nonneg.mpr (div_le_div_of_nonneg_left (hretained state) hretained_pos htotal)
    have hb : (retained state-full state)/total≤0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hle state)) htpos.le
    calc
      _ = |(retained state/kept-retained state/total)+(retained state-full state)/total| := by congr 1; ring
      _ ≤ |retained state/kept-retained state/total|+|(retained state-full state)/total| := abs_add_le _ _
      _ = _ := by rw [abs_of_nonneg ha,abs_of_nonpos hb]; field_simp [htpos.ne',hkpos.ne']; ring
  have hnorm := ((hs.div_const kept).sub (hfull_sum.div_const total)).norm
  have hmajor := ((hfull_sum.sub hs).div_const total).add (hs.mul_right ((total-kept)/(total*kept)))
  have hsum := hnorm.tsum_le_tsum (fun state => by simpa only [Real.norm_eq_abs] using hp state) hmajor
  simp only [Real.norm_eq_abs] at hsum
  rw [Summable.tsum_add ((hfull_sum.sub hs).div_const total) (hs.mul_right _),tsum_div_const,
    hfull_sum.tsum_sub hs,tsum_mul_right] at hsum
  change (∑' state,|retained state/kept-full state/total|)≤
    (total-kept)/total+kept*((total-kept)/(total*kept)) at hsum
  have he : (total-kept)/total+kept*((total-kept)/(total*kept))=2*((total-kept)/total) := by
    field_simp [htpos.ne',hkpos.ne']; ring
  rw [he] at hsum
  change (∑' state,|retained state/kept-full state/total|)/2≤(total-kept)/total
  linarith

end AFT
