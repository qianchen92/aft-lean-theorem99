import AFT.CountableFiniteProduct
import AFT.CountableFiniteChannel

/-! # Total variation for products of genuine countable source laws -/
namespace AFT
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem countableTensor_l1_le {First Second : Type*}
    (p q : First → ℝ) (r s : Second → ℝ)
    (hp : ∀ x,0≤p x) (hq : ∀ x,0≤q x) (hr : ∀ x,0≤r x) (hs : ∀ x,0≤s x)
    (hps : Summable p) (hqs : Summable q) (hrs : Summable r) (hss : Summable s)
    (hq1 : ∑' x,q x=1) (hr1 : ∑' x,r x=1) :
    (∑' point : First × Second,|p point.1*r point.2-q point.1*s point.2|)≤
      (∑' x,|p x-q x|)+(∑' x,|r x-s x|) := by
  have hfirst := (hps.sub hqs).norm
  have hsecond := (hrs.sub hss).norm
  simp only [Real.norm_eq_abs] at hfirst hsecond
  have ha := hfirst.mul_of_nonneg hrs (fun _ => abs_nonneg _) hr
  have hb := hqs.mul_of_nonneg hsecond hq (fun _ => abs_nonneg _)
  have hh := ((hps.mul_of_nonneg hrs hp hr).sub (hqs.mul_of_nonneg hss hq hs)).norm
  simp only [Real.norm_eq_abs] at hh
  have hbound (point : First × Second) :
      |p point.1*r point.2-q point.1*s point.2|≤
        |p point.1-q point.1| *r point.2+q point.1*|r point.2-s point.2| := by
    calc
      _ = |(p point.1-q point.1)*r point.2+q point.1*(r point.2-s point.2)| := by congr 1; ring
      _ ≤ |(p point.1-q point.1)*r point.2|+|q point.1*(r point.2-s point.2)| := abs_add_le _ _
      _ = _ := by rw [abs_mul,abs_mul,abs_of_nonneg (hr _),abs_of_nonneg (hq _)]
  apply (hh.tsum_le_tsum hbound (ha.add hb)).trans_eq
  rw [ha.tsum_add hb,← hfirst.tsum_mul_tsum hrs ha,← hqs.tsum_mul_tsum hsecond hb,hr1,hq1,mul_one,one_mul]

/-- No finite support assumption: every unbounded source coordinate is
included before applying the physical output kernel. -/
theorem countableFiniteProduct_l1_le {State : Type*} (count : ℕ)
    (first second : Fin count → State → ℝ)
    (hf : ∀ i x,0≤first i x) (hg : ∀ i x,0≤second i x)
    (hfs : ∀ i,Summable (first i)) (hgs : ∀ i,Summable (second i))
    (hf1 : ∀ i,∑' x,first i x=1) (hg1 : ∀ i,∑' x,second i x=1) :
    (∑' word : Fin count → State,|(∏ i,first i (word i))-(∏ i,second i (word i))|)≤
      ∑ i,∑' x,|first i x-second i x| := by
  induction count with
  | zero => simp
  | succ count ih =>
    have hp := countableFiniteProduct_summable_sum count (fun i => first i.succ)
      (fun i => hf i.succ) (fun i => hfs i.succ)
    have hq := countableFiniteProduct_summable_sum count (fun i => second i.succ)
      (fun i => hg i.succ) (fun i => hgs i.succ)
    have hp1 : (∑' word : Fin count → State,∏ i : Fin count,first i.succ (word i))=1 := by
      rw [hp.2]; simp only [hf1,Finset.prod_const_one]
    have hh := countableTensor_l1_le (first 0) (second 0)
      (fun word : Fin count → State => ∏ i : Fin count,first i.succ (word i))
      (fun word : Fin count → State => ∏ i : Fin count,second i.succ (word i))
      (hf 0) (hg 0) (fun word => Finset.prod_nonneg fun i _ => hf i.succ (word i))
      (fun word => Finset.prod_nonneg fun i _ => hg i.succ (word i))
      (hfs 0) (hgs 0) hp.1 hq.1 (hg1 0) hp1
    rw [← (Fin.consEquiv (fun _ : Fin (count+1) => State)).tsum_eq]
    simp only [Fin.prod_univ_succ,Fin.consEquiv_apply,Fin.cons_zero,Fin.cons_succ]
    apply hh.trans
    rw [Fin.sum_univ_succ]
    exact add_le_add le_rfl (ih (fun i => first i.succ) (fun i => second i.succ)
      (fun i => hf i.succ) (fun i => hg i.succ) (fun i => hfs i.succ) (fun i => hgs i.succ)
      (fun i => hf1 i.succ) (fun i => hg1 i.succ))

end
end AFT
