import AFT.RootConvolutionStability
import AFT.ClippedConvolution

/-! # Numerical stability of actual root marginal probability queries -/
namespace AFT.RootSlice
open GaussianSource
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance rootMarginalStabilityFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {Source : Type*} [Fintype Source]

private theorem finite_weight_le_one (law : FiniteDist Source) (point : Source) : law.weight point ≤ 1 := by
  simpa only [law.sum_one] using Finset.single_le_sum
    (fun color (_ : color ∈ Finset.univ) => law.nonneg color) (Finset.mem_univ point)

private theorem ratio_error (first second firstMass secondMass : ℝ)
    (hfirst : 0 < firstMass) (hsecond : 0 < secondMass)
    (hnum : 0 ≤ second ∧ second ≤ secondMass) :
    |first/firstMass-second/secondMass| ≤
      (|first-second|+|firstMass-secondMass|)/firstMass := by
  have heq : first/firstMass-second/secondMass=
      ((first-second)+(second/secondMass)*(secondMass-firstMass))/firstMass := by field_simp; ring
  rw [heq,abs_div,abs_of_pos hfirst]
  apply div_le_div_of_nonneg_right _ hfirst.le
  apply (abs_add_le _ _).trans
  have hh : 0 ≤ second/secondMass ∧ second/secondMass ≤ 1 :=
    ⟨div_nonneg hnum.1 hsecond.le,(div_le_one hsecond).mpr hnum.2⟩
  rw [abs_mul,abs_of_nonneg hh.1,abs_sub_comm secondMass firstMass]
  have hm := mul_le_mul_of_nonneg_right hh.2 (abs_nonneg (firstMass-secondMass))
  linarith

/-- An actual root marginal query is stable using only the zero-sum
normalizer. There is no division by an individual root marginal atom. -/
theorem marginalLaw_point_error (first second : FiniteDist Source) (score : Source → ℤ)
    (count : ℕ) (hc : 0 < count)
    (hfirst : 0 < sumProbability first score count 0)
    (hsecond : 0 < sumProbability second score count 0)
    (error : ℝ) (he : (∑ point,|first.weight point-second.weight point|) ≤ error)
    (point : Source) :
    |(marginalLaw first score count hc hfirst).weight point-
      (marginalLaw second score count hc hsecond).weight point| ≤
      2*(count : ℝ)*error/sumProbability first score count 0 := by
  have he0 : 0 ≤ error := (Finset.sum_nonneg fun _ _ => abs_nonneg _).trans he
  have hscalar : |first.weight point-second.weight point| ≤ error :=
    (Finset.single_le_sum (fun _ _ => abs_nonneg _) (Finset.mem_univ point)).trans he
  have hsum := (sumProbability_l1_error first second score (count-1) (-score point)).trans
    (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _))
  have hmass := (sumProbability_l1_error first second score count 0).trans
    (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _))
  have hb0 : 0 ≤ sumProbability first score (count-1) (-score point) := FiniteDist.eventMass_nonneg _ _
  have hb1 : sumProbability first score (count-1) (-score point) ≤ 1 := finite_eventMass_le_one _ _
  have hc0 := second.nonneg point
  have hc1 := finite_weight_le_one second point
  have hnum : |first.weight point*sumProbability first score (count-1) (-score point)-
      second.weight point*sumProbability second score (count-1) (-score point)| ≤ (count : ℝ)*error := by
    have hid : first.weight point*sumProbability first score (count-1) (-score point)-
        second.weight point*sumProbability second score (count-1) (-score point)=
      (first.weight point-second.weight point)*sumProbability first score (count-1) (-score point)+
        second.weight point*(sumProbability first score (count-1) (-score point)-sumProbability second score (count-1) (-score point)) := by ring
    rw [hid]
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul,abs_of_nonneg hb0,abs_of_nonneg hc0]
    calc
      _ ≤ error*1+1*((count-1 : ℕ) : ℝ)*error := by
        have hleft := mul_le_mul hscalar hb1 hb0 he0
        have hright := mul_le_mul hc1 hsum (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
        nlinarith
      _ = _ := by rw [Nat.cast_sub (by omega : 1 ≤ count),Nat.cast_one]; ring
  have ht0 : 0 ≤ second.weight point*sumProbability second score (count-1) (-score point) :=
    mul_nonneg hc0 (FiniteDist.eventMass_nonneg _ _)
  have ht1 : second.weight point*sumProbability second score (count-1) (-score point) ≤
      sumProbability second score count 0 := by
    apply (div_le_one hsecond).mp
    rw [← marginalLaw_weight second score count hc hsecond]
    exact finite_weight_le_one _ _
  rw [marginalLaw_weight,marginalLaw_weight]
  apply (ratio_error _ _ _ _ hfirst hsecond ⟨ht0,ht1⟩).trans
  apply div_le_div_of_nonneg_right _ hfirst.le
  linarith

end
end AFT.RootSlice
