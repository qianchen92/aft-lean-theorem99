import AFT.HistogramGenerating
import AFT.BetaReference

/-! # The common conditional-label kernel of the actual beta reference -/
namespace AFT.BetaReference
open HistogramGenerating RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance binomialHistogramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance binomialHistogramSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
variable {Color : Type*} [Fintype Color]

def convexLaw (interior boundary : FiniteDist Color) (theta : ℝ) (hzero : 0≤theta) (hone : theta≤1) : FiniteDist Color where
  weight color := (1-theta)*interior.weight color+theta*boundary.weight color
  nonneg color := add_nonneg (mul_nonneg (sub_nonneg.mpr hone) (interior.nonneg color)) (mul_nonneg hzero (boundary.nonneg color))
  sum_one := by simp only [Finset.sum_add_distrib,← Finset.mul_sum,interior.sum_one,boundary.sum_one]; ring

def splitLabelLaw (N k : ℕ) (interior boundary : FiniteDist Color) :
    FiniteDist ((Fin (N-k) ⊕ Fin k) → Color) :=
  FiniteDist.independent (Sum.elim (fun _ => interior) (fun _ => boundary))

def labelHistogramKernel (N : ℕ) (interior boundary : FiniteDist Color) (k : Fin (N+1)) :
    FiniteDist (Histogram N Color) :=
  (splitLabelLaw N k interior boundary).map (boundedHistogram N (by
    simp only [Fintype.card_sum,Fintype.card_fin]
    omega))

theorem splitLabelLaw_generating (N k : ℕ) (interior boundary : FiniteDist Color) :
    generating (splitLabelLaw N k interior boundary)=profileForm interior.weight^(N-k)*profileForm boundary.weight^k := by
  rw [splitLabelLaw,generating_independent,Fintype.prod_sum_type]
  simp only [Sum.elim_inl,Sum.elim_inr,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

theorem labelHistogramKernel_weight (N : ℕ) (interior boundary : FiniteDist Color) (k : Fin (N+1)) (hist : Histogram N Color) :
    (labelHistogramKernel N interior boundary k).weight hist=
      MvPolynomial.coeff (histogramExponent N hist) (profileForm interior.weight^(N-k.val)*profileForm boundary.weight^k.val) := by
  rw [← splitLabelLaw_generating,generating_coeff]
  rfl

theorem convexLaw_profile (interior boundary : FiniteDist Color) (theta : ℝ) (hzero : 0≤theta) (hone : theta≤1) :
    profileForm (convexLaw interior boundary theta hzero hone).weight=
      MvPolynomial.C (1-theta)*profileForm interior.weight+MvPolynomial.C theta*profileForm boundary.weight := by
  change profileForm ((1-theta) • interior.weight+theta • boundary.weight)=_
  rw [map_add,LinearMap.map_smul,LinearMap.map_smul]
  simp only [Algebra.smul_def,MvPolynomial.algebraMap_eq]

theorem split_generating_binomial (N K : ℕ) (hKN : K≤N) (interior boundary : FiniteDist Color)
    (theta : ℝ) (hzero : 0≤theta) (hone : theta≤1) :
    generating (splitLabelLaw N K interior (convexLaw interior boundary theta hzero hone))=
      ∑ k : Fin (N+1),MvPolynomial.C ((K.choose k.val : ℝ)*theta^k.val*(1-theta)^(K-k.val))*
        (profileForm interior.weight^(N-k.val)*profileForm boundary.weight^k.val) := by
  rw [splitLabelLaw_generating,convexLaw_profile]
  rw [add_comm (MvPolynomial.C (1-theta)*_),add_pow,Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => MvPolynomial.C ((K.choose k : ℝ)*theta^k*(1-theta)^(K-k))*(profileForm interior.weight^(N-k)*profileForm boundary.weight^k))]
  calc
    _ = ∑ k∈Finset.range (K+1),MvPolynomial.C ((K.choose k : ℝ)*theta^k*(1-theta)^(K-k))*
        (profileForm interior.weight^(N-k)*profileForm boundary.weight^k) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkK : k≤K := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hk
      have he : N-K+(K-k)=N-k := by omega
      simp only [mul_pow,← map_pow,map_mul]
      have hh : profileForm interior.weight^(N-K)*profileForm interior.weight^(K-k)=profileForm interior.weight^(N-k) := by rw [← pow_add,he]
      calc
        _ = (MvPolynomial.C (K.choose k : ℝ)*MvPolynomial.C (theta^k)*MvPolynomial.C ((1-theta)^(K-k)))*
          ((profileForm interior.weight^(N-K)*profileForm interior.weight^(K-k))*profileForm boundary.weight^k) := by simp only [map_natCast]; ring
        _ = _ := by rw [hh]
    _ = _ := by
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro k hk hnot
      have hkK : K<k := by simpa only [Finset.mem_range,not_lt,Nat.succ_le_iff] using hnot
      simp only [Nat.choose_eq_zero_of_lt hkK,Nat.cast_zero,zero_mul,map_zero]

/-- Complete histograms of the inhomogeneous reference use exactly the
same label kernel as iid sampling; only the boundary-count law differs. -/
theorem split_histogram_binomial (N K : ℕ) (hKN : K≤N) (interior boundary : FiniteDist Color)
    (theta : ℝ) (hzero : 0≤theta) (hone : theta≤1) (hist : Histogram N Color) :
    ((splitLabelLaw N K interior (convexLaw interior boundary theta hzero hone)).map
      (boundedHistogram N (by simp only [Fintype.card_sum,Fintype.card_fin]; omega))).weight hist=
      ∑ k : Fin (N+1),((K.choose k.val : ℝ)*theta^k.val*(1-theta)^(K-k.val))*
        (labelHistogramKernel N interior boundary k).weight hist := by
  rw [← generating_coeff,split_generating_binomial N K hKN]
  simp only [MvPolynomial.coeff_sum,MvPolynomial.coeff_C_mul,labelHistogramKernel_weight]


theorem iid_histogram_binomial (N : ℕ) (interior boundary : FiniteDist Color)
    (theta : ℝ) (hzero : 0≤theta) (hone : theta≤1) :
    ((FiniteDist.independent fun _ : Fin N => convexLaw interior boundary theta hzero hone).map histogram)=
      (binomialCount N theta hzero hone).mix (labelHistogramKernel N interior boundary) := by
  have h := histogram_law_eq_of_generating_eq N (by simp) (by simp)
    (FiniteDist.independent fun _ : Fin N => convexLaw interior boundary theta hzero hone)
    (splitLabelLaw N N interior (convexLaw interior boundary theta hzero hone)) (by
      rw [generating_independent,splitLabelLaw_generating]
      simp only [Nat.sub_self,pow_zero,one_mul,Finset.prod_const,Finset.card_univ,Fintype.card_fin])
  have hhist : boundedHistogram (Color:=Color) N (by simp : Fintype.card (Fin N)≤N)=histogram :=
    funext (boundedHistogram_fin N)
  rw [hhist] at h
  rw [h]
  ext hist
  exact split_histogram_binomial N N le_rfl interior boundary theta hzero hone hist

end
end AFT.BetaReference
