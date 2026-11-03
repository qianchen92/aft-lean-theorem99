import AFT.BinomialHistogram

/-! # Continuous inverse-beta mixing of the genuine inhomogeneous histogram -/
namespace AFT.BetaReference
open HistogramGenerating MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance betaHistogramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance betaHistogramSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
variable {Color : Type*} [Fintype Color]

def referenceHistogram (N K : ℕ) (hKN : K≤N) (interior boundary : FiniteDist Color) (theta : ℝ) :
    FiniteDist (Histogram N Color) :=
  if h : 0≤theta ∧ theta≤1 then
    (splitLabelLaw N K interior (convexLaw interior boundary theta h.1 h.2)).map
      (boundedHistogram N (by simp only [Fintype.card_sum,Fintype.card_fin]; omega))
  else labelHistogramKernel N interior boundary ⟨0,by omega⟩

theorem referenceHistogram_weight (N K : ℕ) (hKN : K≤N) (interior boundary : FiniteDist Color)
    (theta : ℝ) (ht : 0≤theta ∧ theta≤1) (hist : Histogram N Color) :
    (referenceHistogram N K hKN interior boundary theta).weight hist=
      ∑ k : Fin (N+1),((K.choose k.val : ℝ)*theta^k.val*(1-theta)^(K-k.val))*
        (labelHistogramKernel N interior boundary k).weight hist := by
  rw [referenceHistogram,dif_pos ht]
  exact split_histogram_binomial N K hKN interior boundary theta ht.1 ht.2 hist

def retainedIntegrand (K n k : ℕ) (b x : ℝ) : ℝ :=
  if k≤K then ((K.choose k : ℝ)*((K+n+1).factorial : ℝ)/(K.factorial*n.factorial)*b^k)*
    ((x-b)^(K-k)*(1-x)^n) else 0

theorem retainedIntegrand_eq (K n k : ℕ) (b x : ℝ) (hx : x≠0) :
    retainedIntegrand K n k b x=inverseBinomial K k b x*density K n x := by
  by_cases hk : k≤K
  · rw [retainedIntegrand,if_pos hk]
    exact (inverseBinomial_mul_density K n k hk b x hx).symm
  · simp only [retainedIntegrand,if_neg hk,inverseBinomial,Nat.choose_eq_zero_of_lt (by omega : K<k),Nat.cast_zero,zero_mul]

theorem retainedIntegrand_continuous (K n k : ℕ) (b : ℝ) : Continuous (retainedIntegrand K n k b) := by
  unfold retainedIntegrand
  split_ifs <;> fun_prop

theorem retainedIntegrand_integral (K n : ℕ) (k : Fin (K+n+2)) (b c : ℝ) :
    (∫ x : ℝ in c..1,retainedIntegrand K n k b x)=retainedWeights K n b c k := by
  unfold retainedWeights retainedIntegrand
  split_ifs
  · rfl
  · exact intervalIntegral.integral_zero

/-- The left side integrates the actual full histogram law of `N-K` interior
coordinates and `K` independent activated coordinates. -/
theorem referenceHistogram_integral (K n : ℕ) (interior boundary : FiniteDist Color)
    (b c : ℝ) (hb : 0<b) (hbc : b≤c) (hc1 : c≤1) (hist : Histogram (K+n+1) Color) :
    (∫ x : ℝ in c..1,(referenceHistogram (K+n+1) K (by omega) interior boundary (b/x)).weight hist*density K n x)=
      ∑ k : Fin (K+n+2),retainedWeights K n b c k*(labelHistogramKernel (K+n+1) interior boundary k).weight hist := by
  calc
    _ = ∫ x : ℝ in c..1,∑ k : Fin (K+n+2),retainedIntegrand K n k b x*
        (labelHistogramKernel (K+n+1) interior boundary k).weight hist := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hc1] at hx
      have hx0 : 0<x := hb.trans_le (hbc.trans hx.1)
      dsimp only
      rw [referenceHistogram_weight (K+n+1) K (by omega) interior boundary (b/x) ⟨div_nonneg hb.le hx0.le,(div_le_one hx0).mpr (hbc.trans hx.1)⟩,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      rw [retainedIntegrand_eq _ _ _ _ _ hx0.ne']
      unfold inverseBinomial
      ring
    _ = _ := by
      rw [intervalIntegral.integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro k _
        rw [intervalIntegral.integral_mul_const,retainedIntegrand_integral]
      · intro k _
        exact ((retainedIntegrand_continuous K n k b).mul continuous_const).intervalIntegrable _ _

/-- Exact continuous mixture and full multinomial histogram TV bound.
The output weights explicitly are integrals of the actual positive product law. -/
theorem inverse_beta_histogram_tv (K n : ℕ) (interior boundary : FiniteDist Color)
    (b c : ℝ) (hb : 0<b) (hbc : b≤c) (hc1 : c<1) :
    ∃ mixed : FiniteDist (Histogram (K+n+1) Color),
      (∀ hist,mixed.weight hist=
        (∫ x : ℝ in c..1,(referenceHistogram (K+n+1) K (by omega) interior boundary (b/x)).weight hist*density K n x)/
          (∫ x : ℝ in c..1,density K n x)) ∧
      FiniteDist.TVBound mixed
        ((FiniteDist.independent fun _ : Fin (K+n+1) => convexLaw interior boundary b hb.le (hbc.trans hc1.le)).map histogram)
        (∫ x : ℝ in (0 : ℝ)..c,density K n x) := by
  obtain ⟨p,hp,htv⟩ := inverse_beta_reference_tv K n b c hb hbc hc1
    (labelHistogramKernel (K+n+1) interior boundary)
  refine ⟨p.mix (labelHistogramKernel (K+n+1) interior boundary),?_,?_⟩
  · intro hist
    rw [referenceHistogram_integral K n interior boundary b c hb hbc hc1.le,Finset.sum_div]
    simp only [FiniteDist.mix_weight,hp]
    apply Finset.sum_congr rfl
    intro k _
    ring
  · simpa only [iid_histogram_binomial] using htv


theorem inverse_beta_histogram_tv_dimension (N K n : ℕ) (hN : K+n+1=N)
    (interior boundary : FiniteDist Color) (b c : ℝ) (hb : 0<b) (hbc : b≤c) (hc1 : c<1) :
    ∃ mixed : FiniteDist (Histogram N Color),
      (∀ hist,mixed.weight hist=
        (∫ x : ℝ in c..1,(referenceHistogram N K (by omega) interior boundary (b/x)).weight hist*density K n x)/
          (∫ x : ℝ in c..1,density K n x)) ∧
      FiniteDist.TVBound mixed
        ((FiniteDist.independent fun _ : Fin N => convexLaw interior boundary b hb.le (hbc.trans hc1.le)).map histogram)
        (∫ x : ℝ in (0 : ℝ)..c,density K n x) := by
  subst N
  exact inverse_beta_histogram_tv K n interior boundary b c hb hbc hc1

end
end AFT.BetaReference
