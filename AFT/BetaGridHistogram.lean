import AFT.BetaGridConditional
import AFT.ReferenceVariation

/-! # Finite beta-grid approximation of the full inhomogeneous histogram -/
namespace AFT.BetaReference
open HistogramGenerating MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance betaGridHistogramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {Color : Type*} [Fintype Color]

def histogramIntegrand (K n : ℕ) (interior boundary : FiniteDist Color) (b x : ℝ)
    (hist : Histogram (K+n+1) Color) : ℝ :=
  ∑ k : Fin (K+n+2),retainedIntegrand K n k b x*(labelHistogramKernel (K+n+1) interior boundary k).weight hist

theorem histogramIntegrand_continuous (K n : ℕ) (interior boundary : FiniteDist Color)
    (b : ℝ) (hist : Histogram (K+n+1) Color) :
    Continuous (fun x => histogramIntegrand K n interior boundary b x hist) := by
  exact continuous_finset_sum _ (fun k _ => (retainedIntegrand_continuous K n k b).mul continuous_const)

theorem histogramIntegrand_eq (K n : ℕ) (interior boundary : FiniteDist Color)
    (b x : ℝ) (hb : 0 ≤ b) (hx : 0 < x) (hbx : b ≤ x) (hist : Histogram (K+n+1) Color) :
    histogramIntegrand K n interior boundary b x hist=
      density K n x*(referenceHistogram (K+n+1) K (by omega) interior boundary (b/x)).weight hist := by
  rw [referenceHistogram_weight _ _ _ _ _ _ ⟨div_nonneg hb hx.le,(div_le_one hx).mpr hbx⟩,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [retainedIntegrand_eq _ _ _ _ _ hx.ne']
  unfold inverseBinomial
  ring

theorem event_difference_le_l1 {State : Type*} [Fintype State]
    (first second : FiniteDist State) (event : Finset State) :
    |first.event event-second.event event| ≤ ∑ state,|first.weight state-second.weight state| := by
  unfold FiniteDist.event
  rw [← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ _) (fun _ _ _ => abs_nonneg _))

/-- The actual finite grid mixture, including every histogram degree, is
close to uniform-binomial mixing with an explicit mesh error. -/
theorem grid_histogram_tv (K n M J : ℕ) (hM : 0 < M) (hJ : 0 < J) (hJM : J < M)
    (interior boundary : FiniteDist Color) (b : ℝ) (hb : 0 < b) (hbc : b ≤ (J : ℝ)/M) :
    FiniteDist.TVBound
      ((gridTailLaw K n M J hM hJM).mix fun j => referenceHistogram (K+n+1) K (by omega)
        interior boundary (b/((j.val+1 : ℕ)/M)))
      ((FiniteDist.independent fun _ : Fin (K+n+1) =>
        convexLaw interior boundary b hb.le (hbc.trans (by
          exact (div_lt_one (by exact_mod_cast hM : (0 : ℝ) < M)).mpr (by exact_mod_cast hJM) |>.le))).map histogram)
      ((∫ x : ℝ in (0 : ℝ)..(J : ℝ)/M,density K n x)+2*K*b/(((J : ℝ)/M)^2*M)) := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hcp : (0 : ℝ) < (J : ℝ)/M := div_pos (by exact_mod_cast hJ) hMp
  have hc1 : (J : ℝ)/M < 1 := (div_lt_one hMp).mpr (by exact_mod_cast hJM)
  obtain ⟨continuousLaw,hlaw,huniform⟩ := inverse_beta_histogram_tv K n interior boundary b ((J : ℝ)/M) hb hbc hc1
  have hgrid : FiniteDist.TVBound
      ((gridTailLaw K n M J hM hJM).mix fun j => referenceHistogram (K+n+1) K (by omega)
        interior boundary (b/((j.val+1 : ℕ)/M))) continuousLaw (2*K*b/(((J : ℝ)/M)^2*M)) := by
    intro event
    let value := fun j : ℕ => (referenceHistogram (K+n+1) K (by omega) interior boundary (b/((j+1 : ℕ)/M))).event event
    let integrand := fun x => ∑ hist ∈ event,histogramIntegrand K n interior boundary b x hist
    have hcont : Continuous integrand := continuous_finset_sum _ (fun hist _ => histogramIntegrand_continuous K n interior boundary b hist)
    have hint : continuousLaw.event event=(∫ x : ℝ in (J : ℝ)/M..1,integrand x)/(∫ x : ℝ in (J : ℝ)/M..1,density K n x) := by
      unfold FiniteDist.event
      simp_rw [hlaw]
      rw [← Finset.sum_div,← intervalIntegral.integral_finset_sum]
      · congr 1
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le hc1.le] at hx
        apply Finset.sum_congr rfl
        intro hist _
        rw [histogramIntegrand_eq _ _ _ _ _ _ hb.le (hcp.trans_le hx.1) (hbc.trans hx.1)]
        ring
      · intro hist _
        apply (histogramIntegrand_continuous K n interior boundary b hist).intervalIntegrable _ _ |>.congr
        intro x hx
        rw [Set.uIoc_of_le hc1.le] at hx
        dsimp only
        rw [histogramIntegrand_eq _ _ _ _ _ _ hb.le (hcp.trans hx.1) (hbc.trans hx.1.le)]
        ring
    rw [FiniteDist.event_mix,hint]
    apply gridTailLaw_quadrature K n M J hM hJM value integrand hcont
    intro j hj x hx
    have hji := Finset.mem_Ico.mp hj
    have hcx : (J : ℝ)/M ≤ x := (div_le_div_of_nonneg_right (by exact_mod_cast hji.1) hMp.le).trans hx.1
    have hcu : (J : ℝ)/M ≤ ((j+1 : ℕ) : ℝ)/M := div_le_div_of_nonneg_right (by exact_mod_cast (by omega : J ≤ j+1)) hMp.le
    have hx1 : x ≤ 1 := hx.2.trans ((div_le_one hMp).mpr (by exact_mod_cast (by omega : j+1 ≤ M)))
    have hx0 : 0 ≤ x := (hcp.trans_le hcx).le
    have hd : 0 ≤ density K n x := by unfold density; exact mul_nonneg (by positivity) (pow_nonneg (sub_nonneg.mpr hx1) _)
    have hg : integrand x=density K n x*(referenceHistogram (K+n+1) K (by omega) interior boundary (b/x)).event event := by
      simp only [integrand,FiniteDist.event]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro hist _
      exact histogramIntegrand_eq _ _ _ _ _ _ hb.le (hcp.trans_le hcx) (hbc.trans hcx) hist
    rw [hg,← mul_sub,abs_mul,abs_of_nonneg hd]
    have hdiff := (event_difference_le_l1
      (referenceHistogram (K+n+1) K (by omega) interior boundary (b/((j+1 : ℕ)/M)))
      (referenceHistogram (K+n+1) K (by omega) interior boundary (b/x)) event).trans
      (inverseBeta_histogram_l1_le (K+n+1) K (by omega) interior boundary b ((J : ℝ)/M)
        ((j+1 : ℕ)/M) x hb.le hcp hbc hcu hcx)
    have hmesh : |((j+1 : ℕ) : ℝ)/M-x| ≤ 1/M := by
      rw [abs_of_nonneg (sub_nonneg.mpr hx.2)]
      have he : ((j+1 : ℕ) : ℝ)/M-(j : ℝ)/M=1/M := by push_cast; ring
      linarith [hx.1]
    have herr : |value j-(referenceHistogram (K+n+1) K (by omega) interior boundary (b/x)).event event| ≤
        2*K*b/(((J : ℝ)/M)^2*M) := hdiff.trans <| (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hmesh (by positivity : (0 : ℝ) ≤ 2*K*b)) (by positivity)).trans_eq (by ring)
    exact (mul_le_mul_of_nonneg_left herr hd).trans_eq (mul_comm _ _)
  intro event
  have hh := (abs_add_le
    (((gridTailLaw K n M J hM hJM).mix fun j => referenceHistogram (K+n+1) K (by omega) interior boundary (b/((j.val+1 : ℕ)/M))).event event-continuousLaw.event event)
    (continuousLaw.event event-((FiniteDist.independent fun _ : Fin (K+n+1) => convexLaw interior boundary b hb.le (hbc.trans hc1.le)).map histogram).event event))
  have hg := hgrid event
  have hu := huniform event
  simp only [sub_add_sub_cancel] at hh
  exact hh.trans (by linarith)

/-- The same finite-grid statement with an explicitly named population. -/
theorem grid_histogram_tv_dimension (N K n M J : ℕ) (hN : K+n+1=N)
    (hM : 0 < M) (hJ : 0 < J) (hJM : J < M)
    (interior boundary : FiniteDist Color) (b : ℝ) (hb : 0 < b) (hbc : b ≤ (J : ℝ)/M) :
    FiniteDist.TVBound
      ((gridTailLaw K n M J hM hJM).mix fun j => referenceHistogram N K (by omega)
        interior boundary (b/((j.val+1 : ℕ)/M)))
      ((FiniteDist.independent fun _ : Fin N =>
        convexLaw interior boundary b hb.le (hbc.trans (by
          exact (div_lt_one (by exact_mod_cast hM : (0 : ℝ) < M)).mpr (by exact_mod_cast hJM) |>.le))).map histogram)
      ((∫ x : ℝ in (0 : ℝ)..(J : ℝ)/M,density K n x)+2*K*b/(((J : ℝ)/M)^2*M)) := by
  subst N
  exact grid_histogram_tv K n M J hM hJ hJM interior boundary b hb hbc

end
end AFT.BetaReference
