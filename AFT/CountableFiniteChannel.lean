import AFT.TotalVariation
import AFT.MixtureTail
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! # Actual countable source laws through finite physical output channels -/
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Source Output : Type*} [Fintype Output]

private theorem weight_le_one (law : FiniteDist Output) (output : Output) : law.weight output ≤ 1 := by
  rw [← law.sum_one]
  exact Finset.single_le_sum (fun point _ => law.nonneg point) (Finset.mem_univ output)

private theorem countable_channel_summable (mass : Source → ℝ)
    (hmass : Summable mass) (channel : Source → FiniteDist Output) (output : Output) :
    Summable (fun source => mass source*(channel source).weight output) := by
  apply Summable.of_norm_bounded hmass.norm
  intro source
  simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg ((channel source).nonneg output)]
  exact mul_le_of_le_one_right (abs_nonneg _) (weight_le_one _ _)

/-- A genuine normalized finite output law for an unbounded integer source. -/
def countableMix (mass : Source → ℝ) (hnonneg : ∀ source,0 ≤ mass source)
    (hsum : Summable mass) (hone : ∑' source,mass source=1)
    (channel : Source → FiniteDist Output) : FiniteDist Output where
  weight output := ∑' source,mass source*(channel source).weight output
  nonneg output := tsum_nonneg fun source => mul_nonneg (hnonneg source) ((channel source).nonneg output)
  sum_one := by
    rw [← tsum_fintype (L := .unconditional Output) (f := fun output : Output => ∑' source,mass source*(channel source).weight output)]
    have hs : Summable (fun point : Output × Source => mass point.2*(channel point.2).weight point.1) := by
      exact (summable_prod_of_nonneg (fun point => mul_nonneg (hnonneg point.2) ((channel point.2).nonneg point.1))).mpr
        ⟨fun output => countable_channel_summable mass hsum channel output,(hasSum_fintype _).summable⟩
    rw [← Summable.tsum_comm hs]
    simp only [tsum_fintype,← Finset.mul_sum,FiniteDist.sum_one,mul_one,hone]

/-- Markov postprocessing never increases the full countable L1 distance. -/
theorem countableMix_l1_le (first second : Source → ℝ)
    (hf : ∀ source,0 ≤ first source) (hg : ∀ source,0 ≤ second source)
    (hsf : Summable first) (hsg : Summable second)
    (hfone : ∑' source,first source=1) (hgone : ∑' source,second source=1)
    (channel : Source → FiniteDist Output) :
    (∑ output,|(countableMix first hf hsf hfone channel).weight output-
      (countableMix second hg hsg hgone channel).weight output|) ≤ ∑' source,|first source-second source| := by
  have hd : Summable (fun source => |first source-second source|) := by
    simpa only [Real.norm_eq_abs] using (hsf.sub hsg).norm
  have hparts (output : Output) := countable_channel_summable (fun source => |first source-second source|) hd channel output
  have hbound (output : Output) :
      |(countableMix first hf hsf hfone channel).weight output-
        (countableMix second hg hsg hgone channel).weight output| ≤ 
      ∑' source,|first source-second source| *(channel source).weight output := by
    change |(∑' source,first source*(channel source).weight output)-
      (∑' source,second source*(channel source).weight output)| ≤ _
    rw [← (countable_channel_summable first hsf channel output).tsum_sub
      (countable_channel_summable second hsg channel output)]
    have hh := norm_tsum_le_tsum_norm (countable_channel_summable (fun source => first source-second source) (hsf.sub hsg) channel output).norm
    simp_rw [← sub_mul]
    simpa only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (FiniteDist.nonneg _ _)] using hh
  apply (Finset.sum_le_sum fun output _ => hbound output).trans_eq
  rw [← tsum_fintype (L := .unconditional Output) (f := fun output : Output => ∑' source,|first source-second source| *(channel source).weight output)]
  have hs : Summable (fun point : Output × Source => |first point.2-second point.2| *(channel point.2).weight point.1) :=
    (summable_prod_of_nonneg (fun point => mul_nonneg (abs_nonneg _) ((channel point.2).nonneg point.1))).mpr
      ⟨hparts,(hasSum_fintype _).summable⟩
  rw [← Summable.tsum_comm hs]
  simp only [tsum_fintype,← Finset.mul_sum,FiniteDist.sum_one,mul_one]

/-- The bound applies uniformly to every public-input dependent physical
channel, without resampling or examining the protected source. -/
theorem countableMix_tvBound (first second : Source → ℝ)
    (hf : ∀ source,0 ≤ first source) (hg : ∀ source,0 ≤ second source)
    (hsf : Summable first) (hsg : Summable second)
    (hfone : ∑' source,first source=1) (hgone : ∑' source,second source=1)
    (channel : Source → FiniteDist Output) (error : ℝ)
    (herror : (∑' source,|first source-second source|)/2 ≤ error) :
    TVBound (countableMix first hf hsf hfone channel) (countableMix second hg hsg hgone channel) error := by
  apply (tvBound_iff_totalVariation_le _ _ _).mpr
  rw [totalVariation_eq_half_l1]
  exact (div_le_div_of_nonneg_right (countableMix_l1_le first second hf hg hsf hsg hfone hgone channel)
    (by norm_num)).trans herror

end
end AFT.FiniteDist
