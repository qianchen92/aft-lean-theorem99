import AFT.CountableFiniteChannel
import AFT.CountableConvolution

/-! # Independent countable sources and additive padding through one channel -/
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {First Second Output : Type*} [Fintype Output]

theorem countableChannel_summable (mass : First → ℝ) (hs : Summable mass)
    (channel : First → FiniteDist Output) (output : Output) :
    Summable (fun point => mass point*(channel point).weight output) := by
  apply Summable.of_norm_bounded hs.norm
  intro point
  simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg ((channel point).nonneg output)]
  apply mul_le_of_le_one_right (abs_nonneg _)
  rw [← (channel point).sum_one]
  exact Finset.single_le_sum (fun value _ => (channel point).nonneg value) (Finset.mem_univ output)

theorem countableMix_reindex (equiv : First ≃ Second) (mass : Second → ℝ)
    (hm : ∀ point,0 ≤ mass point) (hs : Summable mass) (h1 : ∑' point,mass point=1)
    (channel : Second → FiniteDist Output) :
    countableMix (fun point => mass (equiv point)) (fun point => hm (equiv point))
      (equiv.summable_iff.mpr hs) (by rw [equiv.tsum_eq,h1]) (fun point => channel (equiv point))=
      countableMix mass hm hs h1 channel := by
  ext output
  exact equiv.tsum_eq (fun point => mass point*(channel point).weight output)

theorem countableMix_product (first : First → ℝ) (second : Second → ℝ)
    (hf : ∀ point,0≤first point) (hg : ∀ point,0≤second point)
    (hsf : Summable first) (hsg : Summable second)
    (hf1 : ∑' point,first point=1) (hg1 : ∑' point,second point=1)
    (channel : First × Second → FiniteDist Output) :
    countableMix (fun point : First × Second => first point.1*second point.2)
      (fun point => mul_nonneg (hf _) (hg _)) (hsf.mul_of_nonneg hsg hf hg)
      (by rw [← hsf.tsum_mul_tsum hsg (hsf.mul_of_nonneg hsg hf hg),hf1,hg1,mul_one]) channel=
      countableMix first hf hsf hf1 (fun point => countableMix second hg hsg hg1 (fun extra => channel (point,extra))) := by
  ext output
  have hs := countableChannel_summable _ (hsf.mul_of_nonneg hsg hf hg) channel output
  change (∑' point : First × Second,first point.1*second point.2*(channel point).weight output)=_
  rw [hs.tsum_prod]
  simp only [countableMix,tsum_mul_left,mul_assoc]

theorem countableMix_comm (first : First → ℝ) (second : Second → ℝ)
    (hf : ∀ point,0≤first point) (hg : ∀ point,0≤second point)
    (hsf : Summable first) (hsg : Summable second)
    (hf1 : ∑' point,first point=1) (hg1 : ∑' point,second point=1)
    (channel : First → Second → FiniteDist Output) :
    countableMix first hf hsf hf1 (fun point => countableMix second hg hsg hg1 (channel point))=
      countableMix second hg hsg hg1 (fun extra => countableMix first hf hsf hf1 (fun point => channel point extra)) := by
  ext output
  have hs := countableChannel_summable _ (hsf.mul_of_nonneg hsg hf hg)
    (fun point : First × Second => channel point.1 point.2) output
  change (∑' point,first point*(∑' extra,second extra*(channel point extra).weight output))=_
  calc
    _ = ∑' point,∑' extra,first point*second extra*(channel point extra).weight output := by
      apply tsum_congr
      intro point
      rw [← tsum_mul_left]
      simp only [mul_assoc]
    _ = ∑' extra,∑' point,first point*second extra*(channel point extra).weight output := hs.tsum_comm.symm
    _ = _ := by
      apply tsum_congr
      intro extra
      change _=second extra*(∑' point,first point*(channel point extra).weight output)
      rw [← tsum_mul_left]
      apply tsum_congr
      intro point
      ring

private def paddingCoordinates {State : Type*} [AddCommGroup State] : (State × State) ≃ (State × State) where
  toFun point := (point.2,point.1-point.2)
  invFun point := (point.1+point.2,point.1)
  left_inv point := by ext <;> simp
  right_inv point := by ext <;> simp

/-- A convolution followed by any finite channel is exactly the law of
independent source and padding followed by addition. -/
theorem countableMix_convolution {State : Type*} [AddCommGroup State]
    (first second : State → ℝ)
    (hf : ∀ point,0≤first point) (hg : ∀ point,0≤second point)
    (hsf : Summable first) (hsg : Summable second)
    (hf1 : ∑' point,first point=1) (hg1 : ∑' point,second point=1)
    (channel : State → FiniteDist Output) :
    countableMix (countableConvolution first second) (countableConvolution_nonneg first second hf hg)
      (countableConvolution_summable first second hf hg hsf hsg)
      (by rw [countableConvolution_sum first second hf hg hsf hsg,hf1,hg1,mul_one]) channel=
      countableMix first hf hsf hf1 (fun source => countableMix second hg hsg hg1 (fun padding => channel (source+padding))) := by
  have hs := countableChannel_summable _ (hsf.mul_of_nonneg hsg hf hg)
    (fun point : State × State => channel (point.1+point.2))
  have hcoords (output : Output) := paddingCoordinates.summable_iff.mpr (hs output)
  ext output
  change (∑' target,(∑' source,first source*second (target-source))*(channel target).weight output)=_
  simp_rw [← tsum_mul_right]
  have hc : Summable (fun point : State × State => first point.2*second (point.1-point.2)*(channel point.1).weight output) := by
    simpa [paddingCoordinates,Function.comp_def] using hcoords output
  rw [← hc.tsum_prod]
  have he := paddingCoordinates.tsum_eq
    (fun point : State × State => first point.1*second point.2*(channel (point.1+point.2)).weight output)
  have hcancel (a b : State) : a+(b-a)=b := by abel
  simp only [paddingCoordinates,Equiv.coe_fn_mk,hcancel] at he
  rw [he,(hs output).tsum_prod]
  simp only [countableMix,tsum_mul_left,mul_assoc]

end
end AFT.FiniteDist
