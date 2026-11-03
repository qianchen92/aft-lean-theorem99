import AFT.CountableNormalizedTilt
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! # Genuine convolution and normalization of countable probability laws -/
namespace AFT
open scoped BigOperators
noncomputable section
variable {State : Type*} [AddCommGroup State]

def countableConvolution (first second : State → ℝ) (target : State) : ℝ :=
  ∑' source,first source*second (target-source)

private def convolutionCoordinateEquiv : (State × State) ≃ (State × State) where
  toFun point := (point.2,point.1-point.2)
  invFun point := (point.1+point.2,point.1)
  left_inv point := by ext <;> simp
  right_inv point := by ext <;> simp

theorem countableConvolution_nonneg (first second : State → ℝ)
    (hf : ∀ source,0≤first source) (hs : ∀ source,0≤second source) (target : State) :
    0≤countableConvolution first second target :=
  tsum_nonneg (fun source => mul_nonneg (hf source) (hs _))

theorem countableConvolution_summable (first second : State → ℝ)
    (hf : ∀ source,0≤first source) (hs : ∀ source,0≤second source)
    (hf_sum : Summable first) (hs_sum : Summable second) :
    Summable (countableConvolution first second) := by
  have hp := hf_sum.mul_of_nonneg hs_sum hf hs
  have he : Summable (fun point : State × State => first point.2*second (point.1-point.2)) :=
    convolutionCoordinateEquiv.summable_iff.mpr hp
  exact (summable_prod_of_nonneg (fun point => mul_nonneg (hf point.2) (hs _))).mp he |>.2

theorem countableConvolution_sum (first second : State → ℝ)
    (hf : ∀ source,0≤first source) (hs : ∀ source,0≤second source)
    (hf_sum : Summable first) (hs_sum : Summable second) :
    (∑' target,countableConvolution first second target)=(∑' source,first source)*(∑' source,second source) := by
  have hp := hf_sum.mul_of_nonneg hs_sum hf hs
  have he : Summable (fun point : State × State => first point.2*second (point.1-point.2)) :=
    convolutionCoordinateEquiv.summable_iff.mpr hp
  change (∑' target,∑' source,first source*second (target-source))=_
  rw [← he.tsum_prod]
  have hcoord := convolutionCoordinateEquiv.tsum_eq (fun point : State × State => first point.1*second point.2)
  simp only [convolutionCoordinateEquiv,Equiv.coe_fn_mk] at hcoord
  rw [hcoord]
  exact (hf_sum.tsum_mul_tsum hs_sum hp).symm

theorem countableConvolution_div (first second : State → ℝ) (left right : ℝ) (target : State) :
    countableConvolution (fun source => first source/left) (fun source => second source/right) target=
      countableConvolution first second target/(left*right) := by
  simp only [countableConvolution,div_mul_div_comm,tsum_div_const]

end
end AFT
