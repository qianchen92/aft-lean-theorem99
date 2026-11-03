import AFT.MixedKernel
import AFT.SignedChannelFibers

/-! # Actual finite source averaging preserves all prescribed fibers -/

namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
variable {Source State : Type*} [Fintype Source] [Fintype State]

theorem l2Sq_average_le_bound (source : FiniteDist Source) (reference : FiniteDist State)
    (kernel : Source → State → ℝ) (bound : ℝ)
    (hkernel : ∀ point, reference.l2Sq (kernel point) ≤ bound) :
    reference.l2Sq (fun state => ∑ point, source.weight point * kernel point state) ≤ bound := by
  have hh := positiveCombination_l2Sq_le reference source.weight kernel bound source.nonneg hkernel
  simpa only [source.sum_one,one_pow,one_mul] using hh

/-- Source averaging retains the uniform signed sup bound. -/
theorem abs_average_le_bound (source : FiniteDist Source) (kernel : Source → ℝ) (bound : ℝ)
    (hkernel : ∀ point, |kernel point| ≤ bound) :
    |∑ point, source.weight point * kernel point| ≤ bound := by
  calc
    _ ≤ ∑ point, |source.weight point * kernel point| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ point, source.weight point * bound := by
      apply Finset.sum_le_sum
      intro point _
      rw [abs_mul,abs_of_nonneg (source.nonneg point)]
      exact mul_le_mul_of_nonneg_left (hkernel point) (source.nonneg point)
    _ = _ := by rw [← Finset.sum_mul,source.sum_one,one_mul]

end
end AFT.FiniteDist

namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
variable {Source Slot Color : Type*} [Fintype Source] [Fintype Slot] [Fintype Color] [DecidableEq Slot]

theorem fiberSq_average_le_bound (source : FiniteDist Source) (reference : Slot → FiniteDist Color)
    (kernel : Source → (Slot → Color) → ℝ) (fixed : Finset Slot) (values : Slot → Color) (bound : ℝ)
    (hkernel : ∀ point, fiberSq reference (kernel point) fixed values ≤ bound) :
    fiberSq reference (fun word => ∑ point, source.weight point * kernel point word) fixed values ≤ bound :=
  FiniteDist.l2Sq_average_le_bound source (FiniteDist.independent reference)
    (fun point integrated => kernel point (freeze fixed values integrated)) bound hkernel

end
end AFT.MixedKernel
