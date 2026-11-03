import AFT.FixedPairedKernel
import AFT.ActualPairedFirst

/-! # Exact counts of the actual root-conditioned chart triple -/

namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance fixedChartMarginalFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- The original attached-source average is a linear operation. -/
def publicChartAttachedLinear (cutoffScale : ℝ) (parameter : ℕ)
    (mark : Fin (Parameters.modulus parameter)) (charts : PublicChartFamily cutoffScale parameter mark)
    (first second : Fin (Parameters.modulus parameter)) :
    (Window (legCutoff cutoffScale parameter - 1) → ℝ) →ₗ[ℝ] ℝ where
  toFun attached := publicChartRaw cutoffScale parameter mark charts attached first second
  map_add' first second := by
    simp only [publicChartRaw, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' scalar attached := by
    simp only [publicChartRaw, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro sample _
    apply Finset.sum_congr rfl
    intro offset _
    apply Finset.sum_congr rfl
    intro input _
    ring

theorem publicChartRaw_sum {Index : Type*} [Fintype Index]
    (cutoffScale : ℝ) (parameter : ℕ)
    (mark : Fin (Parameters.modulus parameter)) (charts : PublicChartFamily cutoffScale parameter mark)
    (attached : Index → Window (legCutoff cutoffScale parameter - 1) → ℝ)
    (first second : Fin (Parameters.modulus parameter)) :
    (∑ index, publicChartRaw cutoffScale parameter mark charts (attached index) first second) =
      publicChartRaw cutoffScale parameter mark charts (fun source => ∑ index, attached index source) first second := by
  have hh := map_sum (publicChartAttachedLinear cutoffScale parameter mark charts first second) attached Finset.univ
  have he : (fun source => ∑ index, attached index source) = ∑ index, attached index := by
    funext source
    exact (Finset.sum_apply source Finset.univ attached).symm
  rw [he]
  exact hh.symm

def fixedChartTriple (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (mark : Fin (Parameters.modulus parameter)) (charts : PublicChartFamily cutoffScale parameter mark)
    (root queue : ℤ) (first second attached : Fin (Parameters.modulus parameter)) : ℝ :=
  publicChartRaw cutoffScale parameter mark charts
    (fun source => (actualShiftedBodyLaw cutoffScale parameter beta (root + source + queue)).weight attached) first second

def signedChartTriple (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark)
    (root queue : ℤ) (profile : Fin (Parameters.modulus parameter) → ℝ)
    (first second attached : Fin (Parameters.modulus parameter)) : ℝ :=
  ∑ mark, profile mark * fixedChartTriple cutoffScale parameter beta mark (charts mark) root queue first second attached

theorem fixedChartTriple_endpoint_marginal (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (mark : Fin (Parameters.modulus parameter)) (charts : PublicChartFamily cutoffScale parameter mark)
    (root queue : ℤ) (first second : Fin (Parameters.modulus parameter)) :
    (∑ attached, fixedChartTriple cutoffScale parameter beta mark charts root queue first second attached) =
      publicChartRaw cutoffScale parameter mark charts (fun _ => 1) first second := by
  unfold fixedChartTriple
  rw [publicChartRaw_sum]
  simp only [FiniteDist.sum_one]

theorem fixedChartTriple_total (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (mark : Fin (Parameters.modulus parameter)) (charts : PublicChartFamily cutoffScale parameter mark)
    (root queue : ℤ) :
    (∑ first, ∑ second, ∑ attached, fixedChartTriple cutoffScale parameter beta mark charts root queue first second attached) = 1 :=
  publicChartRaw_triple_mass cutoffScale parameter beta mark charts root queue

theorem signedChartTriple_total (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark)
    (root queue : ℤ) (profile : Fin (Parameters.modulus parameter) → ℝ) :
    (∑ first, ∑ second, ∑ attached, signedChartTriple cutoffScale parameter beta charts root queue profile first second attached) =
      ∑ mark, profile mark := by
  unfold signedChartTriple
  have heq (first second) :
      (∑ attached, ∑ mark, profile mark * fixedChartTriple cutoffScale parameter beta mark (charts mark) root queue first second attached) =
      ∑ mark, profile mark * ∑ attached, fixedChartTriple cutoffScale parameter beta mark (charts mark) root queue first second attached := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  simp only [heq]
  rw [sum_pair_mixture]
  simp only [fixedChartTriple_total, mul_one]

/-- The exact count has two endpoint counts and the Gaussian attached
marginal. The latter is independent of the primary mark. -/
theorem fixedChartTriple_count (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (mark : Fin (Parameters.modulus parameter)) (charts : PublicChartFamily cutoffScale parameter mark)
    (root queue : ℤ) (output : Fin (Parameters.modulus parameter)) :
    (∑ first, ∑ second, ∑ attached,
      fixedChartTriple cutoffScale parameter beta mark charts root queue first second attached *
        ((if first = output then 1 else 0) + (if second = output then 1 else 0) + (if attached = output then 1 else 0))) =
    publicChartEndpointMean cutoffScale parameter mark charts output +
      ∑ source, (windowGaussian (10 * parameter) (legCutoff cutoffScale parameter - 1)).weight source *
        (actualShiftedBodyLaw cutoffScale parameter beta (root + source + queue)).weight output := by
  simp only [mul_add, Finset.sum_add_distrib]
  have hfirst : (∑ first, ∑ second, ∑ attached,
      fixedChartTriple cutoffScale parameter beta mark charts root queue first second attached * (if first = output then 1 else 0)) =
      ∑ second, publicChartRaw cutoffScale parameter mark charts (fun _ => 1) output second := by
    have hm (first second) : (∑ attached, fixedChartTriple cutoffScale parameter beta mark charts root queue first second attached *
        (if first = output then (1 : ℝ) else 0)) =
        publicChartRaw cutoffScale parameter mark charts (fun _ => 1) first second * (if first = output then 1 else 0) := by
      rw [← Finset.sum_mul, fixedChartTriple_endpoint_marginal]
    simp only [hm, ← Finset.sum_mul]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hsecond : (∑ first, ∑ second, ∑ attached,
      fixedChartTriple cutoffScale parameter beta mark charts root queue first second attached * (if second = output then 1 else 0)) =
      ∑ first, publicChartRaw cutoffScale parameter mark charts (fun _ => 1) first output := by
    have hm (first second) : (∑ attached, fixedChartTriple cutoffScale parameter beta mark charts root queue first second attached *
        (if second = output then (1 : ℝ) else 0)) =
        publicChartRaw cutoffScale parameter mark charts (fun _ => 1) first second * (if second = output then 1 else 0) := by
      rw [← Finset.sum_mul, fixedChartTriple_endpoint_marginal]
    simp only [hm]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hattached : (∑ first, ∑ second, ∑ attached,
      fixedChartTriple cutoffScale parameter beta mark charts root queue first second attached * (if attached = output then 1 else 0)) =
      ∑ source, (windowGaussian (10 * parameter) (legCutoff cutoffScale parameter - 1)).weight source *
        (actualShiftedBodyLaw cutoffScale parameter beta (root + source + queue)).weight output := by
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      fixedChartTriple, publicChartRaw_total]
  rw [hfirst, hsecond, hattached]
  rfl

/-- A canonical primary profile contributes exactly its endpoint response;
the same-source attached body cancels before any norm is taken. -/
theorem signedChartTriple_count (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark)
    (root queue : ℤ) (profile : Fin (Parameters.modulus parameter) → ℝ)
    (hcanonical : ∑ mark, profile mark = 0) (output : Fin (Parameters.modulus parameter)) :
    (∑ first, ∑ second, ∑ attached,
      signedChartTriple cutoffScale parameter beta charts root queue profile first second attached *
        ((if first = output then 1 else 0) + (if second = output then 1 else 0) + (if attached = output then 1 else 0))) =
      ∑ mark, profile mark * publicChartEndpointMean cutoffScale parameter mark (charts mark) output := by
  unfold signedChartTriple
  simp only [Finset.sum_mul, mul_assoc]
  have heq (first second) :
      (∑ attached, ∑ mark, profile mark *
        (fixedChartTriple cutoffScale parameter beta mark (charts mark) root queue first second attached *
          ((if first = output then 1 else 0) + (if second = output then 1 else 0) + (if attached = output then 1 else 0)))) =
      ∑ mark, profile mark * ∑ attached,
        fixedChartTriple cutoffScale parameter beta mark (charts mark) root queue first second attached *
          ((if first = output then 1 else 0) + (if second = output then 1 else 0) + (if attached = output then 1 else 0)) := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  simp only [heq]
  rw [sum_pair_mixture]
  simp only [fixedChartTriple_count]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hcanonical, zero_mul, add_zero]

end
end AFT.V7Calibration
