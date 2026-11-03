import AFT.SafeFiniteNeumann

/-! # Exact canonicality under the finite smoothing and Neumann operators -/

namespace AFT.SafeConvolution

open scoped BigOperators

variable {G : Type*} [Fintype G] [AddCommGroup G]

/-- Both true signed marginals vanish. -/
def PairCanonical (profile : G × G → ℝ) : Prop :=
  (∀ first, ∑ second, profile (first, second) = 0) ∧
  (∀ second, ∑ first, profile (first, second) = 0)

theorem convolution_pairCanonical (kernel profile : G × G → ℝ) (h : PairCanonical profile) :
    PairCanonical (convolution kernel profile) := by
  constructor
  · intro first
    simp only [convolution_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro shift _
    rw [← Finset.mul_sum]
    change kernel shift * (∑ second, profile (first - shift.1, second - shift.2)) = 0
    rw [translated_sum (fun second => profile (first - shift.1, second)), h.1, mul_zero]
  · intro second
    simp only [convolution_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro shift _
    rw [← Finset.mul_sum]
    change kernel shift * (∑ first, profile (first - shift.1, second - shift.2)) = 0
    rw [translated_sum (fun first => profile (first, second - shift.2)), h.2, mul_zero]

omit [AddCommGroup G] in
theorem PairCanonical.sub {first second : G × G → ℝ} (ha : PairCanonical first) (hb : PairCanonical second) :
    PairCanonical (first - second) := by
  constructor
  · intro color; simp only [Pi.sub_apply, Finset.sum_sub_distrib, ha.1, hb.1, sub_self]
  · intro color; simp only [Pi.sub_apply, Finset.sum_sub_distrib, ha.2, hb.2, sub_self]

omit [AddCommGroup G] in
theorem PairCanonical.sum {ι : Type*} (indices : Finset ι) (profiles : ι → G × G → ℝ)
    (h : ∀ index ∈ indices, PairCanonical (profiles index)) :
    PairCanonical (∑ index ∈ indices, profiles index) := by
  constructor
  · intro color
    simp only [Finset.sum_apply]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun index hi => (h index hi).1 color
  · intro color
    simp only [Finset.sum_apply]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun index hi => (h index hi).2 color

omit [AddCommGroup G] in
theorem operator_power_pairCanonical (operator : Module.End ℝ (G × G → ℝ))
    (hop : ∀ profile, PairCanonical profile → PairCanonical (operator profile))
    (order : ℕ) (profile : G × G → ℝ) (h : PairCanonical profile) :
    PairCanonical ((operator ^ order) profile) := by
  induction order with
  | zero => simpa only [pow_zero, Module.End.one_apply] using h
  | succ order ih => simpa only [pow_succ', Module.End.mul_apply] using hop _ ih

/-- Every actual finite correction term is canonical, including the last
root residual. -/
theorem compactRootInput_pairCanonical (root smooth : FiniteDist (G × G)) (depth : ℕ)
    (seed : G × G → ℝ) (hseed : PairCanonical seed) :
    PairCanonical (compactRootInput root smooth depth seed) := by
  have htarget := operator_power_pairCanonical (convolution smooth.weight)
    (convolution_pairCanonical _) (depth + 1) seed hseed
  have hb : -(convolution root.weight - 1) = 1 - convolution root.weight := by abel
  simp only [compactRootInput, finiteCorrection, LinearMap.sum_apply, hb]
  apply PairCanonical.sum
  intro index _
  apply operator_power_pairCanonical _ _ index _ htarget
  intro profile hp
  exact hp.sub (convolution_pairCanonical _ _ hp)

end AFT.SafeConvolution
