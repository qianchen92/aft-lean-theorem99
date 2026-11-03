import AFT.FockGaussian
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! # Signed finite sums in Gaussian L2, with no number-of-terms loss -/
namespace AFT.GaussianSignedSum
open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

variable {Space Index : Type*} [MeasurableSpace Space]

/-- The real L2 seminorm has exactly the complex energy normalization used
by the Fock identities. -/
theorem lpNorm_two_sq (measure : Measure Space) (function : Space → ℂ)
    (hmeasurable : AEStronglyMeasurable function measure) :
    lpNorm function 2 measure^2=∫ point,Complex.normSq (function point) ∂measure := by
  have heq : lpNorm function 2 measure=
      Real.sqrt (∫ point,Complex.normSq (function point) ∂measure) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hmeasurable]
    simp only [ENNReal.toReal_ofNat,Real.rpow_two,Complex.normSq_eq_norm_sq]
    rw [Real.sqrt_eq_rpow]
    norm_num
  rw [heq,Real.sq_sqrt (integral_nonneg (fun _ => Complex.normSq_nonneg _))]

/-- Finite signed combinations of arbitrary complex L2 functions. The
budget is the coefficient-weighted sum of norms, without a cardinality
factor or a separability assumption on the functions. -/
theorem finite_sum_energy_le (measure : Measure Space) (indices : Finset Index)
    (function : Index → Space → ℂ) (coefficient bound : Index → ℝ)
    (hmem : ∀ index∈indices,MemLp (function index) 2 measure)
    (hbound : ∀ index∈indices,0≤bound index)
    (henergy : ∀ index∈indices,
      (∫ point,Complex.normSq (function index point) ∂measure)≤bound index^2) :
    (∫ point,Complex.normSq (∑ index∈indices,(coefficient index : ℂ)*function index point) ∂measure)≤
      (∑ index∈indices,|coefficient index| * bound index)^2 := by
  let scaled : Index → Space → ℂ := fun index point => (coefficient index : ℂ)*function index point
  have hscaled (index) (hi : index∈indices) : MemLp (scaled index) 2 measure :=
    (hmem index hi).const_mul _
  have hsum := memLp_finset_sum indices hscaled
  have hnorm (index) (hi : index∈indices) : lpNorm (function index) 2 measure≤bound index := by
    have he := lpNorm_two_sq measure (function index) (hmem index hi).aestronglyMeasurable
    have hn := lpNorm_nonneg (f:=function index) (p:=2) (μ:=measure)
    nlinarith [henergy index hi,hbound index hi]
  have htriangle : lpNorm (fun point =>∑ index∈indices,scaled index point) 2 measure≤
      ∑ index∈indices,|coefficient index| * bound index := by
    have ht := lpNorm_sum_le hscaled (by norm_num : (1 : ℝ≥0∞)≤2)
    have heq : (∑ index∈indices,scaled index)=(fun point => ∑ index∈indices,scaled index point) := by
      funext point
      simp only [Finset.sum_apply]
    rw [heq] at ht
    apply ht.trans
    apply Finset.sum_le_sum
    intro index hi
    change lpNorm ((coefficient index : ℂ) • function index) 2 measure≤_
    rw [lpNorm_const_smul]
    change ‖(coefficient index : ℂ)‖ * lpNorm (function index) 2 measure≤_
    rw [Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hnorm index hi) (abs_nonneg _)
  rw [← lpNorm_two_sq measure _ hsum.aestronglyMeasurable]
  exact pow_le_pow_left₀ lpNorm_nonneg htriangle 2

/-- The same estimate at the literal circular complex Gaussian field. -/
theorem field_sum_energy_le {Coordinate : Type*} [Fintype Coordinate]
    (indices : Finset Index) (function : Index → (Coordinate → ℂ) → ℂ)
    (coefficient bound : Index → ℝ)
    (hmem : ∀ index∈indices,MemLp (function index) 2 (FockGaussian.field (Coordinate:=Coordinate)))
    (hbound : ∀ index∈indices,0≤bound index)
    (henergy : ∀ index∈indices,
      (∫ value,Complex.normSq (function index value) ∂FockGaussian.field)≤bound index^2) :
    (∫ value,Complex.normSq (∑ index∈indices,(coefficient index : ℂ)*function index value)
      ∂FockGaussian.field)≤(∑ index∈indices,|coefficient index| * bound index)^2 :=
  finite_sum_energy_le _ indices function coefficient bound hmem hbound henergy

end
end AFT.GaussianSignedSum
