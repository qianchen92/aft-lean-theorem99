import AFT.GaussianLDL
import AFT.TriangularGaussianSampler

/-! # The actual matrix Gaussian is a triangular integer Gaussian chain -/
namespace AFT.GaussianSource
open Matrix
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

def upperGaussianChain : (count : ℕ) → (Fin count → ℝ) → (Fin count → ℝ) →
    Matrix (Fin count) (Fin count) ℝ → GaussianChain count
  | 0,_,_,_ => .nil
  | count+1,width,center,upper => .cons (width 0)
      (fun tail => center 0-∑ j,upper 0 j.succ*((tail j : ℝ)-center j.succ))
      (upperGaussianChain count (fun j => width j.succ) (fun j => center j.succ)
        (fun i j => upper i.succ j.succ))

theorem upperGaussianChain_wide (count : ℕ) (width center : Fin count → ℝ)
    (upper : Matrix (Fin count) (Fin count) ℝ) (base : ℝ) (hwidth : ∀ i,base≤width i) :
    (upperGaussianChain count width center upper).Wide base := by
  induction count with
  | zero => trivial
  | succ count ih => exact ⟨hwidth 0,ih _ _ _ (fun i => hwidth i.succ)⟩

theorem upperGaussianChain_weight (count : ℕ) (width center : Fin count → ℝ)
    (upper : Matrix (Fin count) (Fin count) ℝ)
    (htriangular : ∀ i j,j < i → upper i j=0) (hdiagonal : ∀ i,upper i i=1)
    (word : Fin count → ℤ) :
    (upperGaussianChain count width center upper).weight word=
      Real.exp (-Real.pi*∑ i,(upper.mulVec (fun j => (word j : ℝ)-center j) i)^2/(width i)^2) := by
  induction count with
  | zero => simp [upperGaussianChain,GaussianChain.weight]
  | succ count ih =>
    have hhead : upper.mulVec (fun j => (word j : ℝ)-center j) 0=
        (word 0 : ℝ)-center 0+∑ j : Fin count,upper 0 j.succ*((word j.succ : ℝ)-center j.succ) := by
      simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,hdiagonal 0,one_mul]
    have htail (i : Fin count) : upper.mulVec (fun j => (word j : ℝ)-center j) i.succ=
        Matrix.mulVec (fun i j : Fin count => upper i.succ j.succ)
          (fun j => (Fin.tail word j : ℝ)-center j.succ) i := by
      simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,htriangular i.succ 0 (Fin.succ_pos _),
        zero_mul,zero_add,Fin.tail_def]
    simp only [upperGaussianChain,GaussianChain.weight]
    rw [ih _ _ _ (fun i j hj => htriangular i.succ j.succ (Fin.succ_lt_succ_iff.mpr hj))
      (fun i => hdiagonal i.succ),shiftedWeight,← Real.exp_add,Fin.sum_univ_succ,hhead]
    simp only [htail,Fin.tail_def]
    congr 1
    ring

/-- A genuinely elliptic integer weight, with the actual inverse of its
positive-definite covariance and an arbitrary real center. -/
def matrixGaussianWeight {count : ℕ} (covariance : Matrix (Fin count) (Fin count) ℝ)
    (center : Fin count → ℝ) (word : Fin count → ℤ) : ℝ :=
  Real.exp (-Real.pi*(star (fun i => (word i : ℝ)-center i) ⬝ᵥ
    covariance⁻¹.mulVec (fun i => (word i : ℝ)-center i)))

/-- Reversing the coordinates turns the covariance LDL factor into the
upper triangular chain required by the scalar integer sampler. -/
def matrixGaussianChain {count : ℕ} {covariance : Matrix (Fin count) (Fin count) ℝ}
    (hcovariance : covariance.PosDef) (center : Fin count → ℝ) : GaussianChain count :=
  upperGaussianChain count
    (fun i => Real.sqrt (LDL.diagEntries hcovariance i.rev))
    (fun i => center i.rev)
    (fun i j => LDL.lowerInv hcovariance i.rev j.rev)

/-- Exact equality of the integer weights, including the coordinate
permutation. The sequential approximation is therefore to this matrix law. -/
theorem matrixGaussianChain_weight {count : ℕ} {covariance : Matrix (Fin count) (Fin count) ℝ}
    (hcovariance : covariance.PosDef) (center : Fin count → ℝ) (word : Fin count → ℤ) :
    (matrixGaussianChain hcovariance center).weight (fun i => word i.rev)=
      matrixGaussianWeight covariance center word := by
  rw [matrixGaussianChain,upperGaussianChain_weight]
  · unfold matrixGaussianWeight
    rw [gaussianLDL_quadratic]
    apply congrArg Real.exp
    apply congrArg (fun total : ℝ => -Real.pi*total)
    have hd (i : Fin count) : 0≤LDL.diagEntries hcovariance i := by
      have hh := hcovariance.posSemidef.dotProduct_mulVec_nonneg (LDL.lowerInv hcovariance i)
      simpa only [LDL.diagEntries,EuclideanSpace.inner_toLp_toLp,star_trivial,dotProduct_comm] using hh
    simp only [Real.sq_sqrt (hd _)]
    have hm (i : Fin count) :
        Matrix.mulVec (fun i j : Fin count => LDL.lowerInv hcovariance i.rev j.rev)
          (fun j => (word j.rev : ℝ)-center j.rev) i=
          (LDL.lowerInv hcovariance).mulVec (fun j => (word j : ℝ)-center j) i.rev := by
      simp only [Matrix.mulVec,dotProduct]
      exact Equiv.sum_comp Fin.revPerm (fun j => LDL.lowerInv hcovariance i.rev j*((word j : ℝ)-center j))
    simp only [hm]
    exact Equiv.sum_comp Fin.revPerm (fun i : Fin count =>
      ((LDL.lowerInv hcovariance).mulVec (fun j => (word j : ℝ)-center j) i)^2/LDL.diagEntries hcovariance i)
  · intro i j hj
    apply LDL.lowerInv_triangular
    exact Fin.rev_lt_rev.mpr hj
  · intro i
    exact gaussianLDL_unit_diagonal hcovariance i.rev


theorem upperGaussianChain_volume (count : ℕ) (width center : Fin count → ℝ)
    (upper : Matrix (Fin count) (Fin count) ℝ) :
    (upperGaussianChain count width center upper).volume=∏ i,width i := by
  induction count with
  | zero => simp [upperGaussianChain,GaussianChain.volume]
  | succ count ih => simp only [upperGaussianChain,GaussianChain.volume,ih,Fin.prod_univ_succ]

def matrixGaussianVolume {count : ℕ} {covariance : Matrix (Fin count) (Fin count) ℝ}
    (hcovariance : covariance.PosDef) : ℝ := ∏ i,Real.sqrt (LDL.diagEntries hcovariance i)

theorem matrixGaussianChain_volume {count : ℕ} {covariance : Matrix (Fin count) (Fin count) ℝ}
    (hcovariance : covariance.PosDef) (center : Fin count → ℝ) :
    (matrixGaussianChain hcovariance center).volume=matrixGaussianVolume hcovariance := by
  rw [matrixGaussianChain,upperGaussianChain_volume]
  exact Equiv.prod_comp Fin.revPerm (fun i : Fin count => Real.sqrt (LDL.diagEntries hcovariance i))

def reverseIntegerWord (count : ℕ) : (Fin count → ℤ) ≃ (Fin count → ℤ) where
  toFun word i := word i.rev
  invFun word i := word i.rev
  left_inv word := by funext i; simp
  right_inv word := by funext i; simp

theorem matrixGaussianChain_sum {count : ℕ} {covariance : Matrix (Fin count) (Fin count) ℝ}
    (hcovariance : covariance.PosDef) (center : Fin count → ℝ) :
    (∑' word,(matrixGaussianChain hcovariance center).weight word)=
      ∑' word,matrixGaussianWeight covariance center word := by
  rw [← (reverseIntegerWord count).tsum_eq]
  exact tsum_congr (fun word => matrixGaussianChain_weight hcovariance center word)

theorem matrixGaussianChain_wide {count : ℕ} {covariance : Matrix (Fin count) (Fin count) ℝ}
    (hcovariance : covariance.PosDef) (center : Fin count → ℝ) (base : ℝ) (hbase : 0≤base)
    (hbound : ∀ vector : Fin count → ℝ,base^2*(∑ i,vector i^2)≤
      star vector ⬝ᵥ covariance.mulVec vector) :
    (matrixGaussianChain hcovariance center).Wide base := by
  apply upperGaussianChain_wide
  intro i
  have hh := gaussianLDL_diagonal_lower hcovariance (base^2) (sq_nonneg _) hbound i.rev
  exact (Real.le_sqrt hbase ((sq_nonneg _).trans hh)).mpr hh

/-- The complete countable matrix Gaussian normalizer has the same
uniform error for every real center. It follows from actual triangular
elimination and scalar Poisson bounds, with no multivariate premise. -/
theorem matrixGaussian_relative_normalizer_error {count : ℕ}
    {covariance : Matrix (Fin count) (Fin count) ℝ}
    (hcovariance : covariance.PosDef) (center : Fin count → ℝ)
    (base error : ℝ) (hbase : 0<base) (herror : 0≤error) (hsmall : error≤1)
    (htheta : thetaError base≤error)
    (hbound : ∀ vector : Fin count → ℝ,base^2*(∑ i,vector i^2)≤
      star vector ⬝ᵥ covariance.mulVec vector) :
    Summable (matrixGaussianWeight covariance center) ∧
      |(∑' word,matrixGaussianWeight covariance center word)/matrixGaussianVolume hcovariance-1|≤
        (1+error)^count-1 := by
  have hw := matrixGaussianChain_wide hcovariance center base hbase.le hbound
  obtain ⟨hs,_,_⟩ := (matrixGaussianChain hcovariance center).summable_and_bounds base error hbase herror hsmall htheta hw
  constructor
  · have hh := (reverseIntegerWord count).summable_iff.mpr hs
    exact hh.congr (fun word => matrixGaussianChain_weight hcovariance center word)
  · have hh := (matrixGaussianChain hcovariance center).relative_normalizer_error base error hbase herror hsmall htheta hw
    rwa [matrixGaussianChain_sum,matrixGaussianChain_volume] at hh

end
end AFT.GaussianSource
