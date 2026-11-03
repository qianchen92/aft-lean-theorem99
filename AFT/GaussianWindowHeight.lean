import AFT.RationalSeriesHeight

/-! # Uniform polynomial heights for finite rational Gaussian windows -/
namespace AFT.RationalNumerics
open GaussianSource FiniteConvolutionProgram
open scoped BigOperators
noncomputable section

/-- A bound on the actual rational Gaussian ratio controls every series
length, and therefore the exact numerator and denominator heights. -/
theorem gaussianApprox_height_of_budget (squaredWidth : ℚ) (point : ℤ)
    (precision budget : ℕ) (hb : 2≤budget) (hprecision : precision≤4*budget)
    (hratio0 : 0≤gaussianRatio squaredWidth point) (hratio : gaussianRatio squaredWidth point≤budget)
    (hratioHeight : HeightBound (gaussianRatio squaredWidth point) (3*budget)) :
    HeightBound (gaussianApprox squaredWidth point precision) (100000000*budget^5) := by
  have hguard : gaussianGuard squaredWidth point≤budget := Nat.ceil_le.mpr hratio
  have hpi : gaussianPiPrecision squaredWidth point precision+3≤7*budget := by
    unfold gaussianPiPrecision
    omega
  have harg : max (piApprox (gaussianPiPrecision squaredWidth point precision)*gaussianRatio squaredWidth point) 0≤(5*budget : ℕ) := by
    apply max_le
    · have hh := mul_le_mul_of_nonneg_right (piApprox_le_five (gaussianPiPrecision squaredWidth point precision)) hratio0
      have hh' := mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℚ)≤5)
      push_cast
      linarith
    · positivity
  have hceil : ⌈max (piApprox (gaussianPiPrecision squaredWidth point precision)*gaussianRatio squaredWidth point) 0⌉₊≤5*budget := Nat.ceil_le.mpr harg
  have hscale : gaussianExpScale squaredWidth point precision≤11*budget := by
    unfold gaussianExpScale expScale
    omega
  have hterms : gaussianTaylorTerms squaredWidth point precision≤16*budget := by
    unfold gaussianTaylorTerms
    omega
  have hpiHeight : piHeight (gaussianPiPrecision squaredWidth point precision)≤650*budget^2 := by
    unfold piHeight
    calc
      _ ≤ 2*((7*budget)*(6*(7*budget)+4))+3 := by gcongr
      _ ≤ _ := by nlinarith
  have hinside : piHeight (gaussianPiPrecision squaredWidth point precision)+3*budget+
      gaussianExpScale squaredWidth point precision≤657*budget^2 := by nlinarith
  have hb23 : budget^2≤budget^3 := Nat.pow_le_pow_right (by omega : 1≤budget) (by decide)
  have hb3 : 1≤budget^3 := Nat.one_le_pow _ _ (by omega)
  have hbig : (16*budget)*(657*budget^2)+(16*budget)^2+1≤11000*budget^3 := by nlinarith
  apply (gaussianApprox_height squaredWidth point precision (3*budget) hratioHeight).mono
  calc
    _ ≤ (16*budget)*((16*budget)*(657*budget^2)+(16*budget)^2+1)*(11*budget) := by gcongr
    _ ≤ (16*budget)*(11000*budget^3)*(11*budget) := by gcongr
    _ ≤ _ := by nlinarith

theorem windowApproxWeight_height_of_budget (squaredWidth : ℚ) (cutoff bits budget : ℕ)
    (hb : 2≤budget) (hc : cutoff≤budget) (hbits : bits≤budget)
    (hratio0 : ∀point : Window cutoff,0≤gaussianRatio squaredWidth point)
    (hratio : ∀point : Window cutoff,gaussianRatio squaredWidth point≤budget)
    (hratioHeight : ∀point : Window cutoff,HeightBound (gaussianRatio squaredWidth point) (3*budget))
    (point : Window cutoff) :
    HeightBound (windowApproxWeight squaredWidth cutoff bits point) (500000000*budget^6) := by
  have hprecision : windowApproxPrecision cutoff bits≤4*budget := by unfold windowApproxPrecision;omega
  have hraw (point : Window cutoff) : HeightBound (windowApproxRaw squaredWidth cutoff bits point) (100000000*budget^5) :=
    gaussianApprox_height_of_budget squaredWidth point _ budget hb hprecision (hratio0 point) (hratio point) (hratioHeight point)
  have hcard : Fintype.card (Window cutoff)≤3*budget := by
    rw [←Fintype.card_congr (windowIndexEquiv cutoff),Fintype.card_fin]
    omega
  have hnormal := HeightBound.sum Finset.univ _ (100000000*budget^5) (fun point _ => hraw point)
  have hnormal' : HeightBound (windowApproxNormalizer squaredWidth cutoff bits) (400000000*budget^6) := by
    apply hnormal.mono
    simp only [Finset.card_univ]
    calc
      _ ≤ (3*budget)*(100000000*budget^5+1) := by gcongr
      _ ≤ _ := by
        have hp : budget≤budget^6 := by simpa using Nat.pow_le_pow_right (by omega : 1≤budget) (show 1≤6 by decide)
        nlinarith
  apply ((hraw point).div hnormal').mono
  have hp : budget^5≤budget^6 := Nat.pow_le_pow_right (by omega : 1≤budget) (by decide)
  omega

end
end AFT.RationalNumerics
