import AFT.RationalGaussianChainHeight
import AFT.GaussianWindowHeight

/-! # Polynomial bit and loop bounds at the realized rational centers -/
namespace AFT.RationalNumerics
open GaussianSource FiniteConvolutionProgram
open scoped BigOperators

/-- A single polynomial budget controls precision, the translated window,
the actual rational ratio, and its numerator and denominator lengths. -/
def centeredScalarBudget (widthBits centerBits cutoff bits : ℕ) : ℕ :=
  widthBits+4*centerBits+4*cutoff+bits+(cutoff+1)^2+20

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem centeredGaussianRatio_rat (squaredWidth center : ℚ) (point : ℤ) :
    gaussianRatio (centeredGaussianSquaredWidth squaredWidth center) (centeredGaussianNumerator center point)=
      ((point : ℚ)-center)^2/squaredWidth := by
  exact_mod_cast centeredGaussianRatio squaredWidth center point

theorem centeredWindowRatio_bounds (squaredWidth center : ℚ) (cutoff : ℕ)
    (hwidth : 1≤squaredWidth) (point : Window cutoff) :
    0≤gaussianRatio (centeredGaussianSquaredWidth squaredWidth center)
      (centeredGaussianNumerator center (centeredGaussianAnchor center+point)) ∧
    gaussianRatio (centeredGaussianSquaredWidth squaredWidth center)
      (centeredGaussianNumerator center (centeredGaussianAnchor center+point))≤(cutoff+1 : ℚ)^2 := by
  rw [centeredGaussianRatio_rat]
  have hfloor := Int.floor_le center
  have hfloor' := Int.lt_floor_add_one center
  have hp := Finset.mem_Icc.mp point.property
  have hlo : -(cutoff : ℚ)≤(point : ℤ) := by exact_mod_cast hp.1
  have hhi : ((point : ℤ) : ℚ)≤cutoff := by exact_mod_cast hp.2
  have hdiff : |((centeredGaussianAnchor center+(point : ℤ) : ℤ) : ℚ)-center|≤(cutoff+1 : ℚ) := by
    rw [abs_le]
    simp only [centeredGaussianAnchor,Int.cast_add]
    change -(↑cutoff+1)≤(⌊center⌋ : ℚ)+(point : ℤ)-center ∧
      (⌊center⌋ : ℚ)+(point : ℤ)-center≤↑cutoff+1
    constructor <;> linarith
  refine ⟨by positivity,?_⟩
  apply (div_le_self (sq_nonneg _) hwidth).trans
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hdiff

theorem centeredWindowPoint_height (center : ℚ) (centerBits cutoff : ℕ)
    (hcenter : HeightBound center centerBits) (point : Window cutoff) :
    HeightBound ((centeredGaussianAnchor center+(point : ℤ) : ℤ) : ℚ) (centerBits+cutoff+2) := by
  have hp := Finset.mem_Icc.mp point.property
  have hoff : |((point : ℤ) : ℚ)|≤cutoff := by rw [abs_le];constructor <;> exact_mod_cast (by omega : _)
  have ha : |((centeredGaussianAnchor center+(point : ℤ) : ℤ) : ℚ)|≤(2 : ℚ)^centerBits+cutoff+1 := by
    have hh := abs_add_le (centeredGaussianAnchor center : ℚ) ((point : ℤ) : ℚ)
    push_cast
    linarith [centeredGaussianAnchor_abs center,hcenter.abs_le]
  have hn : (cutoff+1 : ℚ)≤(2 : ℚ)^(cutoff+1) := by exact_mod_cast (Nat.lt_two_pow_self (n:=cutoff+1)).le
  have hc : (1 : ℚ)≤(2 : ℚ)^centerBits := one_le_pow₀ (by norm_num)
  have hw : (1 : ℚ)≤(2 : ℚ)^(cutoff+1) := one_le_pow₀ (by norm_num)
  have hh : (2 : ℚ)^centerBits+cutoff+1≤(2 : ℚ)^(centerBits+cutoff+2) := by
    rw [show centerBits+cutoff+2=centerBits+(cutoff+1)+1 by omega,pow_add,pow_add,pow_one]
    nlinarith
  apply HeightBound.of_int
  have hnat : ((centeredGaussianAnchor center+(point : ℤ)).natAbs : ℚ)≤(2 : ℚ)^(centerBits+cutoff+2) := by
    simpa using ha.trans hh
  exact_mod_cast hnat

theorem centeredWindowRatio_height (squaredWidth center : ℚ) (widthBits centerBits cutoff : ℕ)
    (hw : HeightBound squaredWidth widthBits) (hc : HeightBound center centerBits) (point : Window cutoff) :
    HeightBound (gaussianRatio (centeredGaussianSquaredWidth squaredWidth center)
      (centeredGaussianNumerator center (centeredGaussianAnchor center+point)))
      (widthBits+4*centerBits+2*cutoff+6) := by
  rw [centeredGaussianRatio_rat]
  have hp := centeredWindowPoint_height center centerBits cutoff hc point
  have hd := hp.add hc.neg
  have hh := (hd.pow 2).div hw
  convert hh using 1 <;> ring

/-- These are the literal pi terms, Taylor terms, and powering exponent
used when the scalar draw visits any point in its translated window. -/
theorem centeredWindow_resources (squaredWidth center : ℚ) (widthBits centerBits cutoff bits : ℕ)
    (hw : 1≤squaredWidth) (point : Window cutoff) :
    let budget := centeredScalarBudget widthBits centerBits cutoff bits
    gaussianGuard (centeredGaussianSquaredWidth squaredWidth center)
      (centeredGaussianNumerator center (centeredGaussianAnchor center+point))≤budget ∧
    gaussianPiPrecision (centeredGaussianSquaredWidth squaredWidth center)
      (centeredGaussianNumerator center (centeredGaussianAnchor center+point)) (centeredWindowPrecision cutoff bits)+3≤7*budget ∧
    gaussianExpScale (centeredGaussianSquaredWidth squaredWidth center)
      (centeredGaussianNumerator center (centeredGaussianAnchor center+point)) (centeredWindowPrecision cutoff bits)≤11*budget ∧
    gaussianTaylorTerms (centeredGaussianSquaredWidth squaredWidth center)
      (centeredGaussianNumerator center (centeredGaussianAnchor center+point)) (centeredWindowPrecision cutoff bits)≤16*budget := by
  dsimp only
  let budget := centeredScalarBudget widthBits centerBits cutoff bits
  have hb : 2≤budget := by dsimp [budget,centeredScalarBudget];omega
  have hp : centeredWindowPrecision cutoff bits≤4*budget := by dsimp [budget,centeredScalarBudget,centeredWindowPrecision];omega
  have hr := centeredWindowRatio_bounds squaredWidth center cutoff hw point
  have hrb : gaussianRatio (centeredGaussianSquaredWidth squaredWidth center)
      (centeredGaussianNumerator center (centeredGaussianAnchor center+point))≤(budget : ℚ) :=
    hr.2.trans (by dsimp [budget,centeredScalarBudget];push_cast;nlinarith)
  have hg := Nat.ceil_le.mpr hrb
  have hpi : gaussianPiPrecision (centeredGaussianSquaredWidth squaredWidth center)
      (centeredGaussianNumerator center (centeredGaussianAnchor center+point)) (centeredWindowPrecision cutoff bits)+3≤7*budget := by
    unfold gaussianPiPrecision
    change gaussianGuard _ _≤budget at hg
    omega
  have harg : max (piApprox (gaussianPiPrecision (centeredGaussianSquaredWidth squaredWidth center)
      (centeredGaussianNumerator center (centeredGaussianAnchor center+point)) (centeredWindowPrecision cutoff bits))*
      gaussianRatio (centeredGaussianSquaredWidth squaredWidth center)
      (centeredGaussianNumerator center (centeredGaussianAnchor center+point))) 0≤(5*budget : ℕ) := by
    apply max_le
    · have hh := mul_le_mul_of_nonneg_right (piApprox_le_five (gaussianPiPrecision (centeredGaussianSquaredWidth squaredWidth center)
        (centeredGaussianNumerator center (centeredGaussianAnchor center+point)) (centeredWindowPrecision cutoff bits))) hr.1
      have hh' := mul_le_mul_of_nonneg_left hrb (by norm_num : (0 : ℚ)≤5)
      push_cast
      linarith
    · positivity
  have hs : gaussianExpScale (centeredGaussianSquaredWidth squaredWidth center)
      (centeredGaussianNumerator center (centeredGaussianAnchor center+point)) (centeredWindowPrecision cutoff bits)≤11*budget := by
    have hh := Nat.ceil_le.mpr harg
    unfold gaussianExpScale expScale
    omega
  refine ⟨hg,hpi,hs,?_⟩
  unfold gaussianTaylorTerms
  omega

private theorem normalization_budget (budget : ℕ) (hb : 2≤budget) :
    (3*budget)*(100000000*budget^5+1)≤400000000*budget^6 := by
  have hp : budget≤budget^6 := by simpa using Nat.pow_le_pow_right (by omega : 1≤budget) (show 1≤6 by decide)
  nlinarith

theorem centeredWindowWeight_height (squaredWidth center : ℚ) (widthBits centerBits cutoff bits : ℕ)
    (hwidth : 1≤squaredWidth) (hw : HeightBound squaredWidth widthBits)
    (hc : HeightBound center centerBits) (point : Window cutoff) :
    HeightBound (centeredWindowWeight squaredWidth center cutoff bits point)
      (500000000*(centeredScalarBudget widthBits centerBits cutoff bits)^6) := by
  let budget := centeredScalarBudget widthBits centerBits cutoff bits
  have hb : 2≤budget := by dsimp [budget,centeredScalarBudget];omega
  have hp : centeredWindowPrecision cutoff bits≤4*budget := by dsimp [budget,centeredScalarBudget,centeredWindowPrecision];omega
  have hraw (point : Window cutoff) : HeightBound (centeredWindowRaw squaredWidth center cutoff bits point)
      (100000000*budget^5) := by
    have hr := centeredWindowRatio_bounds squaredWidth center cutoff hwidth point
    apply gaussianApprox_height_of_budget _ _ _ budget hb hp hr.1
    · exact hr.2.trans (by dsimp [budget,centeredScalarBudget];push_cast;nlinarith)
    · exact (centeredWindowRatio_height squaredWidth center widthBits centerBits cutoff hw hc point).mono
        (by dsimp [budget,centeredScalarBudget];omega)
  have hcard : Fintype.card (Window cutoff)≤3*budget := by
    rw [←Fintype.card_congr (windowIndexEquiv cutoff),Fintype.card_fin]
    dsimp [budget,centeredScalarBudget]
    omega
  have hnormal := HeightBound.sum Finset.univ _ (100000000*budget^5) (fun point _ => hraw point)
  have hnormal' : HeightBound (centeredWindowNormalizer squaredWidth center cutoff bits) (400000000*budget^6) := by
    apply hnormal.mono
    simp only [Finset.card_univ]
    calc
      _ ≤ (3*budget)*(100000000*budget^5+1) := by gcongr
      _ ≤ _ := normalization_budget budget hb
  change HeightBound _ (500000000*budget^6)
  apply ((hraw point).div hnormal').mono
  have hp : budget^5≤budget^6 := Nat.pow_le_pow_right (by omega : 1≤budget) (by decide)
  omega

end
end AFT.RationalNumerics
