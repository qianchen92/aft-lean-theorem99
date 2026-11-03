import AFT.BinaryGaussianProgram
import AFT.BinarySeriesPolynomials

/-! Explicit natural-coefficient polynomial bounds for the actual binary
Gaussian evaluator, including its precision and scale control. -/
namespace AFT.BinaryArithmetic.RationalBits
open Polynomial AFT.RationalNumerics

noncomputable def exponentialSeriesHeightPolynomial (height scale bits : Polynomial ℕ) : Polynomial ℕ :=
  (bits+scale+1)*((bits+scale+1)*(height+scale)+(bits+scale+1)^2+1)
noncomputable def exponentialWorkPolynomial (height scale bits : Polynomial ℕ) : Polynomial ℕ :=
  900*(height+2)^2+9*scale+8*(height+2)+2*bits+100+
    2*primitiveWorkPolynomial (height+scale)+seriesWorkPolynomial (height+scale) (bits+scale+1)+
    primitiveWorkPolynomial (exponentialSeriesHeightPolynomial height scale bits)+
    scale*(primitiveWorkPolynomial (exponentialSeriesHeightPolynomial height scale bits*(scale+1))+2)
noncomputable def gaussianRatioWorkPolynomial (height guard scale bits : Polynomial ℕ) : Polynomial ℕ :=
  900*(height+2)^2+6*guard+4*(height+1)+2*bits+12+
    piWorkPolynomial (bits+guard+1)+primitiveWorkPolynomial (piHeightPolynomial (bits+guard+1)+height)+
    exponentialWorkPolynomial (piHeightPolynomial (bits+guard+1)+height) scale (bits+1)
noncomputable def gaussianWorkPolynomial (widthHeight pointHeight guard scale bits : Polynomial ℕ) : Polynomial ℕ :=
  primitiveWorkPolynomial pointHeight+2*primitiveWorkPolynomial (2*pointHeight+widthHeight)+
    gaussianRatioWorkPolynomial (2*pointHeight+widthHeight) guard scale bits+6

@[simp] theorem exponentialSeriesHeightPolynomial_eval (height scale bits : Polynomial ℕ) (n : ℕ) :
    (exponentialSeriesHeightPolynomial height scale bits).eval n=
      exponentialSeriesHeight (height.eval n) (scale.eval n) (bits.eval n) := by
  simp only [exponentialSeriesHeightPolynomial,exponentialSeriesHeight,eval_mul,eval_add,eval_pow,eval_one]
@[simp] theorem exponentialWorkPolynomial_eval (height scale bits : Polynomial ℕ) (n : ℕ) :
    (exponentialWorkPolynomial height scale bits).eval n=
      exponentialWork (height.eval n) (scale.eval n) (bits.eval n) := by
  simp only [exponentialWorkPolynomial,exponentialWork,eval_mul,eval_add,eval_pow,eval_ofNat,eval_one,
    primitiveWorkPolynomial_eval,seriesWorkPolynomial_eval,exponentialSeriesHeightPolynomial_eval]
@[simp] theorem gaussianRatioWorkPolynomial_eval (height guard scale bits : Polynomial ℕ) (n : ℕ) :
    (gaussianRatioWorkPolynomial height guard scale bits).eval n=
      gaussianRatioWork (height.eval n) (guard.eval n) (scale.eval n) (bits.eval n) := by
  simp only [gaussianRatioWorkPolynomial,gaussianRatioWork,eval_mul,eval_add,eval_pow,eval_ofNat,eval_one,
    primitiveWorkPolynomial_eval,piWorkPolynomial_eval,piHeightPolynomial_eval,exponentialWorkPolynomial_eval]
@[simp] theorem gaussianWorkPolynomial_eval (widthHeight pointHeight guard scale bits : Polynomial ℕ) (n : ℕ) :
    (gaussianWorkPolynomial widthHeight pointHeight guard scale bits).eval n=
      gaussianWork (widthHeight.eval n) (pointHeight.eval n) (guard.eval n) (scale.eval n) (bits.eval n) := by
  simp only [gaussianWorkPolynomial,gaussianWork,eval_mul,eval_add,eval_ofNat,
    primitiveWorkPolynomial_eval,gaussianRatioWorkPolynomial_eval]

theorem exponentialWork_mono {h1 h2 s1 s2 b1 b2 : ℕ}
    (hh : h1≤ h2) (hs : s1≤ s2) (hb : b1≤ b2) :
    exponentialWork h1 s1 b1≤ exponentialWork h2 s2 b2 := by
  unfold exponentialWork exponentialSeriesHeight seriesWork seriesTermWork
    seriesStepWork seriesTermBits primitiveWorkBound
  gcongr

theorem gaussianRatioWork_mono {h1 h2 g1 g2 s1 s2 b1 b2 : ℕ}
    (hh : h1≤ h2) (hg : g1≤ g2) (hs : s1≤ s2) (hb : b1≤ b2) :
    gaussianRatioWork h1 g1 s1 b1≤ gaussianRatioWork h2 g2 s2 b2 := by
  have hp : piHeight (b1+g1+1)≤ piHeight (b2+g2+1) := by unfold piHeight;gcongr
  unfold gaussianRatioWork
  apply Nat.add_le_add
  · apply Nat.add_le_add
    · apply Nat.add_le_add
      · gcongr
      · exact piWork_mono (by omega)
    · exact primitiveWorkBound_mono (Nat.add_le_add hp hh)
  · exact exponentialWork_mono (Nat.add_le_add hp hh) hs (by omega)

theorem gaussianWork_mono {w1 w2 p1 p2 g1 g2 s1 s2 b1 b2 : ℕ}
    (hw : w1≤ w2) (hp : p1≤ p2) (hg : g1≤ g2) (hs : s1≤ s2) (hb : b1≤ b2) :
    gaussianWork w1 p1 g1 s1 b1≤ gaussianWork w2 p2 g2 s2 b2 := by
  unfold gaussianWork
  apply Nat.add_le_add_right
  apply Nat.add_le_add
  · exact Nat.add_le_add (primitiveWorkBound_mono hp)
      (Nat.mul_le_mul_left _ (primitiveWorkBound_mono (by omega)))
  · exact gaussianRatioWork_mono (by omega) hg hs hb

end AFT.BinaryArithmetic.RationalBits
