import AFT.RationalLDLHeight
import AFT.RationalBodyCovariance
import AFT.RationalGaussianChainAccuracy

/-! # The actual body-padding covariance has a rational scalar-step program -/
namespace AFT.RationalNumerics
open GaussianSource BodyPadding Matrix
open scoped BigOperators

/-- Reverse the stored lower LDL coordinates to obtain the literal scalar
conditional center formulas used by the earlier matrix Gaussian proof. -/
def rationalMatrixGaussianChain {count : ℕ} (matrix : Matrix (Fin count) (Fin count) ℚ)
    (center : Fin count → ℚ) : RationalGaussianChain count :=
  let lower := rationalLDLLower matrix
  let diagonal := rationalLDLDiagonal matrix
  upperRationalGaussianChain count (fun i => diagonal.get i.rev) (fun i => center i.rev)
    (fun i j => (lower.get i.rev).get j.rev)

def rationalBodyPaddingChain (count sigma : ℕ) : RationalGaussianChain count :=
  rationalMatrixGaussianChain (rationalBodyPaddingCovariance count ((sigma : ℚ)^2)) (fun _ => 0)

/-- A deterministic program on a fixed finite fair-bit tape. The output is
in the original path-basis coordinate order, not the sampling reversal. -/
def rationalBodyPaddingDraw (count sigma cutoff bits : ℕ)
    (tape : Fin (count*windowTicketBits cutoff bits) → Fin 2) : Vector ℤ count :=
  let reversed := (rationalBodyPaddingChain count sigma).drawBits cutoff bits tape
  Vector.ofFn (fun i => reversed.get i.rev)

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

theorem rationalMatrixGaussianChain_real {count : ℕ} (matrix : Matrix (Fin count) (Fin count) ℚ)
    (hpositive : Matrix.PosDef (fun i j => (matrix i j : ℝ))) (center : Fin count → ℚ) :
    (rationalMatrixGaussianChain matrix center).realChain=
      matrixGaussianChain hpositive (fun i => (center i : ℝ)) := by
  rw [rationalMatrixGaussianChain,upperRationalGaussianChain_real]
  unfold matrixGaussianChain
  congr 1
  · funext i
    rw [rationalLDLDiagonal_cast matrix hpositive]
  · funext i j
    exact rationalLDLLower_cast matrix hpositive _ _

private theorem matrixGaussianChain_eq_of_covariance {count : ℕ}
    {first second : Matrix (Fin count) (Fin count) ℝ}
    (hfirst : first.PosDef) (hsecond : second.PosDef) (heq : first=second) (center : Fin count → ℝ) :
    matrixGaussianChain hfirst center=matrixGaussianChain hsecond center := by
  cases heq
  rfl

theorem rationalBodyPaddingChain_real (count sigma : ℕ) (hsigma : 0<sigma) :
    (rationalBodyPaddingChain count sigma).realChain=
      matrixGaussianChain (bodyPaddingCovariance_posDef count sigma (by exact_mod_cast hsigma.ne')) 0 := by
  have hcast := rationalBodyPaddingCovariance_cast count ((sigma : ℚ)^2) sigma (by push_cast;rfl)
  have hpositive : Matrix.PosDef (fun i j => (rationalBodyPaddingCovariance count ((sigma : ℚ)^2) i j : ℝ)) := by
    rw [hcast]
    exact bodyPaddingCovariance_posDef count sigma (by exact_mod_cast hsigma.ne')
  have hh := rationalMatrixGaussianChain_real (rationalBodyPaddingCovariance count ((sigma : ℚ)^2)) hpositive (fun _ => 0)
  have he := matrixGaussianChain_eq_of_covariance hpositive
    (bodyPaddingCovariance_posDef count sigma (by exact_mod_cast hsigma.ne')) hcast (fun _ => (0 : ℝ))
  calc
    (rationalBodyPaddingChain count sigma).realChain =
        matrixGaussianChain hpositive (fun _ => (0 : ℝ)) := by
      simpa only [rationalBodyPaddingChain,Rat.cast_zero] using hh
    _ = _ := he

theorem upperRationalGaussianChain_widthsLe (count : ℕ) (squaredWidth center : Fin count → ℚ)
    (upperMatrix : Matrix (Fin count) (Fin count) ℚ) (upper : ℝ)
    (hwidth : ∀ i,Real.sqrt (squaredWidth i : ℝ)≤upper) :
    (upperRationalGaussianChain count squaredWidth center upperMatrix).WidthsLe upper := by
  induction count with
  | zero => trivial
  | succ count ih => exact ⟨hwidth 0,ih _ _ _ (fun i => hwidth i.succ)⟩

/-- Actual body covariance bounds discharge the scalar width hypotheses. -/
theorem rationalBodyPaddingChain_bounds (count sigma : ℕ) (hsigma : 1≤sigma) :
    (rationalBodyPaddingChain count sigma).realChain.Wide 1 ∧
      (rationalBodyPaddingChain count sigma).WidthsLe (3*sigma*(count+1)) := by
  have hs0 : 0<sigma := by omega
  have hs : (0 : ℝ)<sigma := by exact_mod_cast hs0
  have hs1 : (1 : ℝ)≤sigma := by exact_mod_cast hsigma
  have hcast := rationalBodyPaddingCovariance_cast count ((sigma : ℚ)^2) sigma (by push_cast;rfl)
  have hpositive : Matrix.PosDef (fun i j => (rationalBodyPaddingCovariance count ((sigma : ℚ)^2) i j : ℝ)) := by
    rw [hcast]
    exact bodyPaddingCovariance_posDef count sigma hs.ne'
  constructor
  · rw [rationalBodyPaddingChain_real count sigma hs0]
    apply matrixGaussianChain_wide _ _ 1 (by norm_num)
    intro vector
    have hh := (bodyPaddingCovariance_bounds count sigma vector).1
    have hnorm := Finset.sum_nonneg (fun i (_ : i∈Finset.univ) => sq_nonneg (vector i))
    nlinarith [sq_nonneg ((sigma : ℝ)-1)]
  · unfold rationalBodyPaddingChain rationalMatrixGaussianChain
    apply upperRationalGaussianChain_widthsLe
    intro i
    rw [rationalLDLDiagonal_cast _ hpositive]
    have hh := (bodyPadding_LDL_width_bounds count sigma hs i.rev).2
    have hscalar : Real.sqrt 8≤3 := Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    have hd : LDL.diagEntries hpositive i.rev=
        LDL.diagEntries (bodyPaddingCovariance_posDef count sigma hs.ne') i.rev := by
      congr 1
    rw [hd]
    exact hh.trans (by gcongr)

/-- All stored rational coefficients of the actual body program have
explicit polynomial numerator and denominator lengths. -/
theorem rationalBodyPaddingChain_heights (count sigma : ℕ) (hsigma : 0<sigma) :
    (∀ row column,HeightBound (((rationalLDLLower (rationalBodyPaddingCovariance count ((sigma : ℚ)^2))).get row).get column)
      (rationalLDLRowHeight count (2*sigma+4*count+6))) ∧
    (∀ row,HeightBound ((rationalLDLDiagonal (rationalBodyPaddingCovariance count ((sigma : ℚ)^2))).get row)
      (rationalLDLDiagonalHeight count (2*sigma+4*count+6))) := by
  have hcast := rationalBodyPaddingCovariance_cast count ((sigma : ℚ)^2) sigma (by push_cast;rfl)
  have hpositive : Matrix.PosDef (fun i j => (rationalBodyPaddingCovariance count ((sigma : ℚ)^2) i j : ℝ)) := by
    rw [hcast]
    exact bodyPaddingCovariance_posDef count sigma (by exact_mod_cast hsigma.ne')
  have hsq : HeightBound ((sigma : ℚ)^2) (2*sigma) := by
    simpa only [Nat.mul_comm] using (HeightBound.nat_coarse sigma).pow 2
  have hh := rationalBodyPaddingCovariance_height count ((sigma : ℚ)^2) (2*sigma) hsq
  exact ⟨rationalLDLLower_height _ hpositive hh,rationalLDLDiagonal_height _ hpositive hh⟩

theorem rationalBodyPaddingDraw_channel {Output : Type*} [Fintype Output]
    (count sigma cutoff bits : ℕ) (channel : (Fin count → ℤ) → FiniteDist Output) :
    (FiniteDist.independent (fun _ : Fin (count*windowTicketBits cutoff bits) => FiniteDist.uniform (Fin 2))).mix
      (fun tape => channel (rationalBodyPaddingDraw count sigma cutoff bits tape).get)=
      (rationalBodyPaddingChain count sigma).finiteChannel cutoff bits
        (fun word => channel (reverseIntegerWord count word)) := by
  have hh := (rationalBodyPaddingChain count sigma).draw_channel cutoff bits
    (fun word => channel (reverseIntegerWord count word))
  rw [←FiniteConditionProgram.groupBits_law,FiniteDist.mix_map] at hh
  have he (tape : Fin (count*windowTicketBits cutoff bits) → Fin 2) :
      (rationalBodyPaddingDraw count sigma cutoff bits tape).get=
        reverseIntegerWord count ((rationalBodyPaddingChain count sigma).drawBits cutoff bits tape).get := by
    funext i
    simp only [rationalBodyPaddingDraw,Vector.get_ofFn,reverseIntegerWord,Equiv.coe_fn_mk]
  simpa only [he,RationalGaussianChain.drawBits] using hh

end
end AFT.RationalNumerics
