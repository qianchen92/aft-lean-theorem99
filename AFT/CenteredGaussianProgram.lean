import AFT.RationalGaussianProgram
import AFT.GaussianConvolution

/-! # Executable Gaussian weights at arbitrary rational centers

The denominator of the rational center is cleared exactly. The resulting
program calls the proved rational pi/exponential routine; it does not
invoke a real floor, square root, or Gaussian oracle.
-/
namespace AFT.RationalNumerics

/-- Clearing the center denominator retains the squared width exactly. -/
def centeredGaussianSquaredWidth (squaredWidth center : ℚ) : ℚ :=
  squaredWidth*(center.den : ℚ)^2

def centeredGaussianNumerator (center : ℚ) (point : ℤ) : ℤ :=
  point*(center.den : ℤ)-center.num

def centeredGaussianApprox (squaredWidth center : ℚ) (point : ℤ) (bits : ℕ) : ℚ :=
  gaussianApprox (centeredGaussianSquaredWidth squaredWidth center)
    (centeredGaussianNumerator center point) bits

/-- This integer translation is computed from rational numerator and
denominator. Later scalar draws use bounded offsets from this anchor. -/
def centeredGaussianAnchor (center : ℚ) : ℤ := ⌊center⌋

noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem centeredGaussianSquaredWidth_pos (squaredWidth center : ℚ) (hw : 0<squaredWidth) :
    0<centeredGaussianSquaredWidth squaredWidth center := by
  unfold centeredGaussianSquaredWidth
  have hd : (0 : ℚ)<center.den := by exact_mod_cast center.den_pos
  positivity

theorem centeredGaussianRatio (squaredWidth center : ℚ) (point : ℤ) :
    (gaussianRatio (centeredGaussianSquaredWidth squaredWidth center)
      (centeredGaussianNumerator center point) : ℝ)=
      ((point : ℝ)-(center : ℝ))^2/(squaredWidth : ℝ) := by
  have hd : (center.den : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt center.den_pos)
  have hc : (center : ℝ)=(center.num : ℝ)/(center.den : ℝ) := Rat.cast_def center
  unfold gaussianRatio centeredGaussianSquaredWidth centeredGaussianNumerator
  push_cast
  rw [hc]
  field_simp

/-- The error is uniform in the center and integer point. All guard
precision in the pi and exponential programs is computed rationally. -/
theorem centeredGaussianApprox_error (squaredWidth center : ℚ) (point : ℤ) (bits : ℕ)
    (hw : 0<squaredWidth) :
    |(centeredGaussianApprox squaredWidth center point bits : ℝ)-
      Real.exp (-Real.pi*((point : ℝ)-(center : ℝ))^2/(squaredWidth : ℝ))|≤1/(2 : ℝ)^bits := by
  have hh := gaussianApprox_error (centeredGaussianSquaredWidth squaredWidth center)
    (centeredGaussianNumerator center point) bits (centeredGaussianSquaredWidth_pos squaredWidth center hw)
  have he : -Real.pi*(centeredGaussianNumerator center point : ℝ)^2 /
      (centeredGaussianSquaredWidth squaredWidth center : ℝ)=
      -Real.pi*((point : ℝ)-(center : ℝ))^2/(squaredWidth : ℝ) := by
    have hr := centeredGaussianRatio squaredWidth center point
    simp only [gaussianRatio,Rat.cast_div,Rat.cast_pow,Rat.cast_intCast] at hr
    calc
      _ = -Real.pi*((centeredGaussianNumerator center point : ℝ)^2 /
          (centeredGaussianSquaredWidth squaredWidth center : ℝ)) := by ring
      _ = -Real.pi*(((point : ℝ)-(center : ℝ))^2/(squaredWidth : ℝ)) := congrArg (-Real.pi*·) hr
      _ = _ := by ring
  rw [he] at hh
  exact hh

theorem centeredGaussianApprox_positive (squaredWidth center : ℚ) (point : ℤ) (bits : ℕ) :
    0<centeredGaussianApprox squaredWidth center point bits := gaussianApprox_positive _ _ _

theorem centeredGaussianApprox_shifted_error (squaredWidth center : ℚ) (width : ℝ)
    (point : ℤ) (bits : ℕ) (hw : 0<squaredWidth) (hsquare : width^2=(squaredWidth : ℝ)) :
    |(centeredGaussianApprox squaredWidth center point bits : ℝ)-
      GaussianSource.shiftedWeight width center point|≤1/(2 : ℝ)^bits := by
  have hh := centeredGaussianApprox_error squaredWidth center point bits hw
  have he : GaussianSource.shiftedWeight width center point=
      Real.exp (-Real.pi*((point : ℝ)-(center : ℝ))^2/(squaredWidth : ℝ)) := by
    unfold GaussianSource.shiftedWeight
    rw [hsquare]
    congr 1
    ring
  rw [he]
  exact hh

theorem centeredGaussianAnchor_bounds (center : ℚ) :
    (centeredGaussianAnchor center : ℝ)≤(center : ℝ) ∧
      (center : ℝ)<(centeredGaussianAnchor center : ℝ)+1 := by
  constructor
  · exact_mod_cast (Int.floor_le center)
  · exact_mod_cast (Int.lt_floor_add_one center)

end
end AFT.RationalNumerics
