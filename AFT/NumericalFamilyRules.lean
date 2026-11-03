import AFT.NumericalFamily

/-! Exact finite-expression rules for the already specified rational evaluators. -/
namespace AFT.RationalNumerics
open Filter
open scoped BigOperators Topology
noncomputable section
variable {Index Other : ℕ → Type*}

namespace PolynomialFamily

theorem congr {first second : (n : ℕ) → Index n → ℝ} (h : PolynomialFamily first)
    (heq : ∀ᶠ n : ℕ in atTop,∀ point,first n point=second n point) : PolynomialFamily second := by
  obtain ⟨C,d,hC,hh⟩ := h
  refine ⟨C,d,hC,?_⟩
  filter_upwards [hh,heq] with n hn he point
  rw [←he point];exact hn point

theorem constant (value : ℝ) : PolynomialFamily (fun (_n : ℕ) (_point : Index _n) => value) := by
  exact ⟨|value|,0,abs_nonneg _,Filter.Eventually.of_forall fun _ _ => by simp⟩

end PolynomialFamily
namespace UniformRationalApproximation

theorem congr {program other : (n : ℕ) → Index n → ℚ} {value target : (n : ℕ) → Index n → ℝ}
    (h : UniformRationalApproximation program value)
    (hp : ∀ᶠ n : ℕ in atTop,∀ point,program n point=other n point)
    (hv : ∀ᶠ n : ℕ in atTop,∀ point,value n point=target n point) :
    UniformRationalApproximation other target := by
  obtain ⟨hb,error,he,hh⟩ := h
  refine ⟨hb.congr hv,error,he,?_⟩
  filter_upwards [hh,hp,hv] with n hn hp hv point
  rw [←hp point,←hv point];exact hn point

theorem of_exact {program : (n : ℕ) → Index n → ℚ} {value : (n : ℕ) → Index n → ℝ}
    (hvalue : PolynomialFamily value)
    (heq : ∀ᶠ n : ℕ in atTop,∀ point,(program n point : ℝ)=value n point) :
    UniformRationalApproximation program value := by
  refine ⟨hvalue,(fun _ => 0),?_,?_⟩
  · intro degree;filter_upwards [] with n; simp only [abs_zero];positivity
  · filter_upwards [heq] with n hn point;rw [hn point];simp

theorem constant (value : ℚ) :
    UniformRationalApproximation (fun (_n : ℕ) (_point : Index _n) => value)
      (fun (_n : ℕ) (_point : Index _n) => (value : ℝ)) :=
  of_exact (PolynomialFamily.constant _) (Filter.Eventually.of_forall fun _ _ => rfl)

end UniformRationalApproximation
end
end AFT.RationalNumerics
