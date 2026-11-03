import AFT.NumericalProbabilityKernel

/-! Uniform error bookkeeping for explicit rational finite expressions.

The relation below does not select or compute any approximation. Its first
argument is the already specified rational program. It records uniform
negligible error and polynomial magnitude of its exact real interpretation.
-/
namespace AFT.RationalNumerics
open Filter
open scoped BigOperators Topology

noncomputable section

variable {Index Other : ℕ → Type*}

def PolynomialFamily (value : (n : ℕ) → Index n → ℝ) : Prop :=
  ∃ constant : ℝ,∃ degree : ℕ,0 ≤ constant ∧
    ∀ᶠ n : ℕ in atTop,∀ index,|value n index| ≤ constant*(n : ℝ)^degree

def UniformRationalApproximation (program : (n : ℕ) → Index n → ℚ)
    (value : (n : ℕ) → Index n → ℝ) : Prop :=
  PolynomialFamily value ∧ ∃ error : ℕ → ℝ,Negligible error ∧
    ∀ᶠ n : ℕ in atTop,∀ index,|(program n index : ℝ)-value n index| ≤ |error n|

theorem negligible_abs {error : ℕ → ℝ} (h : Negligible error) : Negligible (fun n => |error n|) := by
  intro degree
  simpa only [abs_abs] using h degree

namespace PolynomialFamily

theorem reindex {value : (n : ℕ) → Index n → ℝ} (h : PolynomialFamily value)
    (index : (n : ℕ) → Other n → Index n) : PolynomialFamily (fun n point => value n (index n point)) := by
  obtain ⟨constant,degree,hc,hh⟩ := h
  exact ⟨constant,degree,hc,hh.mono fun n hn point => hn (index n point)⟩

theorem neg {value : (n : ℕ) → Index n → ℝ} (h : PolynomialFamily value) :
    PolynomialFamily (fun n point => -value n point) := by
  obtain ⟨constant,degree,hc,hh⟩ := h
  refine ⟨constant,degree,hc,hh.mono ?_⟩
  intro n hn point
  simpa only [abs_neg] using hn point

theorem add {first second : (n : ℕ) → Index n → ℝ} (hf : PolynomialFamily first) (hs : PolynomialFamily second) :
    PolynomialFamily (fun n point => first n point+second n point) := by
  obtain ⟨C,a,hC,hf⟩ := hf
  obtain ⟨D,b,hD,hs⟩ := hs
  refine ⟨C+D,a+b,add_nonneg hC hD,?_⟩
  filter_upwards [hf,hs,eventually_ge_atTop 1] with n hf hs hn point
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  apply (abs_add_le _ _).trans ((add_le_add (hf point) (hs point)).trans ?_)
  have ha := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn1 (Nat.le_add_right a b)) hC
  have hb := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn1 (Nat.le_add_left b a)) hD
  linarith

theorem sub {first second : (n : ℕ) → Index n → ℝ} (hf : PolynomialFamily first) (hs : PolynomialFamily second) :
    PolynomialFamily (fun n point => first n point-second n point) := by
  simpa only [sub_eq_add_neg] using hf.add hs.neg

theorem mul {first second : (n : ℕ) → Index n → ℝ} (hf : PolynomialFamily first) (hs : PolynomialFamily second) :
    PolynomialFamily (fun n point => first n point*second n point) := by
  obtain ⟨C,a,hC,hf⟩ := hf
  obtain ⟨D,b,hD,hs⟩ := hs
  refine ⟨C*D,a+b,mul_nonneg hC hD,?_⟩
  filter_upwards [hf,hs] with n hf hs point
  rw [abs_mul]
  exact (mul_le_mul (hf point) (hs point) (abs_nonneg _) (mul_nonneg hC (by positivity))).trans_eq (by rw [pow_add];ring)

theorem sum {Source : ℕ → Type*} [∀ n,Fintype (Source n)]
    {value : (n : ℕ) → Source n × Index n → ℝ} (h : PolynomialFamily value)
    (cardinalConstant : ℝ) (cardinalDegree : ℕ) (hc : 0 ≤ cardinalConstant)
    (hcard : ∀ᶠ n : ℕ in atTop,(Fintype.card (Source n) : ℝ) ≤ cardinalConstant*(n : ℝ)^cardinalDegree) :
    PolynomialFamily (fun n point => ∑ source,value n (source,point)) := by
  obtain ⟨C,d,hC,hh⟩ := h
  refine ⟨cardinalConstant*C,cardinalDegree+d,mul_nonneg hc hC,?_⟩
  filter_upwards [hh,hcard] with n hh hcard point
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _source : Source n,C*(n : ℝ)^d := Finset.sum_le_sum fun source _ => hh (source,point)
    _ = (Fintype.card (Source n) : ℝ)*(C*(n : ℝ)^d) := by simp
    _ ≤ (cardinalConstant*(n : ℝ)^cardinalDegree)*(C*(n : ℝ)^d) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by rw [pow_add];ring

end PolynomialFamily

namespace UniformRationalApproximation

theorem of_bound {program : (n : ℕ) → Index n → ℚ} {value : (n : ℕ) → Index n → ℝ}
    (hvalue : PolynomialFamily value) (error : ℕ → ℝ) (he : Negligible error)
    (herror : ∀ᶠ n : ℕ in atTop,∀ point,|(program n point : ℝ)-value n point| ≤ error n) :
    UniformRationalApproximation program value :=
  ⟨hvalue,error,he,herror.mono fun _n hn point => (hn point).trans (le_abs_self _)⟩

theorem reindex {program : (n : ℕ) → Index n → ℚ} {value : (n : ℕ) → Index n → ℝ}
    (h : UniformRationalApproximation program value) (index : (n : ℕ) → Other n → Index n) :
    UniformRationalApproximation (fun n point => program n (index n point)) (fun n point => value n (index n point)) := by
  obtain ⟨hv,error,he,hh⟩ := h
  exact ⟨hv.reindex index,error,he,hh.mono fun n hn point => hn (index n point)⟩

theorem neg {program : (n : ℕ) → Index n → ℚ} {value : (n : ℕ) → Index n → ℝ}
    (h : UniformRationalApproximation program value) :
    UniformRationalApproximation (fun n point => -program n point) (fun n point => -value n point) := by
  obtain ⟨hv,error,he,hh⟩ := h
  refine ⟨hv.neg,error,he,hh.mono ?_⟩
  intro n hn point
  simpa only [Rat.cast_neg,neg_sub_neg,abs_sub_comm] using hn point

theorem add {first second : (n : ℕ) → Index n → ℚ} {f s : (n : ℕ) → Index n → ℝ}
    (hf : UniformRationalApproximation first f) (hs : UniformRationalApproximation second s) :
    UniformRationalApproximation (fun n point => first n point+second n point) (fun n point => f n point+s n point) := by
  obtain ⟨hfv,fe,hfe,hf⟩ := hf
  obtain ⟨hsv,se,hse,hs⟩ := hs
  refine ⟨hfv.add hsv,(fun n => |fe n|+|se n|),(negligible_abs hfe).add (negligible_abs hse),?_⟩
  filter_upwards [hf,hs] with n hf hs point
  rw [Rat.cast_add,abs_of_nonneg (add_nonneg (abs_nonneg (fe n)) (abs_nonneg (se n)))]
  convert (abs_add_le _ _).trans (add_le_add (hf point) (hs point)) using 1
  congr 1
  ring

theorem sub {first second : (n : ℕ) → Index n → ℚ} {f s : (n : ℕ) → Index n → ℝ}
    (hf : UniformRationalApproximation first f) (hs : UniformRationalApproximation second s) :
    UniformRationalApproximation (fun n point => first n point-second n point) (fun n point => f n point-s n point) := by
  simpa only [sub_eq_add_neg] using hf.add hs.neg

theorem mul {first second : (n : ℕ) → Index n → ℚ} {f s : (n : ℕ) → Index n → ℝ}
    (hf : UniformRationalApproximation first f) (hs : UniformRationalApproximation second s) :
    UniformRationalApproximation (fun n point => first n point*second n point) (fun n point => f n point*s n point) := by
  obtain ⟨hfv,fe,hfe,hf⟩ := hf
  obtain ⟨hsv,se,hse,hs⟩ := hs
  refine ⟨hfv.mul hsv,?_⟩
  obtain ⟨C,a,hC,hfv⟩ := hfv
  obtain ⟨D,b,hD,hsv⟩ := hsv
  let error := fun (n : ℕ) => D*(n : ℝ)^b*|fe n|+(C+1)*(n : ℝ)^a*|se n|
  have he : Negligible error := by
    convert (((negligible_abs hfe).mul_polynomial b).const_mul D).add
      (((negligible_abs hse).mul_polynomial a).const_mul (C+1)) using 1
    funext n;dsimp only [error];ring
  refine ⟨error,he,?_⟩
  filter_upwards [hf,hs,hfv,hsv,hfe 0,eventually_ge_atTop 1] with n hf hs hfv hsv hsmall hn point
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have happ : |(first n point : ℝ)| ≤ (C+1)*(n : ℝ)^a := by
    have ht := abs_add_le ((first n point : ℝ)-f n point) (f n point)
    rw [sub_add_cancel] at ht
    simp only [pow_zero,div_one] at hsmall
    nlinarith [hf point,hfv point,one_le_pow₀ hn1 (n:=a)]
  rw [Rat.cast_mul]
  apply (V7Calibration.approximation_mul_error _ _ _ _).trans
  calc
    _ ≤ |fe n| *(D*(n : ℝ)^b)+((C+1)*(n : ℝ)^a)*|se n| :=
      add_le_add (mul_le_mul (hf point) (hsv point) (abs_nonneg _) (abs_nonneg _))
        (mul_le_mul happ (hs point) (abs_nonneg _) (by positivity))
    _ = error n := by dsimp only [error];ring
    _ ≤ |error n| := le_abs_self _

theorem sum {Source : ℕ → Type*} [∀ n,Fintype (Source n)]
    {program : (n : ℕ) → Source n × Index n → ℚ} {value : (n : ℕ) → Source n × Index n → ℝ}
    (h : UniformRationalApproximation program value)
    (cardinalConstant : ℝ) (cardinalDegree : ℕ) (hc : 0 ≤ cardinalConstant)
    (hcard : ∀ᶠ n : ℕ in atTop,(Fintype.card (Source n) : ℝ) ≤ cardinalConstant*(n : ℝ)^cardinalDegree) :
    UniformRationalApproximation (fun n point => ∑ source,program n (source,point))
      (fun n point => ∑ source,value n (source,point)) := by
  obtain ⟨hv,error,he,hh⟩ := h
  refine ⟨hv.sum cardinalConstant cardinalDegree hc hcard,
    (fun n => cardinalConstant*(n : ℝ)^cardinalDegree*|error n|),?_,?_⟩
  · convert ((negligible_abs he).mul_polynomial cardinalDegree).const_mul cardinalConstant using 1
    funext n;ring
  · filter_upwards [hh,hcard] with n hh hcard point
    rw [Rat.cast_sum,←Finset.sum_sub_distrib,abs_of_nonneg (show 0 ≤ cardinalConstant*(n : ℝ)^cardinalDegree*|error n| by positivity)]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _source : Source n,|error n| := Finset.sum_le_sum fun source _ => hh (source,point)
      _ = (Fintype.card (Source n) : ℝ)*|error n| := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (abs_nonneg _)

end UniformRationalApproximation
end
end AFT.RationalNumerics
