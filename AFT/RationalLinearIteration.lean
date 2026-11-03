import AFT.FinitePrimaryInverse
import AFT.RationalHeight

/-! # Executable linear iteration and stability in primary activity -/
namespace AFT.RationalNumerics
open scoped BigOperators

def matrixApply {Color : Type*} [Fintype Color]
    (matrix : Color → Color → ℚ) (profile : Color → ℚ) (output : Color) : ℚ :=
  ∑ input,matrix output input*profile input

/-- The same right-hand side and stored matrix are used at every step. -/
def linearIteration {Color : Type*} [Fintype Color]
    (matrix : Color → Color → ℚ) (rhs : Color → ℚ) : ℕ → Color → ℚ
  | 0 => 0
  | steps+1 => rhs-matrixApply matrix (linearIteration matrix rhs steps)

def linearIterationWork (colors steps : ℕ) : ℕ := steps*(2*colors^2+colors)

theorem linearIterationWork_succ (colors steps : ℕ) :
    linearIterationWork colors (steps+1)=linearIterationWork colors steps+2*colors^2+colors := by
  unfold linearIterationWork
  ring

noncomputable section

def realMatrixOperator {Color : Type*} [Fintype Color] (matrix : Color → Color → ℚ) :
    Module.End ℝ (Color → ℝ) where
  toFun profile output := ∑ input,(matrix output input : ℝ)*profile input
  map_add' first second := by
    funext output
    simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' scalar profile := by
    funext output
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro input _
    ring

def realLinearIteration {Color : Type*}
    (operator : Module.End ℝ (Color → ℝ)) (rhs : Color → ℝ) : ℕ → Color → ℝ
  | 0 => 0
  | steps+1 => rhs-operator (realLinearIteration operator rhs steps)

theorem linearIteration_cast {Color : Type*} [Fintype Color]
    (matrix : Color → Color → ℚ) (rhs : Color → ℚ) (steps : ℕ) :
    (fun color => (linearIteration matrix rhs steps color : ℝ))=
      realLinearIteration (realMatrixOperator matrix) (fun color => (rhs color : ℝ)) steps := by
  induction steps with
  | zero => ext color;simp [linearIteration,realLinearIteration]
  | succ steps ih =>
    funext output
    simp only [linearIteration,realLinearIteration,Pi.sub_apply,matrixApply,Rat.cast_sub,
      Rat.cast_sum,Rat.cast_mul,realMatrixOperator,LinearMap.coe_mk,AddHom.coe_mk]
    simp_rw [show ∀ color,(linearIteration matrix rhs steps color : ℝ)=
      realLinearIteration (realMatrixOperator matrix) (fun color => (rhs color : ℝ)) steps color
      from fun color => congrFun ih color]
    rfl

/-- A small residual and a half-contractive implemented matrix suffice for
stable iteration. No error proportional to the number of steps occurs. -/
theorem primaryActivity_iteration_error {Color : Type*} [Fintype Color]
    (operator : Module.End ℝ (Color → ℝ)) (rhs target : Color → ℝ)
    (rate : ℝ) (primary : Color → ℝ) (error : ℝ)
    (hrate : 0≤rate) (hp : ∀ color,0<primary color) (he : 0≤error)
    (hcontract : ∀ profile,primaryActivity rate primary (operator profile)≤
      (1/2)*primaryActivity rate primary profile)
    (hresidual : primaryActivity rate primary (rhs-operator target-target)≤error)
    (steps : ℕ) :
    primaryActivity rate primary (realLinearIteration operator rhs steps-target)≤
      (1/2 : ℝ)^steps*primaryActivity rate primary target+2*error := by
  induction steps with
  | zero =>
    simp only [realLinearIteration,zero_sub,primaryActivity_neg,pow_zero,one_mul]
    linarith
  | succ steps ih =>
    have hidentity : realLinearIteration operator rhs (steps+1)-target=
        (rhs-operator target-target)+-(operator (realLinearIteration operator rhs steps-target)) := by
      simp only [realLinearIteration,map_sub]
      abel
    rw [hidentity]
    apply (primaryActivity_add_le rate primary _ _ hrate hp).trans
    rw [primaryActivity_neg]
    apply (add_le_add hresidual (hcontract _)).trans
    have hh := mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ)≤1/2)
    rw [pow_succ]
    linarith

theorem rational_linear_iteration_error {Color : Type*} [Fintype Color]
    (matrix : Color → Color → ℚ) (rhs : Color → ℚ) (target : Color → ℝ)
    (rate : ℝ) (primary : Color → ℝ) (error : ℝ)
    (hrate : 0≤rate) (hp : ∀ color,0<primary color) (he : 0≤error)
    (hcontract : ∀ profile,primaryActivity rate primary (realMatrixOperator matrix profile)≤
      (1/2)*primaryActivity rate primary profile)
    (hresidual : primaryActivity rate primary
      ((fun color => (rhs color : ℝ))-realMatrixOperator matrix target-target)≤error)
    (steps : ℕ) :
    primaryActivity rate primary ((fun color => (linearIteration matrix rhs steps color : ℝ))-target)≤
      (1/2 : ℝ)^steps*primaryActivity rate primary target+2*error := by
  rw [linearIteration_cast]
  exact primaryActivity_iteration_error _ _ _ _ _ _ hrate hp he hcontract hresidual steps

end
end AFT.RationalNumerics
