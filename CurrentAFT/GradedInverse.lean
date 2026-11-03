import CurrentAFT.GradedControlAlgebra

/-!
# Exact finite inverses in the actual truncated control algebra

The augmentation ideal is nilpotent because its products increase total
arity. Consequently every background with scalar coordinate one has an
explicit finite inverse. This algebraic inverse needs no assumed
invertibility and is separate from the quantitative stability estimates.
-/

namespace CurrentAFT.GradedInverse

open AFT ControlCoordinates ControlProduct GradedControlAlgebra
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

def VanishesBelow (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order degree : ℕ) (family : KernelFamily primary body order) : Prop :=
  ∀ arity, arity.val.1.val + arity.val.2.val < degree → family arity = 0

theorem vanishesBelow_zero (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (family : KernelFamily primary body order) :
    VanishesBelow primary body order 0 family := by
  intro arity hdegree
  omega

theorem vanishesBelow_mul (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order firstDegree secondDegree : ℕ) (first second : KernelFamily primary body order)
    (hfirst : VanishesBelow primary body order firstDegree first)
    (hsecond : VanishesBelow primary body order secondDegree second) :
    VanishesBelow primary body order (firstDegree + secondDegree) (first * second) := by
  intro output houtput
  change familyProduct primary body order first second output = 0
  unfold familyProduct
  apply Finset.sum_eq_zero
  intro left _
  apply Finset.sum_eq_zero
  intro right _
  split_ifs with hmatch
  · by_cases hleft : left.val.1.val + left.val.2.val < firstDegree
    · rw [hfirst left hleft, homogeneousProduct_zero_left, transportKernel_zero]
    · have hright : right.val.1.val + right.val.2.val < secondDegree := by omega
      rw [hsecond right hright, homogeneousProduct_zero_right, transportKernel_zero]
  · rfl

theorem vanishesBelow_one_of_zero (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (family : KernelFamily primary body order)
    (hzero : family (zeroArity order) = 0) :
    VanishesBelow primary body order 1 family := by
  intro arity hdegree
  have harity : arity = zeroArity order := by
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · change arity.val.1.val = 0
      omega
    · change arity.val.2.val = 0
      omega
  rw [harity, hzero]

theorem vanishesBelow_pow (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (family : KernelFamily primary body order)
    (hfirst : VanishesBelow primary body order 1 family) (power : ℕ) :
    VanishesBelow primary body order power (family ^ power) := by
  induction power with
  | zero => exact vanishesBelow_zero primary body order _
  | succ power ih =>
    rw [pow_succ]
    exact vanishesBelow_mul primary body order power 1 _ family ih hfirst

theorem augmentation_nilpotent (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (family : KernelFamily primary body order)
    (hzero : family (zeroArity order) = 0) : family ^ (order + 1) = 0 := by
  have h := vanishesBelow_pow primary body order family
    (vanishesBelow_one_of_zero primary body order family hzero) (order + 1)
  funext arity
  exact h arity (by have := arity.property; omega)

def backgroundInverse (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (background : KernelFamily primary body order) : KernelFamily primary body order :=
  ∑ power ∈ Finset.range (order + 1), (1 - background) ^ power

theorem backgroundInverse_mul (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (background : KernelFamily primary body order)
    (hscalar : background (zeroArity order) = (1 : KernelFamily primary body order) (zeroArity order)) :
    backgroundInverse primary body order background * background = 1 := by
  have hzero : (1 - background : KernelFamily primary body order) (zeroArity order) = 0 := by
    change (1 : KernelFamily primary body order) (zeroArity order) - background (zeroArity order) = 0
    rw [hscalar, sub_self]
  have hnil := augmentation_nilpotent primary body order (1 - background) hzero
  have hgeom : (∑ power ∈ Finset.range (order + 1), (1 - background) ^ power) *
      (1 - (1 - background)) = 1 - (1 - background) ^ (order + 1) :=
    geom_sum_mul_neg (1 - background) (order + 1)
  simpa only [backgroundInverse, sub_sub_cancel, hnil, sub_zero] using hgeom

theorem mul_backgroundInverse (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (background : KernelFamily primary body order)
    (hscalar : background (zeroArity order) = (1 : KernelFamily primary body order) (zeroArity order)) :
    background * backgroundInverse primary body order background = 1 := by
  rw [mul_comm]
  exact backgroundInverse_mul primary body order background hscalar

end

end CurrentAFT.GradedInverse
