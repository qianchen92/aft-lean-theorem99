import AFT.RepresentedTruncation

/-!
# The literal truncated endpoint polynomial algebra

Elements are actual real multivariate polynomials fixed by the total-degree
cutoff. Multiplication is their actual polynomial product followed by that
cutoff. The ring and real-algebra laws follow from the proved coefficient
truncation identities; they are not abstract response assumptions.
-/

namespace CurrentAFT.TruncatedOutput

open AFT.RepresentedPolynomial
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {Variable : Type*}

def cut (order : ℕ) (polynomial : MvPolynomial Variable ℝ) : MvPolynomial Variable ℝ :=
  truncate (fun _ => 1) order polynomial

theorem cut_smul (order : ℕ) (scalar : ℝ) (polynomial : MvPolynomial Variable ℝ) :
    cut order (scalar • polynomial) = scalar • cut order polynomial := by
  ext powers
  simp only [cut, coeff_truncate, MvPolynomial.coeff_smul, smul_eq_mul]
  split_ifs <;> simp

theorem cut_constant (order : ℕ) (scalar : ℝ) : cut order (MvPolynomial.C scalar : MvPolynomial Variable ℝ) =
    MvPolynomial.C scalar := by
  ext powers
  by_cases hzero : powers = 0
  · subst powers
    simp only [cut, coeff_truncate, weightedOrder_zero, Nat.zero_le, if_true]
  · simp only [cut, coeff_truncate, MvPolynomial.coeff_C, Ne.symm hzero, if_false, ite_self]

def space (Variable : Type*) (order : ℕ) : Submodule ℝ (MvPolynomial Variable ℝ) where
  carrier := {polynomial | cut order polynomial = polynomial}
  zero_mem' := truncate_zero _ _
  add_mem' := by
    intro first second hfirst hsecond
    change cut order (first + second) = first + second
    rw [cut, truncate_add, ← cut, ← cut, hfirst, hsecond]
  smul_mem' := by
    intro scalar polynomial hpolynomial
    change cut order (scalar • polynomial) = scalar • polynomial
    change cut order polynomial = polynomial at hpolynomial
    rw [cut_smul, hpolynomial]

abbrev Polynomial (Variable : Type*) (order : ℕ) := space Variable order

def project (order : ℕ) (polynomial : MvPolynomial Variable ℝ) : Polynomial Variable order :=
  ⟨cut order polynomial, truncate_idempotent _ _ _⟩

instance polynomialOne (order : ℕ) : One (Polynomial Variable order) :=
  ⟨⟨1, truncate_one _ _⟩⟩

instance polynomialMul (order : ℕ) : Mul (Polynomial Variable order) :=
  ⟨fun first second => project order (first.val * second.val)⟩

instance polynomialNatCast (order : ℕ) : NatCast (Polynomial Variable order) :=
  ⟨fun natural => natural • (1 : Polynomial Variable order)⟩

instance polynomialIntCast (order : ℕ) : IntCast (Polynomial Variable order) :=
  ⟨fun integer => integer • (1 : Polynomial Variable order)⟩

theorem polynomial_mul_assoc (order : ℕ) (first second third : Polynomial Variable order) :
    first * second * third = first * (second * third) := by
  apply Subtype.ext
  change cut order (cut order (first.val * second.val) * third.val) =
    cut order (first.val * cut order (second.val * third.val))
  have hleft := truncate_mul (fun _ : Variable => 1) order (first.val * second.val) third.val
  have hright := truncate_mul (fun _ : Variable => 1) order first.val (second.val * third.val)
  change cut order (first.val * second.val * third.val) =
    cut order (cut order (first.val * second.val) * cut order third.val) at hleft
  change cut order (first.val * (second.val * third.val)) =
    cut order (cut order first.val * cut order (second.val * third.val)) at hright
  rw [third.property] at hleft
  rw [first.property] at hright
  exact hleft.symm.trans ((congrArg (cut order) (mul_assoc first.val second.val third.val)).trans hright)

instance polynomialCommRing (order : ℕ) : CommRing (Polynomial Variable order) where
  __ := inferInstanceAs (AddCommGroup (Polynomial Variable order))
  mul first second := project order (first.val * second.val)
  one := ⟨1, truncate_one _ _⟩
  mul_assoc := polynomial_mul_assoc order
  mul_comm first second := by apply Subtype.ext; exact congrArg (cut order) (mul_comm first.val second.val)
  one_mul polynomial := by apply Subtype.ext; change cut order (1 * polynomial.val) = _; rw [one_mul, polynomial.property]
  mul_one polynomial := by apply Subtype.ext; change cut order (polynomial.val * 1) = _; rw [mul_one, polynomial.property]
  zero_mul polynomial := by apply Subtype.ext; change cut order (0 * polynomial.val) = _; simp only [zero_mul, cut, truncate_zero, Submodule.coe_zero]
  mul_zero polynomial := by apply Subtype.ext; change cut order (polynomial.val * 0) = _; simp only [mul_zero, cut, truncate_zero, Submodule.coe_zero]
  left_distrib first second third := by
    apply Subtype.ext
    change cut order (first.val * (second.val + third.val)) = cut order (first.val * second.val) + cut order (first.val * third.val)
    simp only [mul_add, cut, truncate_add]
  right_distrib first second third := by
    apply Subtype.ext
    change cut order ((first.val + second.val) * third.val) = cut order (first.val * third.val) + cut order (second.val * third.val)
    simp only [add_mul, cut, truncate_add]
  natCast natural := natural • (1 : Polynomial Variable order)
  natCast_zero := zero_nsmul _
  natCast_succ natural := by rw [add_nsmul, one_nsmul]
  intCast integer := integer • (1 : Polynomial Variable order)
  intCast_ofNat natural := by
    change (natural : ℤ) • (1 : Polynomial Variable order) = natural • (1 : Polynomial Variable order)
    simp
  intCast_negSucc natural := by
    change (Int.negSucc natural) • (1 : Polynomial Variable order) = -((natural + 1) • (1 : Polynomial Variable order))
    simp

theorem polynomial_smul_mul (order : ℕ) (scalar : ℝ) (first second : Polynomial Variable order) :
    (scalar • first) * second = scalar • (first * second) := by
  apply Subtype.ext
  change cut order ((scalar • first.val) * second.val) = scalar • cut order (first.val * second.val)
  rw [smul_mul_assoc, cut_smul]

theorem polynomial_mul_smul (order : ℕ) (scalar : ℝ) (first second : Polynomial Variable order) :
    first * (scalar • second) = scalar • (first * second) := by
  rw [mul_comm first, polynomial_smul_mul, mul_comm second]

instance polynomialAlgebra (order : ℕ) : Algebra ℝ (Polynomial Variable order) :=
  Algebra.ofModule (polynomial_smul_mul order) (polynomial_mul_smul order)

def quotientMap (order : ℕ) : MvPolynomial Variable ℝ →ₐ[ℝ] Polynomial Variable order where
  toFun := project order
  map_zero' := by apply Subtype.ext; exact truncate_zero _ _
  map_one' := by apply Subtype.ext; exact truncate_one _ _
  map_add' first second := by apply Subtype.ext; exact truncate_add _ _ first second
  map_mul' first second := by apply Subtype.ext; exact truncate_mul _ _ first second
  commutes' scalar := by
    apply Subtype.ext
    change cut order (MvPolynomial.C scalar) = scalar • (1 : MvPolynomial Variable ℝ)
    rw [cut_constant, Algebra.smul_def, mul_one]
    rfl

end

end CurrentAFT.TruncatedOutput
