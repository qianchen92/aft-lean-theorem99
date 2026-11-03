import CurrentAFT.CommonQueueAssembly
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities

/-!
# Finite product cancellation in the actual truncated algebra

Elementary symmetric sums of the actual positive-degree atoms satisfy
Newton's identities. Products of more atoms than the truncation order
vanish by the proved arity filtration. This gives a finite product
representation that retains cancellation of the complete linear sum,
without multiplying norms of individually unbalanced populations.
-/

namespace CurrentAFT.GradedNewton

open AFT ControlCoordinates GradedControlAlgebra GradedInverse CommonQueueAssembly
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {Primary Body Index : Type*} [Fintype Primary] [Fintype Body] [Fintype Index]

private theorem generic_newton {Ring : Type*} [CommRing Ring]
    (atoms : Index → Ring) (degree : ℕ) :
    (degree : Ring) * (∑ selected ∈ Finset.univ.powersetCard degree, ∏ index ∈ selected, atoms index) =
      (-1) ^ (degree + 1) *
        ∑ pair ∈ (Finset.antidiagonal degree).filter (fun pair => pair.1 < degree),
          (-1) ^ pair.1 * (∑ selected ∈ Finset.univ.powersetCard pair.1, ∏ index ∈ selected, atoms index) *
            (∑ index, atoms index ^ pair.2) := by
  let evaluation := MvPolynomial.eval₂Hom (Int.castRingHom Ring) atoms
  have h := congrArg evaluation (MvPolynomial.mul_esymm_eq_sum Index ℤ degree)
  simpa only [evaluation, map_mul, map_natCast, map_pow, map_neg, map_one, map_sum,
    MvPolynomial.esymm, MvPolynomial.psum, map_prod, MvPolynomial.eval₂Hom_X'] using h

def elementary (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (atoms : Index → KernelFamily primary body order) (degree : ℕ) : KernelFamily primary body order :=
  ∑ selected ∈ Finset.univ.powersetCard degree, ∏ index ∈ selected, atoms index

def powerSum (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (atoms : Index → KernelFamily primary body order) (power : ℕ) : KernelFamily primary body order :=
  ∑ index, atoms index ^ power

theorem elementary_zero (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (atoms : Index → KernelFamily primary body order) : elementary primary body order atoms 0 = 1 := by
  simp only [elementary, Finset.powersetCard_zero, Finset.sum_singleton, Finset.prod_empty]

theorem elementary_one (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (atoms : Index → KernelFamily primary body order) :
    elementary primary body order atoms 1 = ∑ index, atoms index := by
  simp [elementary, Finset.powersetCard_one]

/-- This identity is evaluated from the existing integer polynomial
identity, using the actual finite convolution ring, rather than assumed. -/
theorem newton_identity (primary : FiniteDist Primary) (body : FiniteDist Body) (order degree : ℕ)
    (atoms : Index → KernelFamily primary body order) :
    (degree : KernelFamily primary body order) * elementary primary body order atoms degree =
      (-1) ^ (degree + 1) *
        ∑ pair ∈ (Finset.antidiagonal degree).filter (fun pair => pair.1 < degree),
          (-1) ^ pair.1 * elementary primary body order atoms pair.1 *
            powerSum primary body order atoms pair.2 := by
  exact generic_newton atoms degree

omit [Fintype Index] in
theorem product_vanishesBelow (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (atoms : Index → KernelFamily primary body order)
    (hzero : ∀ index, atoms index (zeroArity order) = 0) (selected : Finset Index) :
    VanishesBelow primary body order selected.card (∏ index ∈ selected, atoms index) := by
  induction selected using Finset.induction_on with
  | empty => exact vanishesBelow_zero primary body order _
  | @insert index selected hnot ih =>
    rw [Finset.prod_insert hnot, Finset.card_insert_of_notMem hnot]
    have h := vanishesBelow_mul primary body order 1 selected.card _ _
      (vanishesBelow_one_of_zero primary body order (atoms index) (hzero index)) ih
    simpa only [Nat.add_comm 1] using h

theorem elementary_above_order (primary : FiniteDist Primary) (body : FiniteDist Body) (order degree : ℕ)
    (atoms : Index → KernelFamily primary body order)
    (hzero : ∀ index, atoms index (zeroArity order) = 0) (hdegree : order < degree) :
    elementary primary body order atoms degree = 0 := by
  unfold elementary
  apply Finset.sum_eq_zero
  intro selected hselected
  have hcard := (Finset.mem_powersetCard.mp hselected).2
  have h := product_vanishesBelow primary body order atoms hzero selected
  funext arity
  apply h arity
  have := arity.property
  omega

theorem product_one_add_eq_truncated_sum (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (atoms : Index → KernelFamily primary body order)
    (hzero : ∀ index, atoms index (zeroArity order) = 0) (hsize : order ≤ Fintype.card Index) :
    (∏ index, (1 + atoms index)) = ∑ degree ∈ Finset.range (order + 1), elementary primary body order atoms degree := by
  rw [Finset.prod_one_add, Finset.sum_powerset]
  change (∑ degree ∈ Finset.range (Fintype.card Index + 1), elementary primary body order atoms degree) = _
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega : order + 1 ≤ Fintype.card Index + 1))
  intro degree _ hnot
  exact elementary_above_order primary body order degree atoms hzero (by
    simp only [Finset.mem_range] at hnot
    omega)

theorem product_one_add_sub_one (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (atoms : Index → KernelFamily primary body order)
    (hzero : ∀ index, atoms index (zeroArity order) = 0) (hsize : order ≤ Fintype.card Index) :
    (∏ index, (1 + atoms index)) - 1 =
      ∑ degree ∈ Finset.range order, elementary primary body order atoms (degree + 1) := by
  rw [product_one_add_eq_truncated_sum primary body order atoms hzero hsize,
    Finset.sum_range_succ', elementary_zero]
  abel

end

end CurrentAFT.GradedNewton
