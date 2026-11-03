import AFT.RepresentedControlKernel
import AFT.RepresentedLogarithm
import AFT.RepresentedQueue
import Mathlib.Algebra.MvPolynomial.Variables

/-! # Canonical seed support is preserved by the finite control algebra -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
variable {Color : Type*} [Fintype Color]

def InputTableCanonical (primary body : FiniteDist Color) (table : Table (InputSeed Color)) : Prop :=
  ∀ powers ∈ table.support, ∀ seed ∈ powers.support,
    Hoeffding.Canonical (inputReference primary body seed) Finset.univ seed.kernel

theorem inputTableCanonical_iff_vars (primary body : FiniteDist Color) (table : Table (InputSeed Color)) :
    InputTableCanonical primary body table ↔ ∀ seed ∈ table.vars,
      Hoeffding.Canonical (inputReference primary body seed) Finset.univ seed.kernel := by
  constructor
  · intro h seed hs
    obtain ⟨powers, hp, hs⟩ := (MvPolynomial.mem_vars seed).mp hs
    exact h powers hp seed hs
  · intro h powers hp seed hs
    exact h seed ((MvPolynomial.mem_vars seed).mpr ⟨powers, hp, hs⟩)

namespace InputTableCanonical
variable {primary body : FiniteDist Color} {first second : Table (InputSeed Color)}

theorem C (scalar : ℝ) : InputTableCanonical primary body (MvPolynomial.C scalar) := by
  rw [inputTableCanonical_iff_vars]
  simp

theorem zero : InputTableCanonical primary body (0 : Table (InputSeed Color)) := by simpa using C (primary := primary) (body := body) 0

theorem one : InputTableCanonical primary body (1 : Table (InputSeed Color)) := by simpa using C (primary := primary) (body := body) 1

theorem X (seed : InputSeed Color)
    (h : Hoeffding.Canonical (inputReference primary body seed) Finset.univ seed.kernel) :
    InputTableCanonical primary body (MvPolynomial.X seed) := by
  rw [inputTableCanonical_iff_vars]
  simpa using h

theorem add (hfirst : InputTableCanonical primary body first) (hsecond : InputTableCanonical primary body second) :
    InputTableCanonical primary body (first + second) := by
  rw [inputTableCanonical_iff_vars] at *
  intro seed hs
  rcases Finset.mem_union.mp (MvPolynomial.vars_add_subset first second hs) with hs | hs
  · exact hfirst seed hs
  · exact hsecond seed hs

theorem mul (hfirst : InputTableCanonical primary body first) (hsecond : InputTableCanonical primary body second) :
    InputTableCanonical primary body (first * second) := by
  rw [inputTableCanonical_iff_vars] at *
  intro seed hs
  rcases Finset.mem_union.mp (MvPolynomial.vars_mul first second hs) with hs | hs
  · exact hfirst seed hs
  · exact hsecond seed hs

theorem neg (h : InputTableCanonical primary body first) : InputTableCanonical primary body (-first) := by
  simpa using (C (primary := primary) (body := body) (-1)).mul h

theorem sub (hfirst : InputTableCanonical primary body first) (hsecond : InputTableCanonical primary body second) :
    InputTableCanonical primary body (first - second) := by
  simpa only [sub_eq_add_neg] using hfirst.add hsecond.neg

theorem pow (h : InputTableCanonical primary body first) (power : ℕ) :
    InputTableCanonical primary body (first ^ power) := by
  rw [inputTableCanonical_iff_vars] at *
  exact fun seed hs => h seed (MvPolynomial.vars_pow first power hs)

theorem sum {Index : Type*} (indices : Finset Index) (tables : Index → Table (InputSeed Color))
    (h : ∀ index ∈ indices, InputTableCanonical primary body (tables index)) :
    InputTableCanonical primary body (∑ index ∈ indices, tables index) := by
  induction indices using Finset.induction_on with
  | empty => simpa using zero (primary := primary) (body := body)
  | @insert index indices hi ih =>
    rw [Finset.sum_insert hi]
    exact (h index (Finset.mem_insert_self ..)).add (ih fun other ho => h other (Finset.mem_insert_of_mem ho))

theorem exponential (h : InputTableCanonical primary body first) (degree : ℕ) :
    InputTableCanonical primary body (RepresentedPolynomial.exponential first degree) :=
  sum _ _ fun _ _ => (C _).mul (h.pow _)

theorem logarithm (h : InputTableCanonical primary body first) (degree : ℕ) :
    InputTableCanonical primary body (RepresentedPolynomial.logarithm first degree) :=
  sum _ _ fun _ _ => (C _).mul (h.pow _)

theorem finiteCorrection (h : InputTableCanonical primary body first) (depth : ℕ) :
    InputTableCanonical primary body (AFT.finiteCorrection first depth) :=
  sum _ _ fun _ _ => h.neg.pow _

theorem queueAverage {Queue : Type*} [Fintype Queue] (queue : FiniteDist Queue)
    (tables : Queue → Table (InputSeed Color)) (h : ∀ value, InputTableCanonical primary body (tables value)) :
    InputTableCanonical primary body (RepresentedPolynomial.queueAverage queue tables) :=
  sum _ _ fun value _ => (C _).mul (h value)

theorem truncate (h : InputTableCanonical primary body first) (order : InputSeed Color → ℕ) (cutoff : ℕ) :
    InputTableCanonical primary body (RepresentedPolynomial.truncate order cutoff first) := by
  intro powers hp seed hs
  exact h powers (Finset.mem_filter.mp hp).1 seed hs

/-- Renaming may identify labels; canonicality only needs the actual
transformed seeds appearing in the original finite support. -/
theorem rename (transform : InputSeed Color → InputSeed Color)
    (h : ∀ seed ∈ first.vars, Hoeffding.Canonical (inputReference primary body (transform seed)) Finset.univ (transform seed).kernel) :
    InputTableCanonical primary body (MvPolynomial.rename transform first) := by
  rw [inputTableCanonical_iff_vars]
  intro seed hs
  obtain ⟨source, hm, rfl⟩ := MvPolynomial.mem_vars_rename transform first hs
  exact h source hm

end InputTableCanonical
end
end AFT.RepresentedPolynomial
