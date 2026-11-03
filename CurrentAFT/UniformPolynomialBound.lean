import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! Polynomial witnesses for specified natural-number resource functions,
uniform at every security parameter. This predicate has no program field. -/
namespace CurrentAFT

def UniformPolynomialBound (resource : ℕ → ℕ) : Prop :=
  ∃ polynomial : Polynomial ℕ, ∀ security, resource security ≤ polynomial.eval security

namespace UniformPolynomialBound

theorem constant (value : ℕ) : UniformPolynomialBound (fun _ => value) :=
  ⟨Polynomial.C value, fun _ => by simp⟩

theorem identity : UniformPolynomialBound id :=
  ⟨Polynomial.X, fun _ => by simp⟩

theorem polynomial (value : Polynomial ℕ) : UniformPolynomialBound value.eval :=
  ⟨value, fun _ => le_rfl⟩

theorem mono {first second : ℕ → ℕ} (h : UniformPolynomialBound second)
    (hle : ∀ security, first security ≤ second security) : UniformPolynomialBound first := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, fun security => (hle security).trans (hp security)⟩

theorem add {first second : ℕ → ℕ} (h : UniformPolynomialBound first) (g : UniformPolynomialBound second) :
    UniformPolynomialBound (fun n => first n+second n) := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨q, hq⟩ := g
  exact ⟨p+q, fun n => by simpa only [Polynomial.eval_add] using Nat.add_le_add (hp n) (hq n)⟩

theorem mul {first second : ℕ → ℕ} (h : UniformPolynomialBound first) (g : UniformPolynomialBound second) :
    UniformPolynomialBound (fun n => first n*second n) := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨q, hq⟩ := g
  exact ⟨p*q, fun n => by simpa only [Polynomial.eval_mul] using Nat.mul_le_mul (hp n) (hq n)⟩

theorem pow {resource : ℕ → ℕ} (h : UniformPolynomialBound resource) (power : ℕ) :
    UniformPolynomialBound (fun n => resource n^power) := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p^power, fun n => by simpa only [Polynomial.eval_pow] using Nat.pow_le_pow_left (hp n) power⟩

theorem subtract {resource : ℕ → ℕ} (h : UniformPolynomialBound resource) (other : ℕ → ℕ) :
    UniformPolynomialBound (fun n => resource n-other n) := h.mono (fun _ => Nat.sub_le ..)

end UniformPolynomialBound
end CurrentAFT
