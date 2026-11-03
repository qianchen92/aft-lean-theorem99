import AFT.RepresentedQueue

/-!
# The actual quotient ring of specified input seed polynomials

Only coefficients above the input-order cutoff are identified.  In
particular, equality of output images is never a quotient relation here.
-/

namespace AFT.RepresentedPolynomial

open scoped BigOperators Classical

noncomputable section

variable {Seed : Type*}

def cutoffIdeal (order : Seed → ℕ) (cutoff : ℕ) : Ideal (Table Seed) where
  carrier := {table | HasOrder order (cutoff + 1) table}
  zero_mem' := by intro powers _; simp
  add_mem' := by
    intro first second hfirst hsecond powers hp
    simp only [MvPolynomial.coeff_add, hfirst powers hp, hsecond powers hp, add_zero]
  smul_mem' := by
    intro scalar table htable
    simpa only [zero_add] using
      hasOrder_mul order 0 (cutoff + 1) scalar table (hasOrder_zero order scalar) htable

abbrev CutoffRing (order : Seed → ℕ) (cutoff : ℕ) := (Table Seed) ⧸ cutoffIdeal order cutoff

def quotientMap (order : Seed → ℕ) (cutoff : ℕ) : Table Seed →+* CutoffRing order cutoff :=
  Ideal.Quotient.mk (cutoffIdeal order cutoff)

theorem quotient_eq_iff_truncate (order : Seed → ℕ) (cutoff : ℕ) (first second : Table Seed) :
    quotientMap order cutoff first = quotientMap order cutoff second ↔
      truncate order cutoff first = truncate order cutoff second := by
  rw [quotientMap, Ideal.Quotient.eq]
  change HasOrder order (cutoff + 1) (first - second) ↔ _
  constructor
  · intro h
    have hh := truncate_of_hasOrder order cutoff (first - second) h
    rw [truncate_sub, sub_eq_zero] at hh
    exact hh
  · intro h powers hp
    have hh := congrArg (MvPolynomial.coeff powers) h
    rw [coeff_truncate, coeff_truncate, if_pos (by omega), if_pos (by omega)] at hh
    simp only [MvPolynomial.coeff_sub, hh, sub_self]

theorem quotient_pow_zero (order : Seed → ℕ) (cutoff : ℕ) (table : Table Seed)
    (h : HasOrder order 1 table) : quotientMap order cutoff table ^ (cutoff + 1) = 0 := by
  rw [← map_pow]
  apply (Ideal.Quotient.eq_zero_iff_mem).mpr
  have hh := hasOrder_pow order 1 table h (cutoff + 1)
  simpa only [mul_one] using hh

theorem quotient_nilpotent (order : Seed → ℕ) (cutoff : ℕ) (table : Table Seed)
    (h : HasOrder order 1 table) : IsNilpotent (quotientMap order cutoff table) :=
  ⟨cutoff + 1, quotient_pow_zero order cutoff table h⟩

@[simp] theorem quotient_C (order : Seed → ℕ) (cutoff : ℕ) (scalar : ℝ) :
    quotientMap order cutoff (MvPolynomial.C scalar) = algebraMap ℝ (CutoffRing order cutoff) scalar := rfl

theorem quotient_exponential (order : Seed → ℕ) (cutoff : ℕ) (table : Table Seed)
    (h : HasOrder order 1 table) :
    quotientMap order cutoff (exponential table cutoff) = IsNilpotent.exp (quotientMap order cutoff table) := by
  rw [IsNilpotent.exp_eq_sum (quotient_pow_zero order cutoff table h)]
  simp only [exponential, map_sum, map_mul, map_pow, quotient_C, Algebra.smul_def]
  apply Finset.sum_congr rfl
  intro index _
  congr 1
  have heq : algebraMap ℚ (CutoffRing order cutoff) ((index.factorial : ℚ)⁻¹) =
      algebraMap ℝ (CutoffRing order cutoff) ((index.factorial : ℝ)⁻¹) := by
    rw [IsScalarTower.algebraMap_apply ℚ ℝ (CutoffRing order cutoff)]
    simp
  exact heq.symm

/-- The finite exponential is exactly multiplicative after the specified
input cutoff, not just bounded in activity. -/
theorem truncate_exponential_add (order : Seed → ℕ) (cutoff : ℕ) (first second : Table Seed)
    (hfirst : HasOrder order 1 first) (hsecond : HasOrder order 1 second) :
    truncate order cutoff (exponential (first + second) cutoff) =
      truncate order cutoff (exponential first cutoff * exponential second cutoff) := by
  apply (quotient_eq_iff_truncate order cutoff _ _).mp
  have hadd : HasOrder order 1 (first + second) := by
    intro powers hp
    simp only [MvPolynomial.coeff_add, hfirst powers hp, hsecond powers hp, add_zero]
  rw [quotient_exponential order cutoff _ hadd, map_mul,
    quotient_exponential order cutoff _ hfirst, quotient_exponential order cutoff _ hsecond,
    map_add]
  exact IsNilpotent.exp_add_of_commute (Commute.all _ _)
    (quotient_nilpotent order cutoff first hfirst) (quotient_nilpotent order cutoff second hsecond)

end

end AFT.RepresentedPolynomial
