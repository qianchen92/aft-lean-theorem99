import AFT.PairedTableMean

/-! # Exact linear evaluation of represented paired public tables -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Color : Type*} [Fintype Color]

def tablePairedStatisticLinear (primary body : FiniteDist Color) (anchor : Color → Color → ℝ)
    (activation : ℝ) (primaryPool bodyPool : ℕ) :
    Table (InputSeed Color) →ₗ[ℝ] (((Fin primaryPool ⊕ Fin bodyPool) → Color × Color) → ℝ) :=
  Finsupp.linearCombination ℝ (monomialPairedStatistic primary body anchor activation primaryPool bodyPool)

theorem tablePairedStatisticLinear_apply (primary body : FiniteDist Color) (anchor : Color → Color → ℝ)
    (activation : ℝ) (primaryPool bodyPool : ℕ) (table : Table (InputSeed Color)) :
    tablePairedStatisticLinear primary body anchor activation primaryPool bodyPool table =
      tablePairedStatistic primary body anchor activation primaryPool bodyPool table := by
  funext word
  change (∑ powers ∈ table.support, MvPolynomial.coeff powers table •
    monomialPairedStatistic primary body anchor activation primaryPool bodyPool powers) word = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rfl

theorem tablePairedStatistic_monomial (primary body : FiniteDist Color) (anchor : Color → Color → ℝ)
    (activation : ℝ) (primaryPool bodyPool : ℕ) (powers : InputSeed Color →₀ ℕ) (scalar : ℝ) :
    tablePairedStatistic primary body anchor activation primaryPool bodyPool (MvPolynomial.monomial powers scalar) =
      scalar • monomialPairedStatistic primary body anchor activation primaryPool bodyPool powers := by
  rw [← tablePairedStatisticLinear_apply]
  exact Finsupp.linearCombination_single ℝ scalar powers

omit [Fintype Color] in
theorem monomialOccurrences_single (seed : InputSeed Color) :
    monomialOccurrences (Finsupp.single seed 1) = [seed] := by
  unfold monomialOccurrences
  rw [Finsupp.support_single_ne_zero _ (by norm_num : (1 : ℕ) ≠ 0), Finset.toList_singleton]
  simp
end
end AFT.RepresentedPolynomial
