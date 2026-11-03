import AFT.PairedTableMoment

/-! # Exact mean of the complete paired public correction -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance pairedTableMeanSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
variable {Color : Type*} [Fintype Color]

theorem monomialPairedStatistic_mean_zero (primary body : FiniteDist Color)
    (anchor : Color → Color → ℝ) (activation : ℝ)
    (hmass : ∀ color, ∑ center, anchor color center = 1)
    (hsupport : ∀ point center, body.weight center = 0 → anchor point center = 0)
    (primaryPool bodyPool : ℕ) (powers : InputSeed Color →₀ ℕ)
    (hc : ∀ seed ∈ powers.support, Hoeffding.Canonical (inputReference primary body seed) Finset.univ seed.kernel)
    (horder : 0 < finiteControlCount (monomialOccurrences powers)) :
    (FiniteDist.independent (Sum.elim (fun _ : Fin primaryPool => primary.prod body) (fun _ : Fin bodyPool => primary.prod body))).expectation
      (monomialPairedStatistic primary body anchor activation primaryPool bodyPool powers) = 0 := by
  have hi : Nonempty (ControlProductSlot (monomialOccurrences powers)) := Fintype.card_pos_iff.mp horder
  have hs : Nonempty (ControlPrimarySlot (monomialOccurrences powers) ⊕ ControlBodySlot (monomialOccurrences powers)) :=
    hi.elim fun slot => ⟨(controlPoolEquiv (monomialOccurrences powers)).symm slot⟩
  exact CanonicalMoments.twoPoolStatistic_mean_zero (primary.prod body) (primary.prod body) _
    (twoPoolPairedKernel_canonical primary body anchor activation hmass hsupport _ (fun seed hs => hc seed (mem_monomialOccurrences_support powers seed hs))) hs

theorem tablePairedStatistic_mean_zero (primary body : FiniteDist Color)
    (anchor : Color → Color → ℝ) (activation : ℝ)
    (hmass : ∀ color, ∑ center, anchor color center = 1)
    (hsupport : ∀ point center, body.weight center = 0 → anchor point center = 0)
    (primaryPool bodyPool : ℕ) (table : Table (InputSeed Color))
    (hc : InputTableCanonical primary body table)
    (horder : HasOrder (fun seed => seed.primaryOrder + seed.bodyOrder) 1 table) :
    (FiniteDist.independent (Sum.elim (fun _ : Fin primaryPool => primary.prod body) (fun _ : Fin bodyPool => primary.prod body))).expectation
      (tablePairedStatistic primary body anchor activation primaryPool bodyPool table) = 0 := by
  have he (word) : tablePairedStatistic primary body anchor activation primaryPool bodyPool table word =
      ∑ term : table.support, MvPolynomial.coeff term.val table * monomialPairedStatistic primary body anchor activation primaryPool bodyPool term.val word :=
    (Finset.sum_coe_sort table.support (fun powers => MvPolynomial.coeff powers table * monomialPairedStatistic primary body anchor activation primaryPool bodyPool powers word)).symm
  rw [show tablePairedStatistic primary body anchor activation primaryPool bodyPool table = _ from funext he, FiniteDist.expectation_sum]
  simp only [FiniteDist.expectation_const_mul]
  apply Finset.sum_eq_zero
  intro term _
  rw [monomialPairedStatistic_mean_zero primary body anchor activation hmass hsupport primaryPool bodyPool term.val (hc term.val term.property)
    (positive_monomial_order table horder term.val term.property), mul_zero]

end
end AFT.RepresentedPolynomial
