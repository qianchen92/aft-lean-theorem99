import AFT.RepresentedTableMoment

/-! # Exact mean zero of literal positive-order input corrections -/
namespace AFT.CanonicalMoments
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance representedInputMeanSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
variable {PS BS PP BP Color : Type*}
  [Fintype PS] [Fintype BS] [Fintype PP] [Fintype BP] [Fintype Color]

theorem twoPoolStatistic_mean_zero (primary body : FiniteDist Color)
    (kernel : ((PS ⊕ BS) → Color) → ℝ)
    (hc : Hoeffding.Canonical (Sum.elim (fun _ : PS => primary) (fun _ : BS => body)) Finset.univ kernel)
    (hslot : Nonempty (PS ⊕ BS)) :
    (FiniteDist.independent (Sum.elim (fun _ : PP => primary) (fun _ : BP => body))).expectation
      (twoPoolStatistic kernel) = 0 := by
  obtain ⟨slot⟩ := hslot
  have hz (placement : (PS ↪ PP) × (BS ↪ BP)) :
      (FiniteDist.independent (Sum.elim (fun _ : PP => primary) (fun _ : BP => body))).expectation
        (placedKernel kernel (placement.1.sumMap placement.2)) = 0 := by
    have hp := placedKernel_canonical_compatible
      (Sum.elim (fun _ : PP => primary) (fun _ : BP => body))
      (Sum.elim (fun _ : PS => primary) (fun _ : BS => body)) kernel hc
      (placement.1.sumMap placement.2) (by intro index; cases index <;> rfl)
    have he := Hoeffding.orthogonal_of_centered
      (Sum.elim (fun _ : PP => primary) (fun _ : BP => body)) ∅ (placement.1.sumMap placement.2 slot)
      (by simp) (placedKernel kernel (placement.1.sumMap placement.2)) (fun _ => 1)
      (hp.2 _ (Finset.mem_map.mpr ⟨slot, Finset.mem_univ _, rfl⟩)) (by intro _ _ _; rfl)
    simpa only [mul_one] using he
  unfold twoPoolStatistic
  simp only [div_eq_mul_inv]
  rw [FiniteDist.expectation_mul_const, FiniteDist.expectation_sum]
  simp only [hz, Finset.sum_const_zero, zero_mul]

end
end AFT.CanonicalMoments

namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance representedInputMeanTableSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
variable {Color : Type*} [Fintype Color]

theorem monomialInputStatistic_mean_zero (primary body : FiniteDist Color)
    (primaryPool bodyPool : ℕ) (powers : InputSeed Color →₀ ℕ)
    (hc : ∀ seed ∈ powers.support, Hoeffding.Canonical (inputReference primary body seed) Finset.univ seed.kernel)
    (horder : 0 < finiteControlCount (monomialOccurrences powers)) :
    (FiniteDist.independent (Sum.elim (fun _ : Fin primaryPool => primary) (fun _ : Fin bodyPool => body))).expectation
      (monomialInputStatistic primaryPool bodyPool powers) = 0 := by
  have hi : Nonempty (ControlProductSlot (monomialOccurrences powers)) := Fintype.card_pos_iff.mp horder
  have hs : Nonempty (ControlPrimarySlot (monomialOccurrences powers) ⊕ ControlBodySlot (monomialOccurrences powers)) :=
    hi.elim fun slot => ⟨(controlPoolEquiv (monomialOccurrences powers)).symm slot⟩
  exact CanonicalMoments.twoPoolStatistic_mean_zero primary body _
    (twoPoolControlKernel_canonical primary body _ (fun seed hs => hc seed (mem_monomialOccurrences_support powers seed hs))) hs

theorem tableInputStatistic_mean_zero (primary body : FiniteDist Color)
    (primaryPool bodyPool : ℕ) (table : Table (InputSeed Color))
    (hc : InputTableCanonical primary body table)
    (horder : HasOrder (fun seed => seed.primaryOrder + seed.bodyOrder) 1 table) :
    (FiniteDist.independent (Sum.elim (fun _ : Fin primaryPool => primary) (fun _ : Fin bodyPool => body))).expectation
      (tableInputStatistic primaryPool bodyPool table) = 0 := by
  have he (word) : tableInputStatistic primaryPool bodyPool table word =
      ∑ term : table.support, MvPolynomial.coeff term.val table * monomialInputStatistic primaryPool bodyPool term.val word :=
    (Finset.sum_coe_sort table.support (fun powers => MvPolynomial.coeff powers table * monomialInputStatistic primaryPool bodyPool powers word)).symm
  rw [show tableInputStatistic primaryPool bodyPool table = _ from funext he, FiniteDist.expectation_sum]
  simp only [FiniteDist.expectation_const_mul]
  apply Finset.sum_eq_zero
  intro term _
  rw [monomialInputStatistic_mean_zero primary body primaryPool bodyPool term.val (hc term.val term.property)
    (positive_monomial_order table horder term.val term.property), mul_zero]

end
end AFT.RepresentedPolynomial
