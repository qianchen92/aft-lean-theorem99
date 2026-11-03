import AFT.CanonicalPolynomialConstants
import AFT.DependentProductEnergy
import AFT.ChannelCentering

/-! # Old-coordinate centering inside genuinely dependent joint tensors -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Index Output : Type*} [Fintype Index] [DecidableEq Index]
  {Old : Index → Type*} [∀ i, Fintype (Old i)]

/-- The polynomial tensor sum uses its literal basis masses. In particular,
no factorization of the joint kernel is imposed. -/
def dependentPolynomial (forms : ∀ i, Old i → Table Output)
    (kernel : ((i : Index) → Old i) → ℝ) : Table Output :=
  ∑ word, MvPolynomial.C (kernel word) * ∏ i, forms i (word i)

/-- Zero weighted mean in one old coordinate annihilates every expression
which is independent of that coordinate. The other alphabets may differ. -/
theorem dependent_centered_polynomial_zero
    (law : ∀ i, FiniteDist (Old i)) (kernel : ((i : Index) → Old i) → ℝ)
    (slot : Index)
    (hc : ∀ tail : (i : {i // i ≠ slot}) → Old i.val,
      ∑ color, (law slot).weight color *
        kernel ((Equiv.piSplitAt slot Old).symm (color,tail)) = 0)
    (polynomial : ((i : Index) → Old i) → Table Output)
    (hp : ∀ first second, (∀ i, i ≠ slot → first i = second i) →
      polynomial first = polynomial second) :
    (∑ word, MvPolynomial.C ((law slot).weight (word slot) * kernel word) * polynomial word) = 0 := by
  classical
  by_cases hn : Nonempty (Old slot)
  · let color₀ : Old slot := Classical.choice hn
    rw [← (Equiv.piSplitAt slot Old).symm.sum_comp, Fintype.sum_prod_type,
      Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro tail _
    have he (color : Old slot) : polynomial ((Equiv.piSplitAt slot Old).symm (color,tail)) =
        polynomial ((Equiv.piSplitAt slot Old).symm (color₀,tail)) := by
      apply hp
      intro other ho
      simp [Equiv.piSplitAt,ho]
    simp only [he]
    have hv (color : Old slot) : (Equiv.piSplitAt slot Old).symm (color,tail) slot = color := by
      simp [Equiv.piSplitAt]
    simp only [hv]
    rw [← Finset.sum_mul, ← map_sum, hc, map_zero, zero_mul]
  · haveI : IsEmpty (Old slot) := not_nonempty_iff.mp hn
    haveI : IsEmpty ((i : Index) → Old i) := ⟨fun word => isEmptyElim (word slot)⟩
    simp

/-- Insert one local correction proportional to the input reference mass.
Its entire contribution vanishes for a canonical joint input. -/
theorem dependentPolynomial_weighted_constant_at
    (law : ∀ i, FiniteDist (Old i)) (forms : ∀ i, Old i → Table Output)
    (kernel : ((i : Index) → Old i) → ℝ) (slot : Index) (constant : Table Output)
    (hc : ∀ tail : (i : {i // i ≠ slot}) → Old i.val,
      ∑ color, (law slot).weight color *
        kernel ((Equiv.piSplitAt slot Old).symm (color,tail)) = 0) :
    dependentPolynomial (Function.update forms slot
      (fun color => forms slot color + MvPolynomial.C ((law slot).weight color)*constant)) kernel =
      dependentPolynomial forms kernel := by
  classical
  let remaining := fun word : (i : Index) → Old i =>
    ∏ other ∈ Finset.univ.erase slot, forms other (word other)
  have hz := dependent_centered_polynomial_zero law kernel slot hc remaining (by
    intro first second h
    apply Finset.prod_congr rfl
    intro other ho
    rw [h other (Finset.mem_erase.mp ho).1])
  have hu (word : (i : Index) → Old i) :
      (fun other => Function.update forms slot
        (fun color => forms slot color + MvPolynomial.C ((law slot).weight color)*constant) other (word other)) =
      Function.update (fun other => forms other (word other)) slot
        (forms slot (word slot)+MvPolynomial.C ((law slot).weight (word slot))*constant) := by
    funext other
    by_cases ho : other=slot
    · subst other; simp
    · simp [Function.update_of_ne ho]
  have he : dependentPolynomial (Function.update forms slot
      (fun color => forms slot color + MvPolynomial.C ((law slot).weight color)*constant)) kernel =
      dependentPolynomial forms kernel + constant *
        (∑ word, MvPolynomial.C ((law slot).weight (word slot)*kernel word)*remaining word) := by
    unfold dependentPolynomial
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro word _
    rw [hu,Finset.prod_update_of_mem (Finset.mem_univ slot),
      ← Finset.mul_prod_erase Finset.univ (fun other => forms other (word other)) (Finset.mem_univ slot)]
    simp only [Finset.sdiff_singleton_eq_erase,map_mul]
    dsimp only [remaining]
    ring
  rw [he,hz,mul_zero,add_zero]

/-- Simultaneous old-coordinate centering cancels on an arbitrary joint
canonical kernel. Only the selected groups need to be centered. -/
theorem dependentPolynomial_sub_weighted_constants
    (law : ∀ i, FiniteDist (Old i)) (forms : ∀ i, Old i → Table Output)
    (constants : Index → Table Output) (kernel : ((i : Index) → Old i) → ℝ)
    (selected : Finset Index)
    (hc : ∀ slot ∈ selected, ∀ tail : (i : {i // i ≠ slot}) → Old i.val,
      ∑ color, (law slot).weight color *
        kernel ((Equiv.piSplitAt slot Old).symm (color,tail)) = 0) :
    dependentPolynomial (fun slot color => forms slot color -
      if slot ∈ selected then MvPolynomial.C ((law slot).weight color)*constants slot else 0) kernel =
      dependentPolynomial forms kernel := by
  classical
  induction selected using Finset.induction_on with
  | empty => simp only [Finset.notMem_empty,if_false,sub_zero]
  | @insert slot selected hs ih =>
    let previous : ∀ i, Old i → Table Output := fun other color => forms other color -
      if other ∈ selected then MvPolynomial.C ((law other).weight color)*constants other else 0
    have he : (fun other color => forms other color -
        if other ∈ insert slot selected then MvPolynomial.C ((law other).weight color)*constants other else 0) =
        Function.update previous slot
          (fun color => previous slot color+MvPolynomial.C ((law slot).weight color)*(-constants slot)) := by
      funext other color
      by_cases ho : other=slot
      · subst other; simp [previous,hs,sub_eq_add_neg]
      · simp [previous,ho]
    rw [he,dependentPolynomial_weighted_constant_at law previous kernel slot (-constants slot)
      (hc slot (Finset.mem_insert_self _ _))]
    exact ih (fun other ho => hc other (Finset.mem_insert_of_mem ho))

omit [Fintype Index] in
/-- The usual canonicality condition on coordinate updates implies the
split-coordinate form used by the dependent tensor identity. -/
theorem dependent_centered_tail_of_update
    (law : ∀ i, FiniteDist (Old i)) (kernel : ((i : Index) → Old i) → ℝ)
    (slot : Index)
    (hc : ∀ word, ∑ color, (law slot).weight color *
      kernel (Function.update word slot color) = 0)
    (tail : (i : {i // i ≠ slot}) → Old i.val) :
    ∑ color, (law slot).weight color *
      kernel ((Equiv.piSplitAt slot Old).symm (color,tail)) = 0 := by
  classical
  by_cases hn : Nonempty (Old slot)
  · let color₀ : Old slot := Classical.choice hn
    have he (color : Old slot) :
        Function.update ((Equiv.piSplitAt slot Old).symm (color₀,tail)) slot color =
          (Equiv.piSplitAt slot Old).symm (color,tail) := by
      funext other
      by_cases ho : other=slot
      · subst other; simp [Equiv.piSplitAt]
      · simp [Equiv.piSplitAt,ho]
    simpa only [he] using hc ((Equiv.piSplitAt slot Old).symm (color₀,tail))
  · haveI : IsEmpty (Old slot) := not_nonempty_iff.mp hn
    simp

/-- Root coordinates stay coupled through the single function `rootKernel`.
Only old-coordinate means are removed, and background groups outside
`selected` are left intact. Every group may have its own input alphabet. -/
theorem dependent_root_old_centering
    {Root Input : Index → Type*} [∀ i,Fintype (Root i)] [∀ i,Fintype (Input i)]
    (equiv : ∀ i, Input i ≃ Root i × Old i)
    (law : ∀ i, FiniteDist (Old i))
    (forms : ∀ i, Root i → Old i → Table Output)
    (constants : ∀ i, Root i → Table Output)
    (rootKernel : ((i : Index) → Root i) → ℝ)
    (oldKernel : ((i : Index) → Old i) → ℝ)
    (selected : Finset Index)
    (hc : ∀ slot ∈ selected, ∀ word, ∑ color, (law slot).weight color *
      oldKernel (Function.update word slot color) = 0) :
    (∑ input : (i : Index) → Input i,
      MvPolynomial.C (rootKernel (fun i => (equiv i (input i)).1) *
        oldKernel (fun i => (equiv i (input i)).2)) *
      ∏ i, (forms i (equiv i (input i)).1 (equiv i (input i)).2 -
        if i ∈ selected then MvPolynomial.C ((law i).weight (equiv i (input i)).2) *
          constants i (equiv i (input i)).1 else 0)) =
    ∑ input : (i : Index) → Input i,
      MvPolynomial.C (rootKernel (fun i => (equiv i (input i)).1) *
        oldKernel (fun i => (equiv i (input i)).2)) *
      ∏ i, forms i (equiv i (input i)).1 (equiv i (input i)).2 := by
  classical
  rw [← (Equiv.piCongrRight equiv).symm.sum_comp, ← (Equiv.piCongrRight equiv).symm.sum_comp]
  simp only [Equiv.piCongrRight_symm_apply,Pi.map_apply,Equiv.apply_symm_apply]
  rw [← (FiniteDist.dependentPairsEquiv (Root:=Root) (Old:=Old)).symm.sum_comp,
    ← (FiniteDist.dependentPairsEquiv (Root:=Root) (Old:=Old)).symm.sum_comp,
    Fintype.sum_prod_type,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro roots _
  change (∑ old, MvPolynomial.C (rootKernel roots * oldKernel old) *
    ∏ i, (forms i (roots i) (old i) - if i ∈ selected then
      MvPolynomial.C ((law i).weight (old i)) * constants i (roots i) else 0)) =
    ∑ old, MvPolynomial.C (rootKernel roots * oldKernel old) * ∏ i, forms i (roots i) (old i)
  simp only [map_mul,mul_assoc,← Finset.mul_sum]
  congr 1
  exact dependentPolynomial_sub_weighted_constants law
    (fun i => forms i (roots i)) (fun i => constants i (roots i)) oldKernel selected
      (fun i hi => dependent_centered_tail_of_update law oldKernel i (hc i hi))

end
end AFT.RepresentedPolynomial

namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
variable {Root Old Output : Type*} [Fintype Old]
def conditionalOldCenter (law : FiniteDist Old) (kernel : Root × Old → ℝ) (point : Root × Old) : ℝ :=
  TensorChannel.center law (fun color => kernel (point.1,color)) point.2

theorem conditionalOldCenter_single [rootOldDecEq : DecidableEq (Root × Old)] (law : FiniteDist Old) (root : Root) (old : Old) :
    conditionalOldCenter law (Pi.single (root,old) (1 : ℝ)) =
      Pi.single (root,old) (1 : ℝ) - law.weight old • (∑ color : Old, (Pi.single (root,color) (1 : ℝ) : Root × Old → ℝ)) := by
  classical
  funext point
  obtain ⟨r,c⟩ := point
  by_cases hr : r=root
  · subst r
    simp [conditionalOldCenter,FiniteDist.expectation,Pi.single_apply,Prod.mk.injEq,eq_comm]
  · simp [conditionalOldCenter,FiniteDist.expectation,Prod.mk.injEq,hr]

theorem polynomial_conditionalOldCenter_single [rootOldDecEq : DecidableEq (Root × Old)] (law : FiniteDist Old)
    (channel : (Root × Old → ℝ) →ₗ[ℝ] Table Output) (root : Root) (old : Old) :
    channel (conditionalOldCenter law (Pi.single (root,old) (1 : ℝ))) =
      channel (Pi.single (root,old) (1 : ℝ)) - MvPolynomial.C (law.weight old) *
        ∑ color : Old, channel (Pi.single (root,color) (1 : ℝ)) := by
  rw [conditionalOldCenter_single,map_sub,map_smul,map_sum]
  rw [Algebra.smul_def,MvPolynomial.algebraMap_eq]
/-- Any linear local polynomial response may be centered on its old input
before tensoring: the resulting complete joint polynomial is unchanged. -/
theorem dependent_root_old_channels
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    {Roots Inputs : Index → Type*} [∀ i,Fintype (Roots i)] [∀ i,Fintype (Inputs i)]
    (law : ∀ i, FiniteDist (Inputs i))
    (channel : ∀ i, (Roots i × Inputs i → ℝ) →ₗ[ℝ] Table Output)
    (rootKernel : ((i : Index) → Roots i) → ℝ)
    (oldKernel : ((i : Index) → Inputs i) → ℝ)
    (selected : Finset Index)
    (hc : ∀ slot ∈ selected, ∀ word, ∑ color, (law slot).weight color *
      oldKernel (Function.update word slot color) = 0) :
    (∑ input : (i : Index) → Roots i × Inputs i,
      MvPolynomial.C (rootKernel (fun i => (input i).1) * oldKernel (fun i => (input i).2)) *
        ∏ i, channel i (if i ∈ selected then
          conditionalOldCenter (law i) (Pi.single (input i) 1) else Pi.single (input i) 1)) =
    ∑ input : (i : Index) → Roots i × Inputs i,
      MvPolynomial.C (rootKernel (fun i => (input i).1) * oldKernel (fun i => (input i).2)) *
        ∏ i, channel i (Pi.single (input i) 1) := by
  classical
  have hpoint (i : Index) (point : Roots i × Inputs i) :
      channel i (if i ∈ selected then conditionalOldCenter (law i) (Pi.single point 1)
        else Pi.single point 1) =
      channel i (Pi.single point 1) - if i ∈ selected then
        MvPolynomial.C ((law i).weight point.2) * ∑ color, channel i (Pi.single (point.1,color) 1) else 0 := by
    by_cases hi : i ∈ selected
    · simp only [hi,if_true]
      exact polynomial_conditionalOldCenter_single (law i) (channel i) point.1 point.2
    · simp only [hi,if_false,sub_zero]
  simp_rw [hpoint]
  exact dependent_root_old_centering (fun _ => Equiv.refl _) law
    (fun i root color => channel i (Pi.single (root,color) 1))
    (fun i root => ∑ color, channel i (Pi.single (root,color) 1)) rootKernel oldKernel selected hc

end
end AFT.RepresentedPolynomial
