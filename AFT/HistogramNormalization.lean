import AFT.BlockProducts

/-! # Exact finite histogram normalization of actual symmetric coefficients -/

namespace AFT
namespace HistogramNormalization

open scoped BigOperators Classical

variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]

/-- Exchangeability of an actual signed output mass. -/
def ExchangeableMass (mass : (Slot → Color) → ℝ) : Prop :=
  ∀ word (permutation : Equiv.Perm Slot), mass (word ∘ permutation) = mass word

/-- Reindex the complete finite word space by a position permutation. -/
def precomposeEquiv (permutation : Equiv.Perm Slot) : (Slot → Color) ≃ (Slot → Color) where
  toFun word := word ∘ permutation
  invFun word := word ∘ permutation.symm
  left_inv word := by ext slot; simp
  right_inv word := by ext slot; simp

set_option backward.isDefEq.respectTransparency false in
/-- Exchangeability transports every genuine selected coefficient through
any bijection of its selected output positions. -/
theorem localTensor_equiv (reference : FiniteDist Color) (mass : (Slot → Color) → ℝ)
    (hexchangeable : ExchangeableMass mass) (first second : Finset Slot)
    (equiv : first ≃ second) (word : second → Color) :
    LocalTensors.localTensor (fun _ : Slot => reference) mass first (word ∘ equiv) =
      LocalTensors.localTensor (fun _ : Slot => reference) mass second word := by
  let permutation : Equiv.Perm Slot := equiv.extendSubtype
  rw [LocalTensors.localTensor_formula, LocalTensors.localTensor_formula]
  have h := (precomposeEquiv (Color := Color) permutation).sum_comp
    (fun input => mass input * ∏ slot : first,
      LocalTensors.atomCoefficient reference (input slot) (word (equiv slot)))
  calc
    _ = ∑ input : Slot → Color, mass (input ∘ permutation) * ∏ slot : first,
        LocalTensors.atomCoefficient reference ((input ∘ permutation) slot) (word (equiv slot)) := h.symm
    _ = _ := by
      apply Finset.sum_congr (by ext; simp)
      intro input _
      rw [hexchangeable input permutation]
      congr 1
      have hperm (slot : first) : permutation slot = equiv slot :=
        equiv.extendSubtype_apply_of_mem slot slot.property
      simp only [Function.comp_apply, hperm]
      exact equiv.prod_comp (fun slot => LocalTensors.atomCoefficient reference (input slot) (word slot))

set_option backward.isDefEq.respectTransparency false in
/-- Equal-size subsets give exactly the same reindexed coefficient under
exchangeability, before any norm estimate is applied. -/
theorem degreePiece_eq (reference : FiniteDist Color) (mass : (Slot → Color) → ℝ)
    (hexchangeable : ExchangeableMass mass) (degree : ℕ) (first second : Finset Slot)
    (hfirst : Fintype.card first = degree) (hsecond : Fintype.card second = degree)
    (word : Fin degree → Color) :
    LocalTensors.degreePiece (fun _ : Slot => reference) mass degree first word =
      LocalTensors.degreePiece (fun _ : Slot => reference) mass degree second word := by
  simp only [LocalTensors.degreePiece, dif_pos hfirst, dif_pos hsecond]
  let ef := Fintype.equivFinOfCardEq hfirst
  let es := Fintype.equivFinOfCardEq hsecond
  have h := localTensor_equiv reference mass hexchangeable first second (ef.trans es.symm) (word ∘ es)
  simpa only [Function.comp_def, Equiv.trans_apply, Equiv.apply_symm_apply] using h

set_option backward.isDefEq.respectTransparency false in
/-- A selected coefficient of an exchangeable law is already symmetric in
its own arguments. -/
theorem degreePiece_symmetric (reference : FiniteDist Color) (mass : (Slot → Color) → ℝ)
    (hexchangeable : ExchangeableMass mass) (degree : ℕ) (selected : Finset Slot)
    (word : Fin degree → Color) (permutation : Equiv.Perm (Fin degree)) :
    LocalTensors.degreePiece (fun _ : Slot => reference) mass degree selected (word ∘ permutation) =
      LocalTensors.degreePiece (fun _ : Slot => reference) mass degree selected word := by
  by_cases hdegree : Fintype.card selected = degree
  · simp only [LocalTensors.degreePiece, dif_pos hdegree]
    let equiv := Fintype.equivFinOfCardEq hdegree
    have h := localTensor_equiv reference mass hexchangeable selected selected
      ((equiv.trans permutation).trans equiv.symm) (word ∘ equiv)
    simpa only [Function.comp_def, Equiv.trans_apply, Equiv.apply_symm_apply] using h
  · simp only [LocalTensors.degreePiece, dif_neg hdegree]

omit [Fintype Color] in
/-- Symmetrizing an already symmetric actual tensor has no effect. -/
theorem symmetrize_eq_of_symmetric (tensor : BlockFock.Tensor Slot Color)
    (hsymmetric : ∀ word (permutation : Equiv.Perm Slot), tensor (word ∘ permutation) = tensor word) :
    BlockFock.symmetrize tensor = tensor := by
  funext word
  simp only [BlockFock.symmetrize, hsymmetric, ← Finset.sum_mul, FiniteDist.sum_one, one_mul]

set_option backward.isDefEq.respectTransparency false in
/-- Each degree tensor of an exchangeable signed law is the number of
same-size position subsets times the one common genuine coefficient. -/
theorem degreeTensor_eq_choose (reference : FiniteDist Color) (mass : (Slot → Color) → ℝ)
    (hexchangeable : ExchangeableMass mass) (degree : ℕ) (selected : Finset Slot)
    (hselected : Fintype.card selected = degree) (word : Fin degree → Color) :
    LocalTensors.degreeTensor (fun _ : Slot => reference) mass degree word =
      ((Fintype.card Slot).choose degree : ℝ) *
        LocalTensors.degreePiece (fun _ : Slot => reference) mass degree selected word := by
  unfold LocalTensors.degreeTensor
  rw [symmetrize_eq_of_symmetric _ (by
    intro word permutation
    apply Finset.sum_congr rfl
    intro subset _
    exact degreePiece_symmetric reference mass hexchangeable degree subset word permutation)]
  have hpoint (subset : Finset Slot) :
      LocalTensors.degreePiece (fun _ : Slot => reference) mass degree subset word =
        if subset.card = degree then
          LocalTensors.degreePiece (fun _ : Slot => reference) mass degree selected word else 0 := by
    by_cases hcard : subset.card = degree
    · rw [if_pos hcard]
      exact degreePiece_eq reference mass hexchangeable degree subset selected
        (by simpa only [Fintype.card_coe] using hcard) hselected word
    · have hc : ¬ Fintype.card subset = degree := by simpa only [Fintype.card_coe] using hcard
      simp only [LocalTensors.degreePiece, dif_neg hc, if_neg hcard]
  trans ∑ subset : Finset Slot, if subset.card = degree then
    LocalTensors.degreePiece (fun _ : Slot => reference) mass degree selected word else 0
  · exact Finset.sum_congr rfl (fun subset _ => hpoint subset)
  rw [← Finset.sum_filter]
  have hsets : (Finset.univ.filter fun subset : Finset Slot => subset.card = degree) =
      Finset.univ.powersetCard degree := by
    ext subset
    simp
  rw [hsets]
  simp only [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, nsmul_eq_mul]

set_option backward.isDefEq.respectTransparency false in
/-- The exact common selected-coefficient energy, after reindexing. -/
theorem degreePiece_energy (reference : FiniteDist Color) (mass : (Slot → Color) → ℝ)
    (degree : ℕ) (selected : Finset Slot) (hselected : Fintype.card selected = degree) :
    BlockFock.tensorEnergy (LocalTensors.degreePiece (fun _ : Slot => reference) mass degree selected) =
      BlockFock.tensorEnergy (LocalTensors.localTensor (fun _ : Slot => reference) mass selected) := by
  simp only [LocalTensors.degreePiece, dif_pos hselected]
  exact LocalTensors.tensorEnergy_reindex _ _

set_option backward.isDefEq.respectTransparency false in
/-- Exact finite-population normalization of every degree of an exchangeable
signed likelihood, including degrees near the population size. -/
theorem degree_energy_identity (reference : FiniteDist Color) (mass : (Slot → Color) → ℝ)
    (hexchangeable : ExchangeableMass mass) (degree : ℕ) (hdegree : degree ≤ Fintype.card Slot) :
    (∑ selected ∈ Finset.univ.powersetCard degree,
      (FiniteDist.independent (fun _ : Slot => reference)).l2Sq
        (Hoeffding.densityComponent (fun _ : Slot => reference) mass selected)) =
      (degree.factorial : ℝ) * BlockFock.tensorEnergy
        (LocalTensors.degreeTensor (fun _ : Slot => reference) mass degree) /
          ((Fintype.card Slot).descFactorial degree : ℝ) := by
  obtain ⟨selected, hselectedMem⟩ := Finset.powersetCard_nonempty.mpr
    (show degree ≤ (Finset.univ : Finset Slot).card by simpa using hdegree)
  have hselected : Fintype.card selected = degree := by
    simpa only [Fintype.card_coe] using (Finset.mem_powersetCard_univ.mp hselectedMem)
  have hpiece (subset : Finset Slot) (hsubset : subset ∈ Finset.univ.powersetCard degree) :
      (FiniteDist.independent (fun _ : Slot => reference)).l2Sq
          (Hoeffding.densityComponent (fun _ : Slot => reference) mass subset) =
        BlockFock.tensorEnergy (LocalTensors.degreePiece (fun _ : Slot => reference) mass degree selected) := by
    rw [← LocalTensors.localTensor_energy_eq]
    have hcard : Fintype.card subset = degree := by
      simpa only [Fintype.card_coe] using (Finset.mem_powersetCard_univ.mp hsubset)
    rw [← degreePiece_energy reference mass degree subset hcard]
    congr 1
    funext word
    exact degreePiece_eq reference mass hexchangeable degree subset selected hcard hselected word
  rw [Finset.sum_congr rfl hpiece]
  simp only [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, nsmul_eq_mul]
  have hcoeff : LocalTensors.degreeTensor (fun _ : Slot => reference) mass degree =
      (fun word => ((Fintype.card Slot).choose degree : ℝ) *
        LocalTensors.degreePiece (fun _ : Slot => reference) mass degree selected word) :=
    funext (degreeTensor_eq_choose reference mass hexchangeable degree selected hselected)
  rw [hcoeff, TensorFock.tensorEnergy_smul, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  have hfactorial : (degree.factorial : ℝ) ≠ 0 := by exact_mod_cast degree.factorial_ne_zero
  have hchoose : ((Fintype.card Slot).choose degree : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hdegree).ne'
  field_simp

/-- The actual finite Hoeffding tail of a signed labeled likelihood. -/
noncomputable def densityTail (reference : FiniteDist Color) (mass : (Slot → Color) → ℝ)
    (cutoff : ℕ) (word : Slot → Color) : ℝ :=
  ∑ selected ∈ Finset.univ.filter (fun selected : Finset Slot => cutoff < selected.card),
    Hoeffding.densityComponent (fun _ : Slot => reference) mass selected word

set_option backward.isDefEq.respectTransparency false in
/-- The complete actual tail norm equals the descending-factorial energy of
its constructed coefficients. This is an exact finite identity. -/
theorem densityTail_energy (reference : FiniteDist Color)
    (hreference : ∀ color, 0 < reference.weight color)
    (mass : (Slot → Color) → ℝ) (hexchangeable : ExchangeableMass mass) (cutoff : ℕ) :
    (FiniteDist.independent (fun _ : Slot => reference)).l2Sq (densityTail reference mass cutoff) =
      HistogramTail.likelihoodTailEnergy (Fintype.card Slot) cutoff
        (fun degree => BlockFock.tensorEnergy
          (LocalTensors.degreeTensor (fun _ : Slot => reference) mass degree)) := by
  unfold densityTail
  rw [Hoeffding.canonical_sum_l2Sq _ _ _
    (fun selected _ => Hoeffding.densityComponent_canonical _ (fun _ color => hreference color) mass selected)]
  have hgroup := Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ.filter (fun selected : Finset Slot => cutoff < selected.card))
    (t := (Finset.range (Fintype.card Slot + 1)).filter (cutoff < ·))
    (g := fun selected : Finset Slot => selected.card) (by
      intro selected hselected
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hselected
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_univ _)), hselected⟩)
    (fun selected => (FiniteDist.independent (fun _ : Slot => reference)).l2Sq
      (Hoeffding.densityComponent (fun _ : Slot => reference) mass selected))
  rw [← hgroup]
  unfold HistogramTail.likelihoodTailEnergy
  apply Finset.sum_congr rfl
  intro degree hdegree
  obtain ⟨hrange, hcutoff⟩ := Finset.mem_filter.mp hdegree
  have hsets : ((Finset.univ.filter fun selected : Finset Slot => cutoff < selected.card).filter
      fun selected => selected.card = degree) = Finset.univ.powersetCard degree := by
    ext selected
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard_univ]
    constructor
    · exact And.right
    · intro h; exact ⟨by simpa only [h] using hcutoff, h⟩
  rw [hsets]
  exact degree_energy_identity reference mass hexchangeable degree
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hrange))

end HistogramNormalization
end AFT
