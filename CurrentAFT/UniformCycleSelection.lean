import CurrentAFT.CycleSelections
import CurrentAFT.ProtectedCycleResponse

/-! # Exact uniform permutation restriction to distinct labeled sites -/

namespace CurrentAFT.CycleSelections

open AFT
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {Selected Pool : Type*} [Fintype Selected] [Fintype Pool] [DecidableEq Pool]

local instance : DecidableEq (Selected ↪ Pool) := Classical.decEq _

/-- Postcomposition is a genuine permutation of the complete embedding type. -/
def embeddingAction (permutation : Equiv.Perm Pool) : (Selected ↪ Pool) ≃ (Selected ↪ Pool) where
  toFun sites := sites.trans permutation.toEmbedding
  invFun sites := sites.trans permutation.symm.toEmbedding
  left_inv sites := by ext slot; exact permutation.symm_apply_apply _
  right_inv sites := by ext slot; exact permutation.apply_symm_apply _

/-- Every pair of ordered distinct selections is related by a whole-pool
permutation. The complement is completed by an actual finite equivalence. -/
def selectionPermutation (first second : Selected ↪ Pool) : Equiv.Perm Pool :=
  (first.toEquivRange.symm.trans second.toEquivRange).extendSubtype

theorem selectionPermutation_apply (first second : Selected ↪ Pool) (slot : Selected) :
    selectionPermutation first second (first slot) = second slot := by
  rw [selectionPermutation, Equiv.extendSubtype_apply_of_mem _ _ ⟨slot, rfl⟩]
  change second (first.toEquivRange.symm ⟨first slot, ⟨slot, rfl⟩⟩) = second slot
  congr 1
  exact first.toEquivRange.symm_apply_apply slot

/-- A whole-pool uniform permutation sends every fixed distinct selection
to the literal uniform law on ordered embeddings. -/
theorem uniform_permutation_selection (labels : Selected ↪ Pool) :
    (FiniteDist.uniform (Equiv.Perm Pool)).map
      (fun permutation => labels.trans permutation.toEmbedding) =
        @FiniteDist.uniform (Selected ↪ Pool) _ ⟨labels⟩ := by
  letI : Nonempty (Selected ↪ Pool) := ⟨labels⟩
  let law := (FiniteDist.uniform (Equiv.Perm Pool)).map
    (fun permutation => labels.trans permutation.toEmbedding)
  have hconstant (first second : Selected ↪ Pool) : law.weight first = law.weight second := by
    let swap := selectionPermutation first second
    have hfirst : first.trans swap.toEmbedding = second := by
      ext slot
      exact selectionPermutation_apply first second slot
    have h := Equiv.sum_comp (Equiv.mulLeft swap)
      (fun permutation : Equiv.Perm Pool =>
        if labels.trans permutation.toEmbedding = second then
          (FiniteDist.uniform (Equiv.Perm Pool)).weight permutation else 0)
    dsimp only [law]
    simp only [FiniteDist.map_weight]
    apply Eq.trans _ h
    apply Finset.sum_congr rfl
    intro permutation _
    have hequal : labels.trans (swap * permutation).toEmbedding = second ↔
        labels.trans permutation.toEmbedding = first := by
      constructor
      · intro he
        apply (embeddingAction swap).injective
        change (labels.trans permutation.toEmbedding).trans swap.toEmbedding = first.trans swap.toEmbedding
        rw [hfirst]
        exact he
      · intro he
        change (labels.trans permutation.toEmbedding).trans swap.toEmbedding = second
        rw [he, hfirst]
    simp only [Equiv.coe_mulLeft, hequal, FiniteDist.uniform_weight]
  ext output
  change law.weight output = _
  have hsum : (Fintype.card (Selected ↪ Pool) : ℝ) * law.weight output = 1 := by
    have h := law.sum_one
    have hfixed : ∀ sites, law.weight sites = law.weight output := fun sites => hconstant sites output
    simpa only [hfixed, Finset.sum_const, nsmul_eq_mul, Finset.card_univ] using h
  have hcard : (0 : ℝ) < Fintype.card (Selected ↪ Pool) := by exact_mod_cast Fintype.card_pos
  rw [FiniteDist.uniform_weight]
  apply (mul_left_cancel₀ hcard.ne')
  rw [hsum]
  field_simp

/-- Inverse permutations have the same uniform restriction law, matching
the manuscript's endpoint relabeling convention. -/
theorem uniform_inverse_permutation_selection (labels : Selected ↪ Pool) :
    (FiniteDist.uniform (Equiv.Perm Pool)).map
      (fun permutation => labels.trans permutation.symm.toEmbedding) =
        @FiniteDist.uniform (Selected ↪ Pool) _ ⟨labels⟩ := by
  have huniform := FiniteDist.uniform_map_equiv (Equiv.inv (Equiv.Perm Pool))
  rw [← huniform, FiniteDist.map_map]
  exact uniform_permutation_selection labels

/-- Specialization to the actual finite-body selection law. -/
theorem body_permutation_selection (body order : ℕ) (horder : order ≤ body)
    (labels : Selection body order) :
    (FiniteDist.uniform (Equiv.Perm (Fin body))).map
      (fun permutation => labels.trans permutation.symm.toEmbedding) =
        selectionLaw body order horder := by
  unfold selectionLaw
  exact uniform_inverse_permutation_selection labels

/-- The literal uniform whole-body permutation experiment, restricted to
fixed labeled output positions, is the actual selected-root mixture. -/
theorem uniform_permuted_selectedLaw {Scalar : Type*} [Fintype Scalar]
    (body order modulus : ℕ) [NeZero modulus] (horder : order ≤ body)
    (source : FiniteDist Scalar) (value : Scalar → ZMod modulus) (labels : Selection body order) :
    (FiniteDist.uniform (Equiv.Perm (Fin body))).mix
      (fun permutation => (ProtectedCycle.relabeledCycleLaw body modulus source value permutation).map
        (fun root slot => root (labels slot))) =
      averagedSelectedLaw body order modulus horder source value := by
  have hchannel (permutation : Equiv.Perm (Fin body)) :
      (ProtectedCycle.relabeledCycleLaw body modulus source value permutation).map
        (fun root slot => root (labels slot)) =
          selectedLaw body order modulus source value (labels.trans permutation.symm.toEmbedding) := by
    unfold ProtectedCycle.relabeledCycleLaw selectedLaw
    rw [FiniteDist.map_map]
    rfl
  simp_rw [hchannel]
  unfold averagedSelectedLaw
  rw [← body_permutation_selection body order horder labels, FiniteDist.mix_map]

end

end CurrentAFT.CycleSelections
