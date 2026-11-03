import Mathlib

/-! # Exact enumeration of all coordinate frequencies by their actual support -/

namespace CurrentAFT.FrequencySupport

open scoped BigOperators Classical

noncomputable section

variable {Index : Type*} [Fintype Index] {modulus : ℕ}

abbrev NonzeroFrequency (modulus : ℕ) := {frequency : ZMod modulus // frequency ≠ 0}

def support (frequency : Index → ZMod modulus) : Finset Index :=
  Finset.univ.filter (fun index => frequency index ≠ 0)

def extend (selected : Finset Index) (frequency : selected → ZMod modulus) : Index → ZMod modulus :=
  fun index => if h : index ∈ selected then frequency ⟨index, h⟩ else 0

def packed (selected : Finset Index) (frequency : selected → NonzeroFrequency modulus) : Index → ZMod modulus :=
  extend selected (fun index => (frequency index).val)

omit [Fintype Index] in
theorem packed_apply (selected : Finset Index) (frequency : selected → NonzeroFrequency modulus)
    (index : selected) : packed selected frequency index = (frequency index).val := by
  unfold packed extend
  split_ifs with h
  · rfl
  · exact False.elim (h index.property)

theorem support_packed (selected : Finset Index) (frequency : selected → NonzeroFrequency modulus) :
    support (packed selected frequency) = selected := by
  ext index
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hindex : index ∈ selected
  · simp only [packed, extend, dif_pos hindex]
    exact iff_of_true (frequency ⟨index, hindex⟩).property hindex
  · simp only [packed, extend, dif_neg hindex, ne_eq, not_true_eq_false]
    exact iff_of_false id hindex

theorem packed_injective : Function.Injective
    (fun point : Sigma (fun selected : Finset Index => selected → NonzeroFrequency modulus) => packed point.1 point.2) := by
  rintro ⟨first, firstWord⟩ ⟨second, secondWord⟩ hequal
  have hselected : first = second := by
    have h := congrArg support hequal
    simpa only [support_packed] using h
  subst second
  congr 1
  funext index
  apply Subtype.ext
  have h := congrFun hequal index.val
  simpa only [packed_apply] using h

theorem packed_surjective : Function.Surjective
    (fun point : Sigma (fun selected : Finset Index => selected → NonzeroFrequency modulus) => packed point.1 point.2) := by
  intro frequency
  let word : support frequency → NonzeroFrequency modulus :=
    fun index => ⟨frequency index.val, (Finset.mem_filter.mp index.property).2⟩
  refine ⟨⟨support frequency, word⟩, ?_⟩
  funext index
  by_cases hzero : frequency index = 0
  · have hnot : index ∉ support frequency := by simp [support, hzero]
    simp only [packed, extend, dif_neg hnot, hzero]
  · have hmem : index ∈ support frequency := by simp [support, hzero]
    simp only [packed, extend, dif_pos hmem, word]

/-- Every full frequency has one support and one nonzero word on that
support. No frequency of high or full support is discarded. -/
def encodingEquiv :
    Sigma (fun selected : Finset Index => selected → NonzeroFrequency modulus) ≃ (Index → ZMod modulus) :=
  Equiv.ofBijective (fun point => packed point.1 point.2) ⟨packed_injective, packed_surjective⟩

variable [NeZero modulus]

theorem sum_by_support {Value : Type*} [AddCommMonoid Value]
    (test : (Index → ZMod modulus) → Value) :
    (∑ frequency : Index → ZMod modulus, test frequency) =
      ∑ selected : Finset Index, ∑ word : selected → NonzeroFrequency modulus, test (packed selected word) := by
  have h := (encodingEquiv (Index := Index) (modulus := modulus)).sum_comp test
  simpa only [Fintype.sum_sigma, encodingEquiv, Equiv.ofBijective_apply] using h.symm

theorem sum_exact_support {Value : Type*} [AddCommMonoid Value]
    (degree : ℕ) (test : (Index → ZMod modulus) → Value) :
    (∑ frequency : Index → ZMod modulus, if (support frequency).card = degree then test frequency else 0) =
      ∑ selected ∈ Finset.univ.powersetCard degree,
        ∑ word : selected → NonzeroFrequency modulus, test (packed selected word) := by
  rw [sum_by_support]
  simp_rw [support_packed]
  simp_rw [Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [← Finset.sum_filter]
  have hsets : (Finset.univ.filter fun selected : Finset Index => selected.card = degree) =
      Finset.univ.powersetCard degree := by ext selected; simp
  rw [hsets]

end

end CurrentAFT.FrequencySupport
