import CurrentAFT.CurrentPermutationDraw

/-! The two stored directions represent precisely one finite permutation. -/
namespace CurrentAFT.CurrentPermutationDraw

private theorem vector_ofFn_get {count : ℕ} (data : Vector (Fin count) count) :
    Vector.ofFn data.get = data := by
  apply Vector.ext
  intro index hindex
  change (Vector.ofFn data.get).get ⟨index, hindex⟩ = data.get ⟨index, hindex⟩
  exact Vector.get_ofFn _ _

def cachedEquiv (count : ℕ) : CachedPermutation count ≃ Equiv.Perm (Fin count) where
  toFun := CachedPermutation.toEquiv
  invFun permutation := ⟨Vector.ofFn permutation, Vector.ofFn permutation.symm,
    fun index => by simp only [Vector.get_ofFn, Equiv.symm_apply_apply],
    fun index => by simp only [Vector.get_ofFn, Equiv.apply_symm_apply]⟩
  left_inv cached := by
    cases cached with
    | mk forward inverse left right =>
      change CachedPermutation.mk (Vector.ofFn forward.get) (Vector.ofFn inverse.get) _ _ = _
      congr 1 <;> exact vector_ofFn_get _
  right_inv permutation := by
    apply Equiv.ext
    intro index
    exact Vector.get_ofFn _ _

noncomputable instance cachedPermutationFintype (count : ℕ) : Fintype (CachedPermutation count) :=
  Fintype.ofEquiv (Equiv.Perm (Fin count)) (cachedEquiv count).symm

end CurrentAFT.CurrentPermutationDraw
