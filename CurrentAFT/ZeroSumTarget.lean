import AFT.FiniteProbability

/-!
# The actual zero-sum endpoint target

For a nonzero modulus and a positive number of endpoint coordinates, uniform
ambient colors have zero total charge with probability exactly `1 / q`.
Conditioning this law gives the uniform zero-sum hyperplane law. These are
finite counting statements; no independence or cardinality estimate for the
calibrated construction is assumed.
-/

namespace CurrentAFT

open AFT
open scoped BigOperators Classical

noncomputable section

/-- The ambient endpoint space has `dimension + 1` coordinates. -/
abbrev EndpointSpace (dimension modulus : ℕ) := Fin (dimension + 1) → ZMod modulus

/-- The zero-sum endpoint hyperplane as a subtype of the ambient space. -/
abbrev ZeroSumSpace (dimension modulus : ℕ) :=
  {endpoint : EndpointSpace dimension modulus // ∑ index, endpoint index = 0}

instance zeroSumSpaceNonempty (dimension modulus : ℕ) :
    Nonempty (ZeroSumSpace dimension modulus) :=
  ⟨⟨fun _ => 0, by simp⟩⟩

/-- Every tail has exactly one zero-charge extension: its first coordinate is
the negative sum of that tail. -/
def zeroSumTailEquiv (dimension modulus : ℕ) :
    ZeroSumSpace dimension modulus ≃ (Fin dimension → ZMod modulus) where
  toFun endpoint index := endpoint.val index.succ
  invFun tail := ⟨Fin.cons (-∑ index, tail index) tail, by simp [Fin.sum_univ_succ]⟩
  left_inv endpoint := by
    apply Subtype.ext
    funext index
    refine Fin.cases ?_ (fun _ => rfl) index
    change -(∑ index : Fin dimension, endpoint.val index.succ) = endpoint.val 0
    have hsum := endpoint.property
    rw [Fin.sum_univ_succ] at hsum
    exact (eq_neg_of_add_eq_zero_left hsum).symm
  right_inv tail := rfl

theorem zeroSumSpace_card (dimension modulus : ℕ) [NeZero modulus] :
    Fintype.card (ZeroSumSpace dimension modulus) = modulus ^ dimension := by
  simpa only [Fintype.card_fun, Fintype.card_fin, ZMod.card] using
    Fintype.card_congr (zeroSumTailEquiv dimension modulus)

theorem endpointSpace_card (dimension modulus : ℕ) [NeZero modulus] :
    Fintype.card (EndpointSpace dimension modulus) = modulus ^ (dimension + 1) := by
  simp only [EndpointSpace, Fintype.card_fun, Fintype.card_fin, ZMod.card]

/-- Uniform on the actual hyperplane, viewed as a law in the ambient space. -/
def uniformZeroSum (dimension modulus : ℕ) [NeZero modulus] :
    FiniteDist (EndpointSpace dimension modulus) :=
  (FiniteDist.uniform (ZeroSumSpace dimension modulus)).map Subtype.val

theorem uniformZeroSum_weight (dimension modulus : ℕ) [NeZero modulus]
    (endpoint : EndpointSpace dimension modulus) :
    (uniformZeroSum dimension modulus).weight endpoint =
      if (∑ index, endpoint index) = 0 then ((modulus : ℝ) ^ dimension)⁻¹ else 0 := by
  by_cases hcharge : (∑ index, endpoint index) = 0
  · let target : ZeroSumSpace dimension modulus := ⟨endpoint, hcharge⟩
    have heq (source : ZeroSumSpace dimension modulus) :
        source.val = endpoint ↔ source = target := by
      constructor
      · intro heq
        exact Subtype.ext heq
      · intro heq
        exact congrArg Subtype.val heq
    simp [uniformZeroSum, FiniteDist.map_weight, heq, FiniteDist.uniform_weight,
      zeroSumSpace_card, hcharge]
  · have hne (source : ZeroSumSpace dimension modulus) : source.val ≠ endpoint := by
      intro heq
      apply hcharge
      rw [← heq]
      exact source.property
    simp [uniformZeroSum, FiniteDist.map_weight, hne, hcharge]

/-- The ambient uniform law assigns the zero-sum event exactly `1 / modulus`.
The proof counts the event using the explicit extension equivalence above. -/
theorem uniform_zeroSum_mass (dimension modulus : ℕ) [NeZero modulus] :
    (∑ endpoint : EndpointSpace dimension modulus,
      if (∑ index, endpoint index) = 0 then
        (FiniteDist.uniform (EndpointSpace dimension modulus)).weight endpoint else 0) =
      1 / (modulus : ℝ) := by
  simp only [FiniteDist.uniform_weight]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hcount : (Finset.univ.filter
      (fun endpoint : EndpointSpace dimension modulus => (∑ index, endpoint index) = 0)).card =
      modulus ^ dimension := by
    rw [← Fintype.card_subtype]
    exact zeroSumSpace_card dimension modulus
  rw [hcount, endpointSpace_card]
  have hmodulus : (modulus : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne modulus)
  simp only [Nat.cast_pow, pow_succ]
  field_simp
  push_cast
  rfl

/-- Pointwise identification of the conditional ambient uniform law with the
inclusion pushforward of the uniform hyperplane law. The denominator has
already been computed, rather than supplied as an assumption. -/
theorem uniformZeroSum_eq_conditional_weight (dimension modulus : ℕ) [NeZero modulus]
    (endpoint : EndpointSpace dimension modulus) :
    (uniformZeroSum dimension modulus).weight endpoint =
      (if (∑ index, endpoint index) = 0 then
        (FiniteDist.uniform (EndpointSpace dimension modulus)).weight endpoint else 0) /
        (1 / (modulus : ℝ)) := by
  rw [uniformZeroSum_weight]
  by_cases hcharge : (∑ index, endpoint index) = 0
  · simp only [hcharge, if_true, FiniteDist.uniform_weight, endpointSpace_card, pow_succ]
    have hmodulus : (modulus : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne modulus)
    field_simp
    push_cast
    rfl
  · simp [hcharge]

end

end CurrentAFT
