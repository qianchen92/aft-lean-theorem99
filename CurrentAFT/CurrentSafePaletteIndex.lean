import CurrentAFT.ActualControls
import CurrentAFT.ProposalCenter
import AFT.BinaryChartMetadata

/-! Native interval coordinates for the actual safe body alphabet. -/
namespace CurrentAFT.CurrentSafePaletteIndex

open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 500000

abbrev count (security : ℕ) := Parameters.modulus security - 2 * Parameters.safeMargin security

theorem count_positive (security : ℕ) : 0 < count security := by
  have h := ProposalPrimary.safe_clearance security
  change 0 < Parameters.modulus security - 2 * Parameters.safeMargin security
  omega

def equiv (security : ℕ) : Fin (count security) ≃ ActualControls.SafePalette security where
  toFun index := ⟨⟨Parameters.safeMargin security + index.val, by
      have h := index.isLt
      have hc := ProposalPrimary.safe_clearance security
      dsimp only [count] at h
      omega⟩, by
    unfold InwardAnchor.SafeColor
    change (Parameters.safeMargin security : ℤ) ≤ ((Parameters.safeMargin security + index.val : ℕ) : ℤ) ∧
      ((Parameters.safeMargin security + index.val : ℕ) : ℤ) < (Parameters.modulus security : ℤ) - Parameters.safeMargin security
    have h := index.isLt
    have hc := ProposalPrimary.safe_clearance security
    dsimp only [count] at h
    constructor <;> omega⟩
  invFun color := ⟨color.val.val - Parameters.safeMargin security, by
    have h := color.property
    unfold InwardAnchor.SafeColor at h
    have hc := ProposalPrimary.safe_clearance security
    dsimp only [count]
    omega⟩
  left_inv index := by apply Fin.ext; dsimp; omega
  right_inv color := by
    apply Subtype.ext
    apply Fin.ext
    have h := color.property.1
    dsimp only
    omega

@[simp] theorem equiv_value (security : ℕ) (index : Fin (count security)) :
    ((equiv security index).val).val = Parameters.safeMargin security + index.val := rfl

/-- An executed offset addition; the equivalence itself is only its specification. -/
def embed (security : ℕ) (index : Fin (count security)) : CountedValue (ActualControls.SafePalette security) :=
  let added := addCounter (Parameters.safeMargin security) index.val
  have he : added.count = Parameters.safeMargin security + index.val := addCounter_value _ _
  ⟨⟨⟨added.count, by rw [he]; exact (equiv security index).val.isLt⟩, by
      simpa only [he] using (equiv security index).property⟩, added.work + 2⟩

theorem embed_value (security : ℕ) (index : Fin (count security)) :
    (embed security index).value = equiv security index := by
  apply Subtype.ext
  apply Fin.ext
  exact addCounter_value _ _

theorem embed_work (security : ℕ) (index : Fin (count security)) :
    (embed security index).work = 2 * Parameters.safeMargin security + 3 := by
  simp only [embed, addCounter_work]

noncomputable section
open scoped Classical

instance safeNonempty (security : ℕ) : Nonempty (Fin (count security)) :=
  ⟨⟨0, count_positive security⟩⟩

def uniformLaw (security : ℕ) : FiniteDist (ActualControls.SafePalette security) :=
  (FiniteDist.uniform (Fin (count security))).map (equiv security)

theorem uniformLaw_weight (security : ℕ) (color : ActualControls.SafePalette security) :
    (uniformLaw security).weight color = ((count security : ℕ) : ℝ)⁻¹ := by
  simp only [uniformLaw, FiniteDist.map_equiv_weight, FiniteDist.uniform_weight, Fintype.card_fin]

theorem uniformLaw_full (security : ℕ) :
    (uniformLaw security).map Subtype.val = ProposalPrimary.safeLaw security := by
  letI : DecidableEq (Fin (Parameters.modulus security)) := Classical.decEq _
  ext color
  rw [FiniteDist.map_weight, ProposalPrimary.safeLaw_weight]
  by_cases hsafe : InwardAnchor.SafeColor security color
  · rw [if_pos hsafe]
    have heq (source : ActualControls.SafePalette security) : source.val = color ↔ source = ⟨color, hsafe⟩ :=
      ⟨fun hh => Subtype.ext hh, fun hh => congrArg Subtype.val hh⟩
    change (∑ source : ActualControls.SafePalette security,
      if source.val = color then (uniformLaw security).weight source else 0) = _
    simp_rw [heq]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _), uniformLaw_weight]
    unfold ProposalPrimary.safeHeight
    have hc := ProposalPrimary.safe_clearance security
    have he : ((count security : ℕ) : ℝ) = (Parameters.modulus security : ℝ) -
        2 * Parameters.safeMargin security := by
      rw [count, Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat]
    rw [he, one_div]
  · rw [if_neg hsafe]
    apply Finset.sum_eq_zero
    intro source _
    have hv : source.val ≠ color := by
      intro he
      exact hsafe (he ▸ source.property)
    simp only [if_neg hv]

end
end CurrentAFT.CurrentSafePaletteIndex
