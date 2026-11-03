import CurrentAFT.RationalFamilyProductProgram
import AFT.RationalHeight

/-! # Explicit size and magnitude bounds for coefficient-table multiplication -/
namespace CurrentAFT.RationalFamilyProductProgram
open AFT RationalNumerics GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def homogeneousHeight (order bits : ℕ) : ℕ :=
  2 * order.factorial + order.factorial * (order.factorial * (2 * bits + 1) + 1)

def productHeight (order bits : ℕ) : ℕ :=
  (order + 1)^2 * ((order + 1)^2 * (homogeneousHeight order bits + 1) + 1)

noncomputable section
open scoped Classical

theorem arity_card_bound (order : ℕ) : Fintype.card (TruncatedArity order) ≤ (order+1)^2 := by
  simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using
    Fintype.card_subtype_le (fun arity : Fin (order+1) × Fin (order+1) => arity.1.val + arity.2.val ≤ order)

theorem product_bound {Primary Body : Type*} (order : ℕ)
    (first second : Table ℝ Primary Body order) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ arity colors centers, |first arity colors centers| ≤ A)
    (hb : ∀ arity colors centers, |second arity colors centers| ≤ B)
    (output : TruncatedArity order) (colors : Fin output.val.1.val → Primary)
    (centers : Fin output.val.2.val → Body) :
    |product order first second output colors centers| ≤
      (Fintype.card (TruncatedArity order) : ℝ)^2 * (A*B) := by
  unfold product
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _left : TruncatedArity order, ∑ _right : TruncatedArity order, (A*B) := by
      apply Finset.sum_le_sum
      intro left _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro right _
      split_ifs with hmatch
      · exact homogeneous_bound _ _ A B hA hB (ha left) (hb right) _ _
      · simpa only [abs_zero] using mul_nonneg hA hB
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem average_height (r s bits : ℕ)
    (value : Equiv.Perm (Fin r) → Equiv.Perm (Fin s) → ℚ)
    (hvalue : ∀ first second, HeightBound (value first second) bits) :
    HeightBound (average r s value)
      (r.factorial + s.factorial + r.factorial * (s.factorial * (bits+1) + 1)) := by
  have hs (first : Equiv.Perm (Fin r)) := HeightBound.sum Finset.univ (value first) bits
    (fun second _ => hvalue first second)
  simp only [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at hs
  have hp := HeightBound.sum Finset.univ (fun first => ∑ second, value first second)
    (s.factorial * (bits+1)) (fun first _ => hs first)
  simp only [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at hp
  exact ((HeightBound.nat_coarse r.factorial).inv.mul (HeightBound.nat_coarse s.factorial).inv).mul hp

theorem homogeneous_height {Primary Body : Type*} {r s r' s' : ℕ}
    (first : Kernel ℚ Primary Body r s) (second : Kernel ℚ Primary Body r' s')
    (order bits : ℕ) (hr : r+r' ≤ order) (hs : s+s' ≤ order)
    (ha : ∀ colors centers, HeightBound (first colors centers) bits)
    (hb : ∀ colors centers, HeightBound (second colors centers) bits)
    (colors : Fin (r+r') → Primary) (centers : Fin (s+s') → Body) :
    HeightBound (homogeneous first second colors centers) (homogeneousHeight order bits) := by
  have h := average_height (r+r') (s+s') (2*bits)
    (fun p b => tensor first second (colors ∘ p) (centers ∘ b))
    (fun p b => ((ha _ _).mul (hb _ _)).mono (by omega))
  apply h.mono
  have hrf := Nat.factorial_le hr
  have hsf := Nat.factorial_le hs
  unfold homogeneousHeight
  calc
    _ ≤ order.factorial + order.factorial +
        order.factorial * (order.factorial * (2 * bits + 1) + 1) := by gcongr
    _ = _ := by omega

theorem product_height {Primary Body : Type*} (order bits : ℕ)
    (first second : Table ℚ Primary Body order)
    (ha : ∀ arity colors centers, HeightBound (first arity colors centers) bits)
    (hb : ∀ arity colors centers, HeightBound (second arity colors centers) bits)
    (output : TruncatedArity order) (colors : Fin output.val.1.val → Primary)
    (centers : Fin output.val.2.val → Body) :
    HeightBound (product order first second output colors centers) (productHeight order bits) := by
  unfold product
  have hterm (left right : TruncatedArity order) : HeightBound
      (if hmatch : left.val.1.val + right.val.1.val = output.val.1.val ∧
          left.val.2.val + right.val.2.val = output.val.2.val then
        homogeneous (first left) (second right) (colors ∘ finCongr hmatch.1) (centers ∘ finCongr hmatch.2)
      else 0) (homogeneousHeight order bits) := by
    split_ifs with hmatch
    · have ho := output.property
      exact homogeneous_height _ _ order bits (by omega) (by omega) (ha left) (hb right) _ _
    · exact HeightBound.zero.mono (Nat.zero_le _)
  have hinner (left : TruncatedArity order) := HeightBound.sum Finset.univ _
    (homogeneousHeight order bits) (fun right _ => hterm left right)
  have hout := HeightBound.sum Finset.univ _
    (Fintype.card (TruncatedArity order) * (homogeneousHeight order bits + 1))
    (fun left _ => by simpa only [Finset.card_univ] using hinner left)
  simp only [Finset.card_univ] at hout
  apply hout.mono
  unfold productHeight
  gcongr <;> exact arity_card_bound order

end
end CurrentAFT.RationalFamilyProductProgram
