import AFT.BinaryFiniteDraw
import AFT.FiniteTicketSampler
import AFT.BinaryLoopControl

/-! Literal ticket sampling from a stored certified rational probability array. -/

namespace CurrentAFT.CurrentProbabilityArrayDraw

open AFT AFT.RationalNumerics AFT.BinaryArithmetic AFT.RationalRejectionProgram
open AFT.BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 400000

structure ProbabilityArray (count : ℕ) where
  data : Vector RationalBits count
  nonneg : ∀ index, 0 ≤ (data.get index).decode
  mass : ∑ index, (data.get index).decode = 1

def draw (count : ℕ) (table : ProbabilityArray (count + 1)) (bits : ℕ)
    (word : Fin (bits + (count + 1) + 1) → Fin 2) : CountedValue (Fin (count + 1)) :=
  let guard := addCounter bits (count + 1)
  have heq : guard.count + 1 = bits + (count + 1) + 1 := by rw [addCounter_value]
  let selected := binaryRationalDraw table.data (guard.count + 1) (fun index => word (index.cast heq))
  have hi : selected.value < count + 1 := by
    dsimp only [selected]
    rw [binaryRationalDraw_cast _ _ _ heq, binaryRationalDraw_value table.data table.nonneg table.mass]
    exact Fin.isLt _
  ⟨⟨selected.value, hi⟩, guard.work + selected.work + 3⟩

theorem draw_value (count : ℕ) (table : ProbabilityArray (count + 1)) (bits : ℕ)
    (word : Fin (bits + (count + 1) + 1) → Fin 2) :
    (draw count table bits word).value = RationalFiniteQuantization.draw (fun index => (table.data.get index).decode)
      table.nonneg table.mass (bits + (count + 1) + 1) word := by
  apply Fin.ext
  simp only [draw, binaryRationalDraw_cast]
  exact binaryRationalDraw_value table.data table.nonneg table.mass _ _

def workBound (count height bits : ℕ) : ℕ :=
  (2 * bits + 1) + binaryRationalDrawWork count height (bits + count + 1) + 3

theorem draw_work (count : ℕ) (table : ProbabilityArray (count + 1)) (height bits : ℕ)
    (hh : ∀ index, HeightBound (table.data.get index).decode height)
    (word : Fin (bits + (count + 1) + 1) → Fin 2) :
    (draw count table bits word).work ≤ workBound (count + 1) height bits := by
  have hs := binaryRationalDraw_work table.data height (bits + (count + 1) + 1) hh word
  simp only [draw, binaryRationalDraw_cast, addCounter_work, workBound]
  omega

/-- Cardinal-sized wrapper, with positivity used only to exclude an empty table. -/
def positiveDraw : (count : ℕ) → (hpositive : 0 < count) → (table : ProbabilityArray count) → (bits : ℕ) →
    (Fin (bits + count + 1) → Fin 2) → CountedValue (Fin count)
  | 0, hpositive, _, _, _ => False.elim (by omega)
  | count + 1, _, table, bits, word => draw count table bits word

theorem positiveDraw_work (count : ℕ) (hpositive : 0 < count) (table : ProbabilityArray count)
    (height bits : ℕ) (hh : ∀ index, HeightBound (table.data.get index).decode height)
    (word : Fin (bits + count + 1) → Fin 2) :
    (positiveDraw count hpositive table bits word).work ≤ workBound count height bits := by
  cases count with
  | zero => omega
  | succ count => exact draw_work count table height bits hh word

noncomputable section
open scoped Classical

def law {count : ℕ} (table : ProbabilityArray count) : FiniteDist (Fin count) where
  weight index := (table.data.get index).decode
  nonneg index := by exact_mod_cast table.nonneg index
  sum_one := by exact_mod_cast table.mass

theorem draw_law (count : ℕ) (table : ProbabilityArray (count + 1)) (bits : ℕ) :
    (FiniteDist.uniform (Fin (bits + (count + 1) + 1) → Fin 2)).map (fun word => (draw count table bits word).value) =
      RationalFiniteQuantization.roundedLaw (fun index => (table.data.get index).decode) table.nonneg table.mass
        (2 ^ (bits + (count + 1) + 1)) (by positivity) := by
  simp only [draw_value]
  rw [← FiniteTicketSampler.independent_fair_bits_uniform]
  exact RationalFiniteQuantization.draw_law _ _ _ _

theorem draw_l1 (count : ℕ) (table : ProbabilityArray (count + 1)) (bits : ℕ) :
    (∑ index, |((FiniteDist.uniform (Fin (bits + (count + 1) + 1) → Fin 2)).map
      (fun word => (draw count table bits word).value)).weight index - (law table).weight index|) ≤ 1 / (2 : ℝ) ^ bits := by
  rw [draw_law]
  have h := RationalFiniteQuantization.roundedLaw_l1_le (fun index => (table.data.get index).decode)
    table.nonneg table.mass (2 ^ (bits + (count + 1) + 1)) (by positivity)
  apply h.trans
  have hc : ((count + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (count + 1) := by exact_mod_cast (Nat.lt_two_pow_self (n := count + 1)).le
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  calc
    2 * (count + 1) / (2 : ℝ) ^ (bits + (count + 1) + 1) ≤ 2 * (2 : ℝ) ^ (count + 1) / (2 : ℝ) ^ (bits + (count + 1) + 1) := by
      gcongr
      simpa only [Nat.cast_add, Nat.cast_one] using hc
    _ = 1 / (2 : ℝ) ^ bits := by rw [pow_add, pow_add]; field_simp; ring


theorem positiveDraw_l1 (count : ℕ) (hpositive : 0 < count) (table : ProbabilityArray count) (bits : ℕ) :
    (∑ index, |((FiniteDist.uniform (Fin (bits + count + 1) → Fin 2)).map
      (fun word => (positiveDraw count hpositive table bits word).value)).weight index - (law table).weight index|) ≤
      1 / (2 : ℝ) ^ bits := by
  cases count with
  | zero => omega
  | succ count => exact draw_l1 count table bits

end
end CurrentAFT.CurrentProbabilityArrayDraw
