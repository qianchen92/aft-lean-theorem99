import CurrentAFT.BinaryFirstInverseResources

/-! # A binary-key lookup by a charged complete palette scan -/
namespace CurrentAFT.BinaryPaletteLookup
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalCounter signedEqual

def term {count : ℕ} (table : Vector RationalBits count) (key : List Bool) (color : Fin count) : RationalResult :=
  let code := canonicalCounter color.val
  let matched := signedEqual false false code.digits key
  let atom := readVector zero table color
  ⟨if matched.value then atom.value else zero, code.work+matched.work+atom.work+3⟩

theorem term_value {count : ℕ} (table : Vector RationalBits count) (key : List Bool) (color : Fin count) :
    (term table key color).data.decode = if color.val=value key then (table.get color).decode else 0 := by
  have hm : (signedEqual false false (canonicalCounter color.val).digits key).value = true ↔ color.val=value key := by
    rw [signedEqual_value]
    simp only [signedValue, Bool.false_eq_true, if_false, canonicalCounter_value, Nat.cast_inj]
  unfold term
  dsimp only
  simp only [hm]
  split_ifs
  · exact congrArg RationalBits.decode (readVector_value zero table color)
  · exact zero_value

def current {count : ℕ} (table : Vector RationalBits count) (key : List Bool) : RationalResult := sumFin count (term table key)

theorem current_value {count : ℕ} (table : Vector RationalBits count) (key : List Bool) (color : Fin count)
    (hkey : value key=color.val) :
    (current table key).data.decode = (table.get color).decode := by
  rw [current, sumFin_value]
  simp only [term_value, hkey, ← Fin.ext_iff]
  simp

def termWork (count keyBits : ℕ) : ℕ := 50*(count+1)^2+48*(count+keyBits)+42+3*count+3
def work (count keyBits bits : ℕ) : ℕ :=
  count*(termWork count keyBits+primitiveWorkBound ((count+1)*(bits+1))+2)+2

theorem term_height {count : ℕ} (table : Vector RationalBits count) (key : List Bool) (bits : ℕ)
    (ht : ∀ color, HeightBound (table.get color).decode bits) (color : Fin count) :
    HeightBound (term table key color).data.decode bits := by
  rw [term_value]
  split_ifs
  · exact ht color
  · exact HeightBound.zero.mono (Nat.zero_le _)

theorem term_work {count : ℕ} (table : Vector RationalBits count) (key : List Bool) (keyBits : ℕ)
    (hk : key.length ≤ keyBits) (color : Fin count) :
    (term table key color).work ≤ termWork count keyBits := by
  have hl : (canonicalCounter color.val).digits.length ≤ count := by
    rw [canonicalCounter_length]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n := color.val))).trans color.isLt.le
  have wc := (canonicalCounter_work color.val).trans
    (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right color.isLt.le 1) 2))
  have wm := signedEqual_work false false (canonicalCounter color.val).digits key
  have wa := readVector_work zero table color
  change _+_+_+3 ≤ _
  unfold termWork
  omega

theorem current_bounds {count : ℕ} (table : Vector RationalBits count) (key : List Bool) (keyBits bits : ℕ)
    (hk : key.length ≤ keyBits) (ht : ∀ color, HeightBound (table.get color).decode bits) :
    HeightBound (current table key).data.decode (count*(bits+1)) ∧
      (current table key).work ≤ work count keyBits bits :=
  ⟨sumFin_height count bits (term table key) (term_height table key bits ht),
    sumFin_work count bits (termWork count keyBits) (term table key)
      (term_height table key bits ht) (term_work table key keyBits hk)⟩

end CurrentAFT.BinaryPaletteLookup
