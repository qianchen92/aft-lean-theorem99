import AFT.BinaryPhysicalBaseline
import AFT.BinaryChartMetadata
import AFT.UnaryPolynomialCounters

/-! Executed entries of the actual path-plus-two-leg incidence loads.
The edge order is body, first leg edges, second leg edges, then the shared
queue column. Every indicator is an actual counter comparison. -/
namespace CurrentAFT.CurrentBinaryIncidence
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
set_option maxHeartbeats 700000
set_option maxRecDepth 4096


private theorem decode_ite (condition : Prop) [Decidable condition] (first second : IntegerBits) :
    (if condition then first else second).decode = if condition then first.decode else second.decode := by
  split_ifs <;> rfl


def pathEntry (bodyEdges column root : ℕ) : CountedValue IntegerBits :=
  let inside := lessCounter column bodyEdges
  let positive := equalCounter root column
  let next := addCounter column 1
  let negative := equalCounter root next.count
  let difference := IntegerBits.subtract (if positive.value then IntegerBits.one else IntegerBits.zero)
    (if negative.value then IntegerBits.one else IntegerBits.zero)
  ⟨if inside.value then difference.value else IntegerBits.zero,
    inside.work + positive.work + next.work + negative.work + difference.work + 5⟩

 theorem pathEntry_value (bodyEdges column root : ℕ) :
    (pathEntry bodyEdges column root).value.decode = if column < bodyEdges then
      (if root = column then 1 else 0) - (if root = column + 1 then 1 else 0) else 0 := by
  have hi : (lessCounter column bodyEdges).value = true ↔ column < bodyEdges := lessCounter_value _ _
  have hp : (equalCounter root column).value = true ↔ root = column := equalCounter_value _ _
  have hn : (equalCounter root (addCounter column 1).count).value = true ↔ root = column + 1 := by
    rw [equalCounter_value, addCounter_value]
  simp only [pathEntry, decode_ite, IntegerBits.subtract_value, IntegerBits.one_value, IntegerBits.zero_value, hi, hp, hn]

 theorem pathEntry_length (bodyEdges column root : ℕ) : (pathEntry bodyEdges column root).value.digits.length ≤ 2 := by
  have hi : (if (equalCounter root column).value then IntegerBits.one else IntegerBits.zero).digits.length ≤ 1 := by
    split_ifs <;> decide
  have hj : (if (equalCounter root (addCounter column 1).count).value then IntegerBits.one else IntegerBits.zero).digits.length ≤ 1 := by
    split_ifs <;> decide
  have h := IntegerBits.subtract_length
    (if (equalCounter root column).value then IntegerBits.one else IntegerBits.zero)
    (if (equalCounter root (addCounter column 1).count).value then IntegerBits.one else IntegerBits.zero)
  have hmax := max_le hi hj
  by_cases inside : (lessCounter column bodyEdges).value = true
  · simp only [pathEntry, if_pos inside]
    exact h.trans (by omega)
  · simp only [pathEntry, if_neg inside]
    decide

def pathEntryWork (bodyEdges column root : ℕ) : ℕ :=
  3 * (column + bodyEdges) + 3 * (root + column) + 2 * column + 3 * (root + column + 1) + 100

 theorem pathEntry_work (bodyEdges column root : ℕ) :
    (pathEntry bodyEdges column root).work ≤ pathEntryWork bodyEdges column root := by
  have hi := lessCounter_work column bodyEdges
  have hp := equalCounter_work root column
  have hn := equalCounter_work root (addCounter column 1).count
  have hd := IntegerBits.subtract_work
    (if (equalCounter root column).value then IntegerBits.one else IntegerBits.zero)
    (if (equalCounter root (addCounter column 1).count).value then IntegerBits.one else IntegerBits.zero)
  have hfirst : (if (equalCounter root column).value then IntegerBits.one else IntegerBits.zero).digits.length ≤ 1 := by
    split_ifs <;> decide
  have hsecond : (if (equalCounter root (addCounter column 1).count).value then IntegerBits.one else IntegerBits.zero).digits.length ≤ 1 := by
    split_ifs <;> decide
  simp only [addCounter_value] at hn hd hfirst hsecond
  simp only [pathEntry, addCounter_work, addCounter_value, pathEntryWork]
  omega


def legEntries {legs : ℕ} (bodyEdges column : ℕ) (scale shear : Vector IntegerBits legs) (leg : Fin legs) :
    CountedValue (IntegerBits × (IntegerBits × IntegerBits)) :=
  let firstAddress := addCounter bodyEdges leg.val
  let secondAddress := addCounter firstAddress.count legs
  let firstHit := equalCounter column firstAddress.count
  let secondHit := equalCounter column secondAddress.count
  let scaleEntry := readVector IntegerBits.zero scale leg
  let shearEntry := readVector IntegerBits.zero shear leg
  let primary := IntegerBits.add (if firstHit.value then scaleEntry.value else IntegerBits.zero)
    (if secondHit.value then shearEntry.value else IntegerBits.zero)
  let second := if secondHit.value then IntegerBits.one else IntegerBits.zero
  let negative := IntegerBits.negate primary.value
  let companion := IntegerBits.subtract negative.value second
  ⟨(primary.value, (companion.value, second)), firstAddress.work + secondAddress.work + firstHit.work + secondHit.work +
    scaleEntry.work + shearEntry.work + primary.work + negative.work + companion.work + 7⟩

 theorem legEntries_value {legs : ℕ} (bodyEdges column : ℕ) (scale shear : Vector IntegerBits legs) (leg : Fin legs) :
    let first := (if column = bodyEdges + leg.val then (scale.get leg).decode else 0) +
      (if column = bodyEdges + leg.val + legs then (shear.get leg).decode else 0)
    let second := if column = bodyEdges + leg.val + legs then (1 : ℤ) else 0
    ((legEntries bodyEdges column scale shear leg).value.1.decode,
      ((legEntries bodyEdges column scale shear leg).value.2.1.decode,
        (legEntries bodyEdges column scale shear leg).value.2.2.decode)) = (first, (-first - second, second)) := by
  have hf : (equalCounter column (addCounter bodyEdges leg.val).count).value = true ↔ column = bodyEdges + leg.val := by
    rw [equalCounter_value, addCounter_value]
  have hs : (equalCounter column (addCounter (addCounter bodyEdges leg.val).count legs).count).value = true ↔
      column = bodyEdges + leg.val + legs := by
    rw [equalCounter_value, addCounter_value, addCounter_value]
  simp only [legEntries, decode_ite, IntegerBits.add_value, IntegerBits.subtract_value, IntegerBits.negate_value, readVector_value, hf, hs, IntegerBits.zero_value, IntegerBits.one_value]


 theorem legEntries_length {legs : ℕ} (bodyEdges column bits : ℕ) (scale shear : Vector IntegerBits legs) (leg : Fin legs)
    (hscale : (scale.get leg).digits.length ≤ bits) (hshear : (shear.get leg).digits.length ≤ bits) :
    (legEntries bodyEdges column scale shear leg).value.1.digits.length ≤ bits + 1 ∧
    (legEntries bodyEdges column scale shear leg).value.2.1.digits.length ≤ bits + 2 ∧
    (legEntries bodyEdges column scale shear leg).value.2.2.digits.length ≤ 1 := by
  let firstHit := (equalCounter column (addCounter bodyEdges leg.val).count).value
  let secondHit := (equalCounter column (addCounter (addCounter bodyEdges leg.val).count legs).count).value
  let first := if firstHit then scale.get leg else IntegerBits.zero
  let second := if secondHit then shear.get leg else IntegerBits.zero
  let indicator := if secondHit then IntegerBits.one else IntegerBits.zero
  have hf : first.digits.length ≤ bits := by dsimp only [first]; split_ifs; exact hscale; exact Nat.zero_le _
  have hs : second.digits.length ≤ bits := by dsimp only [second]; split_ifs; exact hshear; exact Nat.zero_le _
  have hi : indicator.digits.length ≤ 1 := by dsimp only [indicator]; split_ifs <;> decide
  have hp := IntegerBits.add_length first second
  have hc := IntegerBits.subtract_length (IntegerBits.negate (IntegerBits.add first second).value).value indicator
  rw [IntegerBits.negate_length] at hc
  have hprimary : (IntegerBits.add first second).value.digits.length ≤ bits + 1 := hp.trans (by omega)
  simp only [legEntries, readVector_value]
  change (IntegerBits.add first second).value.digits.length ≤ bits + 1 ∧
    (IntegerBits.subtract (IntegerBits.negate (IntegerBits.add first second).value).value indicator).value.digits.length ≤ bits + 2 ∧
    indicator.digits.length ≤ 1
  exact ⟨hprimary, by omega, hi⟩

 def legEntriesWork (bodyEdges column legs bits : ℕ) : ℕ :=
   10 * bodyEdges + 20 * legs + 6 * column + 40 * bits + 100

 theorem legEntries_work {legs : ℕ} (bodyEdges column bits : ℕ) (scale shear : Vector IntegerBits legs) (leg : Fin legs)
    (hscale : (scale.get leg).digits.length ≤ bits) (hshear : (shear.get leg).digits.length ≤ bits) :
    (legEntries bodyEdges column scale shear leg).work ≤ legEntriesWork bodyEdges column legs bits := by
  let firstAddress := addCounter bodyEdges leg.val
  let secondAddress := addCounter firstAddress.count legs
  let firstHit := (equalCounter column firstAddress.count).value
  let secondHit := (equalCounter column secondAddress.count).value
  let first := if firstHit then scale.get leg else IntegerBits.zero
  let second := if secondHit then shear.get leg else IntegerBits.zero
  let indicator := if secondHit then IntegerBits.one else IntegerBits.zero
  have hf : first.digits.length ≤ bits := by dsimp only [first]; split_ifs; exact hscale; exact Nat.zero_le _
  have hs : second.digits.length ≤ bits := by dsimp only [second]; split_ifs; exact hshear; exact Nat.zero_le _
  have hi : indicator.digits.length ≤ 1 := by dsimp only [indicator]; split_ifs <;> decide
  have hp := IntegerBits.add_length first second
  have hprimary : (IntegerBits.add first second).value.digits.length ≤ bits + 1 := hp.trans (by omega)
  have wa := IntegerBits.add_work first second
  have wc := IntegerBits.subtract_work (IntegerBits.negate (IntegerBits.add first second).value).value indicator
  rw [IntegerBits.negate_length] at wc
  have wfirst := equalCounter_work column firstAddress.count
  have wsecond := equalCounter_work column secondAddress.count
  have wrscale := readVector_work IntegerBits.zero scale leg
  have wrshear := readVector_work IntegerBits.zero shear leg
  have hleg := leg.isLt
  simp only [legEntries, readVector_value, IntegerBits.negate_work]
  change firstAddress.work + secondAddress.work + (equalCounter column firstAddress.count).work +
    (equalCounter column secondAddress.count).work + (readVector IntegerBits.zero scale leg).work +
    (readVector IntegerBits.zero shear leg).work + (IntegerBits.add first second).work + 2 +
    (IntegerBits.subtract (IntegerBits.negate (IntegerBits.add first second).value).value indicator).work + 7 ≤ _
  have wf : firstAddress.work = 2 * bodyEdges + 1 := addCounter_work _ _
  have ws : secondAddress.work = 2 * (bodyEdges + leg.val) + 1 := by
    rw [show secondAddress.work = 2 * firstAddress.count + 1 from addCounter_work _ _, addCounter_value]
  have va : firstAddress.count = bodyEdges + leg.val := addCounter_value _ _
  have vb : secondAddress.count = bodyEdges + leg.val + legs := by
    rw [show secondAddress.count = firstAddress.count + legs from addCounter_value _ _, va]
  unfold legEntriesWork
  omega

end CurrentAFT.CurrentBinaryIncidence
