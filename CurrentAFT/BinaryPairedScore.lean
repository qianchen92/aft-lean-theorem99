import AFT.BinaryChartIteration

/-! # Binary evaluation of a paired score from stored reference tables

Every reference and score lookup is a sequential array read. The returned
rational is formed by binary arithmetic, with explicit height and work
bounds. Reference-table construction is accounted for separately.
-/
namespace CurrentAFT.BinaryPairedScore
open AFT AFT.RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1800000

def term {count : ℕ} (primary score : Vector RationalBits count)
    (anchor : Vector (Vector RationalBits count) count) (center color : Fin count) : RationalResult :=
  let p := readVector zero primary color
  let f := readVector zero score color
  let a := matrixEntry anchor color center
  let product := multiply p.value f.value
  let result := multiply product.data a.value
  ⟨result.data, p.work + f.work + a.work + product.work + result.work + 2⟩

theorem term_value {count : ℕ} (primary score : Vector RationalBits count)
    (anchor : Vector (Vector RationalBits count) count) (center color : Fin count) :
    (term primary score anchor center color).data.decode =
      (primary.get color).decode * (score.get color).decode * ((anchor.get color).get center).decode := by
  simp only [term, RationalBits.multiply_value, readVector_value, matrixEntry_value]

def current {count : ℕ} (primary centerLaw score : Vector RationalBits count)
    (anchor : Vector (Vector RationalBits count) count) (rate : RationalBits)
    (input center : Fin count) : RationalResult :=
  let profile := sumFin count (term primary score anchor center)
  let first := readVector zero score input
  let body := readVector zero centerLaw center
  let reciprocal := inverse body.value
  let activated := multiply rate profile.data
  let correction := multiply activated.data reciprocal.data
  let negative := negate correction.data
  let result := add first.value negative.data
  ⟨result.data, profile.work + first.work + body.work + reciprocal.work + activated.work +
    correction.work + negative.work + result.work + 6⟩

theorem current_value {count : ℕ} (primary centerLaw score : Vector RationalBits count)
    (anchor : Vector (Vector RationalBits count) count) (rate : RationalBits) (input center : Fin count) :
    (current primary centerLaw score anchor rate input center).data.decode =
      (score.get input).decode - rate.decode *
        (∑ color, (primary.get color).decode * (score.get color).decode * ((anchor.get color).get center).decode) /
          (centerLaw.get center).decode := by
  simp only [current, RationalBits.add_value, negate_value, RationalBits.multiply_value, inverse_value, readVector_value,
    sumFin_value, term_value, div_eq_mul_inv, sub_eq_add_neg]

def height (count bits : ℕ) : ℕ := (count + 1) * (3 * bits + 1) + 3 * bits + 3
def work (count bits : ℕ) : ℕ :=
  count * (13 * count + 18 + 3 * primitiveWorkBound (height count bits)) +
    6 * count + 14 + 5 * primitiveWorkBound (height count bits)

theorem term_height {count : ℕ} (primary score : Vector RationalBits count)
    (anchor : Vector (Vector RationalBits count) count) (center color : Fin count) (bits : ℕ)
    (hp : ∀ color, HeightBound (primary.get color).decode bits)
    (hs : ∀ color, HeightBound (score.get color).decode bits)
    (ha : ∀ color center, HeightBound ((anchor.get color).get center).decode bits) :
    HeightBound (term primary score anchor center color).data.decode (3 * bits) := by
  rw [term_value]
  exact (((hp color).mul (hs color)).mul (ha color center)).mono (by omega)

theorem term_work {count : ℕ} (primary score : Vector RationalBits count)
    (anchor : Vector (Vector RationalBits count) count) (center color : Fin count) (bits : ℕ)
    (hp : ∀ color, HeightBound (primary.get color).decode bits)
    (hs : ∀ color, HeightBound (score.get color).decode bits)
    (ha : ∀ color center, HeightBound ((anchor.get color).get center).decode bits) :
    (term primary score anchor center color).work ≤
      13 * count + 16 + 2 * primitiveWorkBound (height count bits) := by
  let B := height count bits
  have hb : 2 * bits ≤ B := by dsimp [B, height]; nlinarith
  have wp := readVector_work zero primary color
  have ws := readVector_work zero score color
  have wa := matrixEntry_work anchor color center
  have wfirst := RationalBits.multiply_work (readVector zero primary color).value (readVector zero score color).value B
    (by rw [readVector_value]; exact (hp color).mono (by omega))
    (by rw [readVector_value]; exact (hs color).mono (by omega))
  have wsecond := RationalBits.multiply_work
    (multiply (readVector zero primary color).value (readVector zero score color).value).data
    (matrixEntry anchor color center).value B
    (by rw [RationalBits.multiply_value, readVector_value, readVector_value]; exact ((hp color).mul (hs color)).mono (by omega))
    (by rw [matrixEntry_value]; exact (ha color center).mono (by omega))
  change _ + _ + _ + _ + _ + 2 ≤ 13 * count + 16 + 2 * primitiveWorkBound B
  omega

theorem current_height {count : ℕ} (primary centerLaw score : Vector RationalBits count)
    (anchor : Vector (Vector RationalBits count) count) (rate : RationalBits) (input center : Fin count)
    (bits : ℕ) (hp : ∀ color, HeightBound (primary.get color).decode bits)
    (hb : ∀ color, HeightBound (centerLaw.get color).decode bits)
    (hs : ∀ color, HeightBound (score.get color).decode bits)
    (ha : ∀ color center, HeightBound ((anchor.get color).get center).decode bits)
    (hr : HeightBound rate.decode bits) :
    HeightBound (current primary centerLaw score anchor rate input center).data.decode (height count bits) := by
  rw [current_value, sub_eq_add_neg]
  have hsum := HeightBound.sum Finset.univ
    (fun color => (primary.get color).decode * (score.get color).decode * ((anchor.get color).get center).decode)
    (3 * bits) (fun color _ => (((hp color).mul (hs color)).mul (ha color center)).mono (by omega))
  simp only [Finset.card_univ, Fintype.card_fin] at hsum
  exact ((hs input).add ((hr.mul hsum).div (hb center)).neg).mono (by unfold height; nlinarith)

theorem current_work {count : ℕ} (primary centerLaw score : Vector RationalBits count)
    (anchor : Vector (Vector RationalBits count) count) (rate : RationalBits) (input center : Fin count)
    (bits : ℕ) (hp : ∀ color, HeightBound (primary.get color).decode bits)
    (hb : ∀ color, HeightBound (centerLaw.get color).decode bits)
    (hs : ∀ color, HeightBound (score.get color).decode bits)
    (ha : ∀ color center, HeightBound ((anchor.get color).get center).decode bits)
    (hr : HeightBound rate.decode bits) :
    (current primary centerLaw score anchor rate input center).work ≤ work count bits := by
  let B := height count bits
  have hbits : bits ≤ B := by dsimp [B, height]; nlinarith
  have hsum := sumFin_height count (3 * bits) (term primary score anchor center)
    (fun color => term_height primary score anchor center color bits hp hs ha)
  have wsum := sumFin_work count (3 * bits) (13 * count + 16 + 2 * primitiveWorkBound B)
    (term primary score anchor center)
    (fun color => term_height primary score anchor center color bits hp hs ha)
    (fun color => term_work primary score anchor center color bits hp hs ha)
  have hmono := primitiveWorkBound_mono (show (count + 1) * (3 * bits + 1) ≤ B by dsimp [B, height]; nlinarith)
  have wf := readVector_work zero score input
  have wb := readVector_work zero centerLaw center
  have wi := inverse_work (readVector zero centerLaw center).value B
  have wa := RationalBits.multiply_work rate (sumFin count (term primary score anchor center)).data B
    (hr.mono hbits) (hsum.mono (by dsimp [B, height]; nlinarith))
  have hc := RationalBits.multiply_work
    (multiply rate (sumFin count (term primary score anchor center)).data).data
    (inverse (readVector zero centerLaw center).value).data B
    (by rw [RationalBits.multiply_value]; exact (hr.mul hsum).mono (by dsimp [B, height]; nlinarith))
    (by rw [inverse_value, readVector_value]; exact (hb center).inv.mono hbits)
  have hcorrection : HeightBound
      (multiply (multiply rate (sumFin count (term primary score anchor center)).data).data
        (inverse (readVector zero centerLaw center).value).data).data.decode B := by
    rw [RationalBits.multiply_value, RationalBits.multiply_value, inverse_value, readVector_value]
    exact ((hr.mul hsum).mul (hb center).inv).mono (by dsimp [B, height]; nlinarith)
  have wn := negate_work
    (multiply (multiply rate (sumFin count (term primary score anchor center)).data).data
      (inverse (readVector zero centerLaw center).value).data).data B
  have wadd := RationalBits.add_work (readVector zero score input).value
    (negate (multiply (multiply rate (sumFin count (term primary score anchor center)).data).data
      (inverse (readVector zero centerLaw center).value).data).data).data B
    (by rw [readVector_value]; exact (hs input).mono hbits)
    (by rw [negate_value]; exact hcorrection.neg)
  change _ + _ + _ + _ + _ + _ + _ + _ + 6 ≤ _
  unfold work
  nlinarith only [wsum, hmono, wf, wb, wi, wa, hc, wn, wadd]

end CurrentAFT.BinaryPairedScore
