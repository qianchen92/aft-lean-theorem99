import AFT.BinaryPositiveFinDraw
import AFT.BinarySamplingPolynomials

/-! An interval-index sampler with a binary-computed uniform probability. -/
namespace AFT.BinaryArithmetic
open AFT.RationalRejectionProgram AFT.RationalNumerics RationalBits Polynomial

def binaryUniformDraw (count : ℕ) (hc : 0 < count) (bits : ℕ)
    (word : Fin (bits+count+1) → Fin 2) : CountedValue (Fin count) :=
  letI : NeZero count := ⟨Nat.ne_zero_of_lt hc⟩
  let encoded := ofCounter count
  let probability := inverse encoded.data
  let weights := Vector.replicate count probability.data
  let selected := binaryPositiveFinDraw weights bits word
  ⟨⟨selected.value,binaryPositiveFinDraw_lt weights bits word⟩,
    encoded.work+probability.work+count+selected.work+4⟩

theorem binaryUniformDraw_value (count : ℕ) (hc : 0 < count) (bits : ℕ)
    (word : Fin (bits+count+1) → Fin 2) :
    (binaryUniformDraw count hc bits word).value=
      RationalPaletteSampler.draw count hc (fun _ => (count : ℚ)⁻¹) bits word := by
  letI : NeZero count := ⟨Nat.ne_zero_of_lt hc⟩
  apply Fin.ext
  change (binaryPositiveFinDraw _ bits word).value=_
  rw [binaryPositiveFinDraw_palette_value]
  simp only [Vector.get_replicate,inverse_value,ofCounter_value]

def binaryUniformDrawWork (count bits : ℕ) : ℕ :=
  60*(count+1)^2+primitiveWorkBound count+count+binaryPositiveDrawWork count count bits+4

theorem binaryUniformDraw_work (count : ℕ) (hc : 0 < count) (bits : ℕ)
    (word : Fin (bits+count+1) → Fin 2) :
    (binaryUniformDraw count hc bits word).work ≤ binaryUniformDrawWork count bits := by
  letI : NeZero count := ⟨Nat.ne_zero_of_lt hc⟩
  have he := ofCounter_work count
  have hh : HeightBound (ofCounter count).data.decode count := by
    rw [ofCounter_value];exact HeightBound.nat_coarse _
  have hi := inverse_work (ofCounter count).data count
  have hp : HeightBound (inverse (ofCounter count).data).data.decode count := by
    rw [inverse_value];exact hh.inv
  have hd := binaryPositiveFinDraw_work (Vector.replicate count (inverse (ofCounter count).data).data)
    count bits (by intro index;simpa only [Vector.get_replicate] using hp) word
  unfold binaryUniformDraw binaryUniformDrawWork
  dsimp only
  omega

noncomputable def binaryUniformDrawPolynomial (count bits : Polynomial ℕ) : Polynomial ℕ :=
  60*(count+1)^2+primitiveWorkPolynomial count+count+binaryPositiveDrawPolynomial count count bits+4

@[simp] theorem binaryUniformDrawPolynomial_eval (count bits : Polynomial ℕ) (n : ℕ) :
    (binaryUniformDrawPolynomial count bits).eval n=binaryUniformDrawWork (count.eval n) (bits.eval n) := by
  simp [binaryUniformDrawPolynomial,binaryUniformDrawWork]

theorem binaryUniformDrawWork_mono {c d b e : ℕ} (hc : c ≤ d) (hb : b ≤ e) :
    binaryUniformDrawWork c b ≤ binaryUniformDrawWork d e := by
  have hd := binaryPositiveDrawWork_mono hc hc hb
  unfold binaryUniformDrawWork primitiveWorkBound
  gcongr

end AFT.BinaryArithmetic
