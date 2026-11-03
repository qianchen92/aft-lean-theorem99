import CurrentAFT.AmbientFourier
import AFT.LocalTensors

/-!
# Actual finite color coordinates and the positive-sign character basis

The palette may be the implementation's `Fin q`. A fixed equivalence with
`ZMod q` supplies the actual additive characters. Parseval and the
centered-atom identities are proved on these finite sums, with no assumed
unitary table or replacement of the physical coefficient arrays.
-/

namespace CurrentAFT.FourierCoordinates

open AFT
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable {Color Index : Type*} [Fintype Color] [Nonempty Color] [Fintype Index] [DecidableEq Index]
  {modulus : ℕ} [NeZero modulus]

def scalarCharacter (palette : Color ≃ ZMod modulus) (frequency : ZMod modulus) (color : Color) : ℂ :=
  AddChar.zmodAddEquiv frequency (palette color)

def fourier (palette : Color ≃ ZMod modulus) (mass : (Index → Color) → ℂ)
    (frequency : Index → ZMod modulus) : ℂ :=
  ∑ point, mass point * ∏ index, scalarCharacter palette (frequency index) (point index)

def uniformReference : FiniteDist Color := FiniteDist.uniform Color

omit [Nonempty Color] [NeZero modulus] in
/-- Finite complex Fubini on the actual independent color word. -/
theorem complex_product_expectation (reference : Index → FiniteDist Color)
    (factor : Index → Color → ℂ) :
    (∑ point : Index → Color, ((FiniteDist.independent reference).weight point : ℂ) *
      ∏ index, factor index (point index)) =
      ∏ index, ∑ color, ((reference index).weight color : ℂ) * factor index color := by
  simp only [FiniteDist.independent, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun index : Index => fun color : Color =>
    ((reference index).weight color : ℂ) * factor index color)).symm

omit [Nonempty Color] in
/-- Full word-space Fourier Parseval through the actual palette equivalence. -/
theorem parseval (palette : Color ≃ ZMod modulus) (mass : (Index → Color) → ℂ) :
    (∑ frequency : Index → ZMod modulus, ‖fourier palette mass frequency‖ ^ 2) =
      (Fintype.card (Index → Color) : ℝ) * ∑ point, ‖mass point‖ ^ 2 := by
  let words : (Index → Color) ≃ (Index → ZMod modulus) := Equiv.piCongrRight (fun _ => palette)
  have hfrequency (frequency : Index → ZMod modulus) :
      fourier palette mass frequency = characterFourier
        (fun point => mass (words.symm point)) (coordinateCharacter frequency) := by
    have h := words.sum_comp (fun point => mass (words.symm point) * coordinateCharacter frequency point)
    simpa only [fourier, scalarCharacter, coordinateCharacter, Equiv.symm_apply_apply,
      words, Equiv.piCongrRight_apply, Equiv.coe_fn_mk] using h
  simp_rw [hfrequency]
  change (∑ frequency : Index → ZMod modulus, ‖characterFourier
    (fun point => mass (words.symm point)) ((coordinateCharacterEquiv (Index := Index) (modulus := modulus)) frequency)‖ ^ 2) = _
  rw [(coordinateCharacterEquiv (Index := Index) (modulus := modulus)).sum_comp
    (fun frequency => ‖characterFourier (fun point => mass (words.symm point)) frequency‖ ^ 2)]
  rw [character_parseval]
  have hcard := Fintype.card_congr words
  rw [← hcard]
  congr 1
  exact words.symm.sum_comp (fun point => ‖mass point‖ ^ 2)

/-- Exact probability-normalized Fourier energy of a real density array. -/
theorem uniform_density_parseval
    (palette : Color ≃ ZMod modulus) (density : (Index → Color) → ℝ) :
    (∑ frequency : Index → ZMod modulus,
      ‖fourier palette (fun point =>
        (((FiniteDist.independent (fun _ : Index => uniformReference (Color := Color))).weight point *
          density point : ℝ) : ℂ)) frequency‖ ^ 2) =
      (FiniteDist.independent (fun _ : Index => uniformReference (Color := Color))).l2Sq density := by
  rw [show FiniteDist.independent (fun _ : Index => uniformReference (Color := Color)) =
      FiniteDist.uniform (Index → Color) by
        ext point
        simp only [FiniteDist.independent, uniformReference, FiniteDist.uniform_weight,
          Finset.prod_const, Finset.card_univ, Fintype.card_fun, Nat.cast_pow, inv_pow]]
  rw [parseval]
  simp only [FiniteDist.uniform_weight, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    FiniteDist.l2Sq, FiniteDist.expectation, mul_pow]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hcard : (Fintype.card (Index → Color) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- The actual normalized uniform scalar character average. -/
theorem scalarCharacter_uniform (palette : Color ≃ ZMod modulus) (frequency : ZMod modulus) :
    (∑ color : Color, ((uniformReference (Color := Color)).weight color : ℂ) *
      scalarCharacter palette frequency color) = if frequency = 0 then 1 else 0 := by
  have hcard := Fintype.card_congr palette
  simp only [uniformReference, FiniteDist.uniform_weight, scalarCharacter,
    Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [hcard, palette.sum_comp (fun point => (Fintype.card (ZMod modulus) : ℂ)⁻¹ *
    AddChar.zmodAddEquiv frequency point)]
  have h := characterFourier_uniform (AddChar.zmodAddEquiv frequency)
  have hzero : AddChar.zmodAddEquiv frequency = 0 ↔ frequency = 0 := by
    constructor
    · intro h
      apply AddChar.zmodAddEquiv.injective
      simpa only [map_zero] using h
    · intro h
      subst frequency
      exact map_zero _
  simpa only [characterFourier, hzero] using h

/-- Multiplication by the real centered atom has its actual positive-sign
Fourier response, with no reference atom omitted. -/
theorem centeredAtom_fourier (palette : Color ≃ ZMod modulus) (input : Color) (frequency : ZMod modulus) :
    (∑ output : Color, ((uniformReference (Color := Color)).weight output : ℂ) *
      (Hoeffding.centeredAtom (uniformReference (Color := Color)) input output : ℂ) *
        scalarCharacter palette frequency output) =
      if frequency = 0 then 0 else scalarCharacter palette frequency input := by
  have hatom (output : Color) :
      ((uniformReference (Color := Color)).weight output : ℂ) *
        (Hoeffding.centeredAtom (uniformReference (Color := Color)) input output : ℂ) =
      (if input = output then (1 : ℂ) else 0) - (uniformReference (Color := Color)).weight output := by
    have hpositive : 0 < (uniformReference (Color := Color)).weight output := by
      exact inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
    by_cases hequal : input = output
    · simp only [Hoeffding.centeredAtom, if_pos hequal, Complex.ofReal_sub, Complex.ofReal_inv,
        Complex.ofReal_one]
      have hnonzero : ((uniformReference (Color := Color)).weight output : ℂ) ≠ 0 := by
        exact_mod_cast hpositive.ne'
      field_simp
    · simp [Hoeffding.centeredAtom, hequal]
  simp_rw [hatom, sub_mul]
  rw [Finset.sum_sub_distrib, scalarCharacter_uniform]
  simp only [ite_mul, zero_mul, one_mul]
  by_cases hzero : frequency = 0
  · subst frequency
    have hchar : AddChar.zmodAddEquiv (0 : ZMod modulus) = 0 := map_zero _
    simp only [scalarCharacter, hchar, AddChar.zero_apply]
    simp
  · simp [hzero]

end

end CurrentAFT.FourierCoordinates
