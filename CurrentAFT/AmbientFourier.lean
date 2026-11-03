import Mathlib

/-!
# Ambient Fourier energy for real signed masses

The frequency space is the actual group of all complex additive characters
of a finite abelian group. Its orthogonality and completeness are proved by
mathlib's finite Pontryagin duality, rather than assumed as a character-table
hypothesis. In particular the results apply to `Fin dimension → ZMod modulus`.
The final section proves the bijection with the manuscript's coordinate-indexed
positive-sign characters and reindexes the complete nonzero spectral sum.
-/

namespace CurrentAFT

open scoped BigOperators ComplexConjugate Classical

noncomputable section

variable {Group : Type*} [Fintype Group] [AddCommGroup Group]

/-- Unnormalized positive-sign Fourier transform of a finite complex mass. -/
def characterFourier (mass : Group → ℂ) (frequency : AddChar Group ℂ) : ℂ :=
  ∑ point, mass point * frequency point

/-- Orthogonality in the actual complete dual group. -/
theorem sum_character_kernel (first second : Group) :
    (∑ frequency : AddChar Group ℂ,
      conj (frequency first) * frequency second) =
      if first = second then (Fintype.card Group : ℂ) else 0 := by
  classical
  calc
    _ = ∑ frequency : AddChar Group ℂ, frequency (second - first) := by
      apply Finset.sum_congr rfl
      intro frequency _
      rw [AddChar.map_sub_eq_div, div_eq_mul_inv, AddChar.inv_apply_eq_conj]
      ring
    _ = _ := by rw [AddChar.sum_apply_eq_ite]; simp only [sub_eq_zero, eq_comm]

/-- Parseval with counting-measure normalization and no positivity hypothesis. -/
theorem character_parseval (mass : Group → ℂ) :
    (∑ frequency : AddChar Group ℂ, ‖characterFourier mass frequency‖ ^ 2) =
      (Fintype.card Group : ℝ) * ∑ point, ‖mass point‖ ^ 2 := by
  classical
  have hcomplex :
      (∑ frequency : AddChar Group ℂ,
        conj (characterFourier mass frequency) * characterFourier mass frequency) =
      (Fintype.card Group : ℂ) * ∑ point, conj (mass point) * mass point := by
    calc
      _ = ∑ frequency : AddChar Group ℂ, ∑ first, ∑ second,
          conj (mass first) * mass second *
            (conj (frequency first) * frequency second) := by
        apply Finset.sum_congr rfl
        intro frequency _
        simp only [characterFourier, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro first _
        apply Finset.sum_congr rfl
        intro second _
        ring
      _ = ∑ first, ∑ second, conj (mass first) * mass second *
          (∑ frequency : AddChar Group ℂ,
            conj (frequency first) * frequency second) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro first _
        rw [Finset.sum_comm]
      _ = ∑ first, ∑ second, conj (mass first) * mass second *
          (if first = second then (Fintype.card Group : ℂ) else 0) := by
        simp_rw [sum_character_kernel]
      _ = _ := by
        simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro point _
        ring
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self] using hcomplex

/-- The normalized uniform mass has only its trivial-character coefficient. -/
theorem characterFourier_uniform (frequency : AddChar Group ℂ) :
    characterFourier (fun _ : Group => (Fintype.card Group : ℂ)⁻¹) frequency =
      if frequency = 0 then 1 else 0 := by
  classical
  have hcard : (Fintype.card Group : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [characterFourier, ← Finset.mul_sum, AddChar.sum_eq_ite]
  split_ifs <;> simp [hcard]

/-- Linearity is used before imposing positivity or charge. -/
theorem characterFourier_sub (first second : Group → ℂ)
    (frequency : AddChar Group ℂ) :
    characterFourier (fun point => first point - second point) frequency =
      characterFourier first frequency - characterFourier second frequency := by
  simp only [characterFourier, sub_mul, Finset.sum_sub_distrib]

/-- The signed real mass convention of the current manuscript. -/
def signedFourier (mass : Group → ℝ) (frequency : AddChar Group ℂ) : ℂ :=
  characterFourier (fun point => (mass point : ℂ)) frequency

/-- Difference between a real signed mass and ambient uniformity. -/
def uniformDeviation (mass : Group → ℝ) (point : Group) : ℝ :=
  mass point - (Fintype.card Group : ℝ)⁻¹

@[simp] theorem signedFourier_zero (mass : Group → ℝ) :
    signedFourier mass 0 = (∑ point, mass point : ℝ) := by
  simp [signedFourier, characterFourier]

/-- The Fourier transform of the centered signed mass. -/
theorem signedFourier_uniformDeviation (mass : Group → ℝ)
    (frequency : AddChar Group ℂ) :
    signedFourier (uniformDeviation mass) frequency =
      signedFourier mass frequency - if frequency = 0 then 1 else 0 := by
  unfold signedFourier uniformDeviation
  simp only [Complex.ofReal_sub, Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [characterFourier_sub, characterFourier_uniform]

/-- Ambient Parseval with the zero frequency removed. This applies to every
real signed mass of total mass one, even when some weights are negative. -/
theorem ambient_signed_energy (mass : Group → ℝ) (hmass : ∑ point, mass point = 1) :
    (Fintype.card Group : ℝ) * ∑ point, (uniformDeviation mass point) ^ 2 =
      ∑ frequency ∈ Finset.univ.erase (0 : AddChar Group ℂ),
        ‖signedFourier mass frequency‖ ^ 2 := by
  classical
  have hparseval := character_parseval
    (fun point => (uniformDeviation mass point : ℂ))
  have hreal :
      (∑ frequency : AddChar Group ℂ,
        ‖signedFourier (uniformDeviation mass) frequency‖ ^ 2) =
      (Fintype.card Group : ℝ) * ∑ point, (uniformDeviation mass point) ^ 2 := by
    simpa only [signedFourier, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hparseval
  rw [← hreal]
  rw [← Finset.sum_erase_add Finset.univ
    (fun frequency : AddChar Group ℂ =>
      ‖signedFourier (uniformDeviation mass) frequency‖ ^ 2)
    (Finset.mem_univ 0)]
  have hzero : signedFourier (uniformDeviation mass) 0 = 0 := by
    rw [signedFourier_uniformDeviation]
    simp [hmass]
  rw [hzero, show ‖(0 : ℂ)‖ ^ 2 = 0 by norm_num, add_zero]
  apply Finset.sum_congr rfl
  intro frequency hfrequency
  rw [signedFourier_uniformDeviation]
  simp [Finset.ne_of_mem_erase hfrequency]

/-- Density of a signed mass relative to the exact ambient uniform law. -/
def uniformDensity (mass : Group → ℝ) (point : Group) : ℝ :=
  (Fintype.card Group : ℝ) * mass point

/-- The density-error and mass-error normalizations agree exactly. -/
theorem uniformDensity_deviation (mass : Group → ℝ) (point : Group) :
    uniformDensity mass point - 1 =
      (Fintype.card Group : ℝ) * uniformDeviation mass point := by
  have hcard : (Fintype.card Group : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [uniformDensity, uniformDeviation, mul_sub, mul_inv_cancel₀ hcard]

/-- Exact squared L2 energy under the ambient uniform reference, written as
its finite average. This is the normalization in `lem:df-ambient-target`. -/
theorem ambient_density_energy (mass : Group → ℝ) (hmass : ∑ point, mass point = 1) :
    (∑ point, (uniformDensity mass point - 1) ^ 2) / (Fintype.card Group : ℝ) =
      ∑ frequency ∈ Finset.univ.erase (0 : AddChar Group ℂ),
        ‖signedFourier mass frequency‖ ^ 2 := by
  have hcard : (Fintype.card Group : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [← ambient_signed_energy mass hmass]
  simp_rw [uniformDensity_deviation, mul_pow]
  rw [← Finset.mul_sum]
  field_simp

/-- Cauchy--Schwarz and the complete character energy give the ambient
half-L1 error, with no nonnegativity assumption on the signed law. -/
theorem ambient_signed_half_l1 (mass : Group → ℝ) (hmass : ∑ point, mass point = 1) :
    (∑ point, |uniformDeviation mass point|) / 2 ≤
      Real.sqrt (∑ frequency ∈ Finset.univ.erase (0 : AddChar Group ℂ),
        ‖signedFourier mass frequency‖ ^ 2) / 2 := by
  classical
  let energy := ∑ frequency ∈ Finset.univ.erase (0 : AddChar Group ℂ),
    ‖signedFourier mass frequency‖ ^ 2
  have henergy : 0 ≤ energy := Finset.sum_nonneg fun frequency _ => sq_nonneg _
  have hcs : (∑ point, |uniformDeviation mass point|) ^ 2 ≤
      (Fintype.card Group : ℝ) * ∑ point, (uniformDeviation mass point) ^ 2 := by
    simpa only [Finset.card_univ, sq_abs] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun point : Group => |uniformDeviation mass point|))
  rw [ambient_signed_energy mass hmass] at hcs
  have hroot := Real.sq_sqrt henergy
  have hrootNonneg := Real.sqrt_nonneg energy
  have hl1Nonneg : 0 ≤ ∑ point, |uniformDeviation mass point| :=
    Finset.sum_nonneg fun point _ => abs_nonneg _
  change (∑ point, |uniformDeviation mass point|) / 2 ≤ Real.sqrt energy / 2
  nlinarith

section Coordinates

variable {Index : Type*} [Fintype Index]
    {modulus : ℕ} [NeZero modulus]

/-- The manuscript's positive-sign coordinate character, constructed from
mathlib's characters `exp(2 π i frequency * point / modulus)` on `ZMod`.
The modulus need only be nonzero; primality is unnecessary for Fourier theory. -/
def coordinateCharacter (frequency : Index → ZMod modulus) :
    AddChar (Index → ZMod modulus) ℂ where
  toFun point := ∏ index, AddChar.zmodAddEquiv (frequency index) (point index)
  map_zero_eq_one' := by simp
  map_add_eq_mul' first second := by
    simp [AddChar.map_add_eq_mul, Finset.prod_mul_distrib]

/-- Exact coordinate product formula. -/
theorem coordinateCharacter_apply (frequency point : Index → ZMod modulus) :
    coordinateCharacter frequency point =
      ∏ index, AddChar.zmodAddEquiv (frequency index) (point index) := rfl

/-- The positive-sign coordinate character is explicitly the product of the
one-coordinate circle exponentials. -/
theorem coordinateCharacter_apply_zmod (frequency point : Index → ZMod modulus) :
    coordinateCharacter frequency point =
      ∏ index, ((AddChar.zmod modulus (frequency index) (point index) : Circle) : ℂ) := rfl

/-- Integer representatives give the positive exponent convention of the
current paper. Products multiply the characters across all coordinates. -/
theorem coordinateCharacter_intCast (frequency point : Index → ℤ) :
    coordinateCharacter (fun index => (frequency index : ZMod modulus))
      (fun index => (point index : ZMod modulus)) =
      ∏ index, ((Circle.exp (2 * Real.pi *
        ((frequency index : ℝ) * (point index : ℝ) / modulus)) : Circle) : ℂ) := by
  simp only [coordinateCharacter_apply_zmod, AddChar.zmod_intCast]

@[simp] theorem coordinateCharacter_zero :
    coordinateCharacter (0 : Index → ZMod modulus) = 0 := by
  ext point
  rw [coordinateCharacter_apply]
  simp only [Pi.zero_apply, map_zero, AddChar.zero_apply, Finset.prod_const_one]

variable [DecidableEq Index]

/-- Evaluation on one coordinate identifies the corresponding frequency. -/
@[simp] theorem coordinateCharacter_single (frequency : Index → ZMod modulus)
    (index : Index) (point : ZMod modulus) :
    coordinateCharacter frequency (Pi.single index point) =
      AddChar.zmodAddEquiv (frequency index) point := by
  rw [coordinateCharacter_apply]
  rw [Finset.prod_eq_single index]
  · simp only [Pi.single_apply, ite_true]
  · intro other _ hne
    simp only [Pi.single_apply, if_neg hne, AddChar.map_zero_eq_one]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ index))

/-- All coordinate characters are distinct. -/
theorem coordinateCharacter_injective :
    Function.Injective (coordinateCharacter (Index := Index) (modulus := modulus)) := by
  intro first second hequal
  funext index
  apply AddChar.zmodAddEquiv.injective
  ext point
  have heval := congrArg
    (fun character : AddChar (Index → ZMod modulus) ℂ =>
      character (Pi.single index point)) hequal
  simpa only [coordinateCharacter_single] using heval

/-- Coordinate frequency vectors enumerate the whole dual group, with no
missing or repeated frequencies. Completeness uses finite Pontryagin duality. -/
def coordinateCharacterEquiv : (Index → ZMod modulus) ≃
    AddChar (Index → ZMod modulus) ℂ :=
  Equiv.ofBijective coordinateCharacter
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨coordinateCharacter_injective, AddChar.card_eq.symm⟩)

@[simp] theorem coordinateCharacterEquiv_apply (frequency : Index → ZMod modulus) :
    coordinateCharacterEquiv frequency = coordinateCharacter frequency := rfl

/-- Reindexing the complete nonzero energy by actual coordinate frequencies. -/
theorem coordinate_nonzero_energy (mass : (Index → ZMod modulus) → ℝ) :
    (∑ frequency ∈ Finset.univ.erase (0 : Index → ZMod modulus),
      ‖signedFourier mass (coordinateCharacter frequency)‖ ^ 2) =
      ∑ frequency ∈ Finset.univ.erase (0 : AddChar (Index → ZMod modulus) ℂ),
        ‖signedFourier mass frequency‖ ^ 2 := by
  classical
  have hall :
      (∑ frequency : Index → ZMod modulus,
        ‖signedFourier mass (coordinateCharacter frequency)‖ ^ 2) =
      ∑ frequency : AddChar (Index → ZMod modulus) ℂ,
        ‖signedFourier mass frequency‖ ^ 2 := by
    exact (coordinateCharacterEquiv (Index := Index) (modulus := modulus)).sum_comp
      (fun frequency : AddChar (Index → ZMod modulus) ℂ =>
        ‖signedFourier mass frequency‖ ^ 2)
  have hvector := Finset.sum_erase_add Finset.univ
    (fun frequency : Index → ZMod modulus =>
      ‖signedFourier mass (coordinateCharacter frequency)‖ ^ 2) (Finset.mem_univ 0)
  have hdual := Finset.sum_erase_add Finset.univ
    (fun frequency : AddChar (Index → ZMod modulus) ℂ =>
      ‖signedFourier mass frequency‖ ^ 2) (Finset.mem_univ 0)
  dsimp only at hvector hdual
  rw [coordinateCharacter_zero] at hvector
  linarith

/-- The exact ambient energy identity on the current paper's vector space,
with every nonzero coordinate frequency present. -/
theorem coordinate_ambient_signed_energy
    (mass : (Index → ZMod modulus) → ℝ) (hmass : ∑ point, mass point = 1) :
    (Fintype.card (Index → ZMod modulus) : ℝ) *
        ∑ point, (uniformDeviation mass point) ^ 2 =
      ∑ frequency ∈ Finset.univ.erase (0 : Index → ZMod modulus),
        ‖signedFourier mass (coordinateCharacter frequency)‖ ^ 2 := by
  rw [coordinate_nonzero_energy]
  exact ambient_signed_energy mass hmass

/-- The ambient error inequality in coordinate frequency notation. -/
theorem coordinate_ambient_signed_half_l1
    (mass : (Index → ZMod modulus) → ℝ) (hmass : ∑ point, mass point = 1) :
    (∑ point, |uniformDeviation mass point|) / 2 ≤
      Real.sqrt (∑ frequency ∈ Finset.univ.erase (0 : Index → ZMod modulus),
        ‖signedFourier mass (coordinateCharacter frequency)‖ ^ 2) / 2 := by
  rw [coordinate_nonzero_energy]
  exact ambient_signed_half_l1 mass hmass

end Coordinates

end

end CurrentAFT
