import AFT.TrimmedPalette
import AFT.BlockDensity

/-!
# The actual integer-window endpoint pair and its exact marginals
-/

namespace AFT.TrimmedSlice

open scoped BigOperators

/-- Draw the first endpoint uniformly from its actual trimmed slice, then
set the second endpoint by the required integer pair sum. -/
noncomputable def orderedPairSlice (modulus : ℕ) (boundary shift : ℤ)
    (first second : Fin modulus) : ℝ :=
  law modulus boundary shift first.val *
    if (second.val : ℤ) = (modulus : ℤ) - 1 + shift - first.val then 1 else 0

theorem orderedPairSlice_nonneg (modulus : ℕ) (boundary shift : ℤ) (first second : Fin modulus) :
    0 ≤ orderedPairSlice modulus boundary shift first second := by
  unfold orderedPairSlice
  exact mul_nonneg (law_nonneg _ _ _ _) (by split_ifs <;> norm_num)

theorem orderedPairSlice_marginal (modulus : ℕ) (boundary shift : ℤ)
    (hb : 0 ≤ boundary) (first : Fin modulus) :
    ∑ second, orderedPairSlice modulus boundary shift first second = law modulus boundary shift first.val := by
  classical
  by_cases hc : (first.val : ℤ) ∈ slice modulus boundary shift
  · have hs := (mem_slice modulus boundary shift first.val).mp hc
    let output := (modulus : ℤ) - 1 + shift - first.val
    have houtput : 0 ≤ output ∧ output < modulus := by dsimp [output]; omega
    let second : Fin modulus := ⟨output.toNat, by omega⟩
    have heq : (second.val : ℤ) = output := by dsimp [second]; omega
    have hdelta (color : Fin modulus) : ((color.val : ℤ) = output) ↔ color = second := by
      constructor
      · intro hh
        apply Fin.ext
        have ht : (color.val : ℤ) = second.val := hh.trans heq.symm
        exact_mod_cast ht
      · rintro rfl
        exact heq
    simp only [orderedPairSlice, ← Finset.mul_sum]
    change law modulus boundary shift first.val * (∑ color : Fin modulus, if (color.val : ℤ) = output then 1 else 0) = _
    simp only [hdelta, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_one]
  · simp only [orderedPairSlice, law, if_neg hc, zero_mul, Finset.sum_const_zero]

theorem orderedPairSlice_symmetric (modulus : ℕ) (boundary shift : ℤ)
    (first second : Fin modulus) :
    orderedPairSlice modulus boundary shift first second = orderedPairSlice modulus boundary shift second first := by
  have hrel : ((second.val : ℤ) = (modulus : ℤ) - 1 + shift - first.val) ↔
      ((first.val : ℤ) = (modulus : ℤ) - 1 + shift - second.val) := by omega
  unfold orderedPairSlice
  by_cases hr : (second.val : ℤ) = (modulus : ℤ) - 1 + shift - first.val
  · have hc : (first.val : ℤ) ∈ slice modulus boundary shift ↔
        (second.val : ℤ) ∈ slice modulus boundary shift := by
      simp only [mem_slice]
      omega
    simp only [if_pos hr, if_pos (hrel.mp hr), mul_one, law, hc]
  · simp only [if_neg hr, if_neg (fun hh => hr (hrel.mpr hh)), mul_zero]

noncomputable def averagedPair (modulus : ℕ) (boundary start source : ℤ) (width : ℕ)
    (first second : Fin modulus) : ℝ :=
  ∑ offset ∈ anchorInterval start width,
    intervalAnchorLaw start width offset * orderedPairSlice modulus boundary (offset - source) first second

noncomputable def mixedPair {τ : Type*} [Fintype τ] (modulus : ℕ) (boundary : ℤ)
    (starts sources : τ → ℤ) (weights : τ → ℝ) (width : ℕ) (first second : Fin modulus) : ℝ :=
  ∑ index, weights index * averagedPair modulus boundary (starts index) (sources index) width first second

/-- The exact joint mass keeps the integer sum and its nonconstant slice
denominator; no circular-window replacement is used. -/
theorem averagedPair_formula (modulus : ℕ) (boundary start source : ℤ) (width : ℕ)
    (first second : Fin modulus) :
    averagedPair modulus boundary start source width first second =
      intervalAnchorLaw start width ((first.val : ℤ) + second.val - ((modulus : ℤ) - 1) + source) *
      law modulus boundary ((first.val : ℤ) + second.val - ((modulus : ℤ) - 1)) first.val := by
  let offset := (first.val : ℤ) + second.val - ((modulus : ℤ) - 1) + source
  unfold averagedPair
  rw [Finset.sum_eq_single offset]
  · have hs : offset - source = (first.val : ℤ) + second.val - ((modulus : ℤ) - 1) := by dsimp [offset]; ring
    have hd : (second.val : ℤ) = (modulus : ℤ) - 1 + (offset - source) - first.val := by dsimp [offset]; ring
    simp only [orderedPairSlice]
    rw [if_pos hd, mul_one, hs]
  · intro other _ hne
    have hd : ¬ (second.val : ℤ) = (modulus : ℤ) - 1 + (other - source) - first.val := by
      dsimp [offset] at hne
      omega
    simp [orderedPairSlice, hd]
  · intro hout
    simp only [intervalAnchorLaw, if_neg hout, zero_mul]

theorem mixedPair_first_marginal {τ : Type*} [Fintype τ]
    (modulus : ℕ) (boundary : ℤ) (starts sources : τ → ℤ) (weights : τ → ℝ) (width : ℕ)
    (hb : 0 ≤ boundary) (first : Fin modulus) :
    ∑ second, mixedPair modulus boundary starts sources weights width first second =
      mixedLaw modulus boundary starts sources weights width first.val := by
  unfold mixedPair mixedLaw averagedPair averagedLaw intervalMixture
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro index _
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, orderedPairSlice_marginal modulus boundary _ hb]

theorem mixedPair_symmetric {τ : Type*} [Fintype τ]
    (modulus : ℕ) (boundary : ℤ) (starts sources : τ → ℤ) (weights : τ → ℝ) (width : ℕ)
    (first second : Fin modulus) :
    mixedPair modulus boundary starts sources weights width first second =
      mixedPair modulus boundary starts sources weights width second first := by
  simp only [mixedPair, averagedPair, orderedPairSlice_symmetric modulus boundary _ first second]

theorem mixedPair_nonneg {τ : Type*} [Fintype τ]
    (modulus : ℕ) (boundary : ℤ) (starts sources : τ → ℤ) (weights : τ → ℝ) (width : ℕ)
    (hw : ∀ index, 0 ≤ weights index) (first second : Fin modulus) :
    0 ≤ mixedPair modulus boundary starts sources weights width first second := by
  apply Finset.sum_nonneg
  intro index _
  apply mul_nonneg (hw index)
  apply Finset.sum_nonneg
  intro offset _
  exact mul_nonneg (intervalAnchorLaw_nonneg _ _ _) (orderedPairSlice_nonneg _ _ _ _ _)

theorem mixedPair_mass {τ : Type*} [Fintype τ]
    (modulus : ℕ) (boundary shiftBound cutoff : ℤ) (width : ℕ) (hwidth : width ≠ 0)
    (starts sources : τ → ℤ) (weights : τ → ℝ)
    (hmass : ∑ index, weights index = 1) (hb : 0 ≤ boundary)
    (hstarts : ∀ index shift, shift ∈ anchorInterval (starts index) width → |shift| ≤ shiftBound)
    (hsources : ∀ index, |sources index| ≤ cutoff)
    (hclear : 2 * boundary + shiftBound + cutoff < modulus) :
    ∑ first, ∑ second, mixedPair modulus boundary starts sources weights width first second = 1 := by
  simp_rw [mixedPair_first_marginal modulus boundary starts sources weights width hb]
  exact mixedLaw_palette_mass modulus boundary shiftBound cutoff width hwidth starts sources weights hmass hb hstarts hsources hclear

/-- The physical joint endpoint mass has the sharp `1/(W*(q-D))` ceiling. -/
theorem mixedPair_le {τ : Type*} [Fintype τ]
    (modulus : ℕ) (boundary shiftBound cutoff : ℤ) (width : ℕ)
    (starts sources : τ → ℤ) (weights : τ → ℝ)
    (hweights : ∀ index, 0 ≤ weights index) (hmass : ∑ index, weights index = 1)
    (hstarts : ∀ index shift, shift ∈ anchorInterval (starts index) width → |shift| ≤ shiftBound)
    (hsources : ∀ index, |sources index| ≤ cutoff)
    (hclear : 2 * boundary + shiftBound + cutoff < modulus) (first second : Fin modulus) :
    mixedPair modulus boundary starts sources weights width first second ≤
      1 / ((width : ℝ) * ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff)) := by
  have hden : 0 < (modulus : ℝ) - 2 * boundary - shiftBound - cutoff := by
    have hh : (0 : ℤ) < (modulus : ℤ) - 2 * boundary - shiftBound - cutoff := by omega
    exact_mod_cast hh
  have hrow (index : τ) : averagedPair modulus boundary (starts index) (sources index) width first second ≤
      (width : ℝ)⁻¹ * (1 / ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff)) := by
    rw [averagedPair_formula]
    let shift := (first.val : ℤ) + second.val - ((modulus : ℤ) - 1)
    by_cases hin : shift + sources index ∈ anchorInterval (starts index) width
    · have hs : |shift| ≤ shiftBound + cutoff := by
        have hh := (abs_sub (shift + sources index) (sources index)).trans
          (add_le_add (hstarts index _ hin) (hsources index))
        simpa only [add_sub_cancel_right] using hh
      have hslice := law_le_of_shift_bound (modulus : ℤ) boundary shift (shiftBound + cutoff) first.val hs (by omega)
      have hh := mul_le_mul (intervalAnchorLaw_bound (starts index) (shift + sources index) width)
        hslice (law_nonneg _ _ _ _) (inv_nonneg.mpr (Nat.cast_nonneg width))
      convert hh using 1
      dsimp [shift]
      push_cast
      ring
    · have hz : intervalAnchorLaw (starts index) width (shift + sources index) = 0 := by simp [intervalAnchorLaw, hin]
      change intervalAnchorLaw (starts index) width (shift + sources index) * _ ≤ _
      rw [hz, zero_mul]
      positivity
  calc
    _ ≤ ∑ index, weights index * ((width : ℝ)⁻¹ *
      (1 / ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff))) :=
      Finset.sum_le_sum fun index _ => mul_le_mul_of_nonneg_left (hrow index) (hweights index)
    _ = _ := by rw [← Finset.sum_mul, hmass, one_mul]; simp only [one_div, mul_inv_rev, mul_comm]

/-- The endpoint construction is an actual finite probability distribution. -/
noncomputable def mixedPairDistribution {τ : Type*} [Fintype τ]
    (modulus : ℕ) (boundary shiftBound cutoff : ℤ) (width : ℕ) (hwidth : width ≠ 0)
    (starts sources : τ → ℤ) (sourceLaw : FiniteDist τ) (hb : 0 ≤ boundary)
    (hstarts : ∀ index shift, shift ∈ anchorInterval (starts index) width → |shift| ≤ shiftBound)
    (hsources : ∀ index, |sources index| ≤ cutoff)
    (hclear : 2 * boundary + shiftBound + cutoff < modulus) : FiniteDist (Fin modulus × Fin modulus) where
  weight point := mixedPair modulus boundary starts sources sourceLaw.weight width point.1 point.2
  nonneg point := mixedPair_nonneg _ _ _ _ _ _ sourceLaw.nonneg _ _
  sum_one := by
    rw [Fintype.sum_prod_type]
    exact mixedPair_mass modulus boundary shiftBound cutoff width hwidth starts sources sourceLaw.weight
      sourceLaw.sum_one hb hstarts hsources hclear

/-- The actual window pair has the claimed full uniform-profile energy,
with its exact integer-trimming denominator. -/
theorem mixedPair_uniform_energy_le {τ : Type*} [Fintype τ]
    (modulus : ℕ) (boundary shiftBound cutoff : ℤ) (width : ℕ) (hwidth : width ≠ 0)
    (starts sources : τ → ℤ) (sourceLaw : FiniteDist τ) (hb : 0 ≤ boundary)
    (hq : 0 < modulus)
    (hstarts : ∀ index shift, shift ∈ anchorInterval (starts index) width → |shift| ≤ shiftBound)
    (hsources : ∀ index, |sources index| ≤ cutoff)
    (hclear : 2 * boundary + shiftBound + cutoff < modulus) :
    BlockDensity.pairEnergy (fun _ : Fin modulus => 1 / (modulus : ℝ))
      (fun _ : Fin modulus => 1 / (modulus : ℝ))
      (mixedPair modulus boundary starts sources sourceLaw.weight width) ≤
      (modulus : ℝ) ^ 2 / ((width : ℝ) * ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff)) := by
  have hqReal : 0 < (modulus : ℝ) := by exact_mod_cast hq
  have hden : 0 < (modulus : ℝ) - 2 * boundary - shiftBound - cutoff := by
    have hh : (0 : ℤ) < (modulus : ℤ) - 2 * boundary - shiftBound - cutoff := by omega
    exact_mod_cast hh
  have hh := BlockDensity.diffuse_pair_energy_le (fun _ : Fin modulus => 1 / (modulus : ℝ))
    (fun _ : Fin modulus => 1 / (modulus : ℝ))
    (mixedPair modulus boundary starts sources sourceLaw.weight width)
    (1 / (modulus : ℝ)) (1 / (modulus : ℝ))
    (1 / ((width : ℝ) * ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff)))
    (by positivity) (by positivity) (by positivity) (fun _ => le_rfl) (fun _ => le_rfl)
    (mixedPair_nonneg _ _ _ _ _ _ sourceLaw.nonneg)
    (mixedPair_le modulus boundary shiftBound cutoff width starts sources sourceLaw.weight sourceLaw.nonneg
      sourceLaw.sum_one hstarts hsources hclear)
    (mixedPair_mass modulus boundary shiftBound cutoff width hwidth starts sources sourceLaw.weight
      sourceLaw.sum_one hb hstarts hsources hclear).le
  exact hh.trans_eq (by field_simp)

/-- Fixing either endpoint leaves counting-square mass at most
`1/(W*(q-D)^2)`, rather than introducing a palette-size factor. -/
theorem mixedPair_fiber_square_le {τ : Type*} [Fintype τ]
    (modulus : ℕ) (boundary shiftBound cutoff : ℤ) (width : ℕ) (hwidth : width ≠ 0)
    (starts sources : τ → ℤ) (sourceLaw : FiniteDist τ) (hb : 0 ≤ boundary)
    (hstarts : ∀ index shift, shift ∈ anchorInterval (starts index) width → |shift| ≤ shiftBound)
    (hsources : ∀ index, |sources index| ≤ cutoff)
    (hclear : 2 * boundary + shiftBound + cutoff < modulus) (first : Fin modulus) :
    (∑ second, mixedPair modulus boundary starts sources sourceLaw.weight width first second ^ 2) ≤
      1 / ((width : ℝ) * ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff) ^ 2) := by
  have hden : 0 < (modulus : ℝ) - 2 * boundary - shiftBound - cutoff := by
    have hh : (0 : ℤ) < (modulus : ℤ) - 2 * boundary - shiftBound - cutoff := by omega
    exact_mod_cast hh
  have hheight := mixedPair_le modulus boundary shiftBound cutoff width starts sources sourceLaw.weight
    sourceLaw.nonneg sourceLaw.sum_one hstarts hsources hclear
  have hmarginal := mixedLaw_le (modulus : ℤ) boundary shiftBound cutoff starts sources sourceLaw.weight width
    hwidth sourceLaw.nonneg sourceLaw.sum_one hstarts hsources hclear first.val
  calc
    _ ≤ ∑ second, (1 / ((width : ℝ) * ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff))) *
        mixedPair modulus boundary starts sources sourceLaw.weight width first second := by
      apply Finset.sum_le_sum
      intro second _
      have hh := mul_le_mul_of_nonneg_right (hheight first second)
        (mixedPair_nonneg modulus boundary starts sources sourceLaw.weight width sourceLaw.nonneg first second)
      nlinarith only [hh]
    _ = (1 / ((width : ℝ) * ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff))) *
        mixedLaw modulus boundary starts sources sourceLaw.weight width first.val := by
      rw [← Finset.mul_sum, mixedPair_first_marginal _ _ _ _ _ _ hb]
    _ ≤ (1 / ((width : ℝ) * ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff))) *
        (1 / ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff)) :=
      mul_le_mul_of_nonneg_left (by simpa only [Int.cast_natCast] using hmarginal) (by positivity)
    _ = _ := by
      have hwReal : (width : ℝ) ≠ 0 := by exact_mod_cast hwidth
      field_simp

end AFT.TrimmedSlice
