import CurrentAFT.FirstResponse

/-!
# The actual inward anchor kernel

The index is uniform on `Fin A`, representing the integer interval
`A,...,2*A-1`. Its sign is inward away from the palette midpoint;
at the midpoint a fresh fair Boolean chooses either sign. The smoothed
kernel adds an independent draw from the actual protected scalar law.

Probability normalization, safe support, and column height are derived
from these finite draws. They are not assumptions on an abstract kernel.
-/

namespace CurrentAFT.InwardAnchor

open AFT DiffuseProfiles
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth
  Parameters.sourceCutoff Parameters.safeMargin DiffuseProfiles.scalarLaw

abbrev Palette (security : ℕ) := Fin (Parameters.modulus security)
abbrev Index (security : ℕ) := Fin (Parameters.anchorWidth security)
abbrev ScalarSample (security : ℕ) := GaussianSource.Window (Parameters.sourceCutoff security - 1)

theorem anchorWidth_pos (security : ℕ) : 0 < Parameters.anchorWidth security := by
  rw [anchorWidth_eq]
  exact pow_pos (Parameters.base_pos security) _

local instance anchorWidthNeZero (security : ℕ) : NeZero (Parameters.anchorWidth security) :=
  ⟨(anchorWidth_pos security).ne'⟩

theorem sourceCutoff_pos (security : ℕ) : 0 < Parameters.sourceCutoff security := by
  unfold Parameters.sourceCutoff
  exact pow_pos (Parameters.base_pos security) _

theorem four_cutoffs_le_anchor (security : ℕ) :
    4 * Parameters.sourceCutoff security ≤ Parameters.anchorWidth security := by
  have hb : 2 ≤ Parameters.base security := Parameters.base_ge_two security
  have hb1 : 1 ≤ Parameters.base security := by omega
  have hb2 : 4 ≤ Parameters.base security ^ 2 := by nlinarith
  have hfactor : 4 ≤ Parameters.base security ^ 46 :=
    hb2.trans (Nat.pow_le_pow_right hb1 (by omega))
  rw [anchorWidth_eq, Parameters.sourceCutoff]
  calc
    _ ≤ Parameters.base security ^ 46 * Parameters.base security ^ 2 :=
      Nat.mul_le_mul_right _ hfactor
    _ = _ := by rw [← pow_add]

theorem modulus_room (security : ℕ) :
    6 * Parameters.anchorWidth security + 1 ≤ Parameters.modulus security := by
  have hb : 1 ≤ Parameters.base security := by have := Parameters.base_ge_two security; omega
  have ha : Parameters.anchorWidth security ≤ Parameters.base security ^ 64 := by
    rw [anchorWidth_eq]
    exact Nat.pow_le_pow_right hb (by omega)
  have hpower : 1 ≤ Parameters.base security ^ 64 := one_le_pow₀ hb
  have hq := (Parameters.modulus_bounds security).1
  omega

/-- The Boolean is read only at the midpoint. -/
def positiveDirection (security : ℕ) (color : Palette security) (coin : Bool) : Bool :=
  if 2 * color.val < Parameters.modulus security - 1 then false
  else if Parameters.modulus security - 1 < 2 * color.val then true else coin

def offset (security : ℕ) (index : Index security) : ℤ :=
  (Parameters.anchorWidth security : ℤ) + index.val

def integerPoint (security : ℕ) (color : Palette security) (coin : Bool)
    (index : Index security) (shift : ℤ) : ℤ :=
  (Parameters.modulus security : ℤ) - 1 - color.val +
    (if positiveDirection security color coin then offset security index else -offset security index) + shift

theorem direction_left (security : ℕ) (color : Palette security) (coin : Bool)
    (hdirection : positiveDirection security color coin = false) :
    2 * (color.val : ℤ) ≤ (Parameters.modulus security : ℤ) - 1 := by
  have hq := (Parameters.modulus_spec security).2.pos
  by_contra h
  have hhigh : Parameters.modulus security - 1 < 2 * color.val := by omega
  have hlow : ¬2 * color.val < Parameters.modulus security - 1 := by omega
  simp [positiveDirection, hlow, hhigh] at hdirection

theorem direction_right (security : ℕ) (color : Palette security) (coin : Bool)
    (hdirection : positiveDirection security color coin = true) :
    (Parameters.modulus security : ℤ) - 1 ≤ 2 * (color.val : ℤ) := by
  have hq := (Parameters.modulus_spec security).2.pos
  by_contra h
  have hlow : 2 * color.val < Parameters.modulus security - 1 := by omega
  simp [positiveDirection, hlow] at hdirection

/-- All anchor samples remain safe after every protected scalar shift. -/
theorem integerPoint_safe (security : ℕ) (color : Palette security) (coin : Bool)
    (index : Index security) (shift : ℤ)
    (hshift : |shift| ≤ (Parameters.sourceCutoff security : ℤ) - 1) :
    (Parameters.safeMargin security : ℤ) ≤ integerPoint security color coin index shift ∧
      integerPoint security color coin index shift <
        (Parameters.modulus security : ℤ) - Parameters.safeMargin security := by
  have hroom : 6 * (Parameters.anchorWidth security : ℤ) + 1 ≤ Parameters.modulus security := by
    exact_mod_cast modulus_room security
  have hfour : 4 * (Parameters.sourceCutoff security : ℤ) ≤ Parameters.anchorWidth security := by
    exact_mod_cast four_cutoffs_le_anchor security
  have hmargin : (Parameters.safeMargin security : ℤ) +
      ((Parameters.sourceCutoff security : ℤ) - 1) ≤ Parameters.anchorWidth security := by
    rw [Parameters.safeMargin]
    push_cast
    omega
  have hindex := index.isLt
  have hoffsetLower : (Parameters.anchorWidth security : ℤ) ≤ offset security index := by
    unfold offset
    omega
  have hoffsetUpper : offset security index < 2 * (Parameters.anchorWidth security : ℤ) := by
    unfold offset
    omega
  cases hdirection : positiveDirection security color coin
  · simpa only [integerPoint, hdirection, Bool.false_eq_true, if_false, sub_eq_add_neg] using
      publicAnchor_left_safe (Parameters.modulus security) (Parameters.anchorWidth security) color.val
        (offset security index) shift (Parameters.safeMargin security)
        ((Parameters.sourceCutoff security : ℤ) - 1) hroom (Int.natCast_nonneg _)
        (direction_left security color coin hdirection) hoffsetLower hoffsetUpper hshift hmargin
  · simpa only [integerPoint, hdirection, if_true] using
      publicAnchor_right_safe (Parameters.modulus security) (Parameters.anchorWidth security) color.val
        (offset security index) shift (Parameters.safeMargin security)
        ((Parameters.sourceCutoff security : ℤ) - 1) hroom (by exact_mod_cast color.isLt)
        (direction_right security color coin hdirection) hoffsetLower hoffsetUpper hshift hmargin

def SafeColor (security : ℕ) (color : Palette security) : Prop :=
  (Parameters.safeMargin security : ℤ) ≤ color.val ∧
    (color.val : ℤ) < (Parameters.modulus security : ℤ) - Parameters.safeMargin security

/-- Reduction to the actual finite palette is performed only after the
integer support theorem; it never wraps an unsafe anchor around the palette. -/
def point (security : ℕ) (color : Palette security) (coin : Bool)
    (index : Index security) (shift : ℤ)
    (hshift : |shift| ≤ (Parameters.sourceCutoff security : ℤ) - 1) : Palette security :=
  ⟨(integerPoint security color coin index shift).toNat, by
    have hs := integerPoint_safe security color coin index shift hshift
    have hm : (0 : ℤ) ≤ Parameters.safeMargin security := Int.natCast_nonneg _
    omega⟩

theorem point_value (security : ℕ) (color : Palette security) (coin : Bool)
    (index : Index security) (shift : ℤ)
    (hshift : |shift| ≤ (Parameters.sourceCutoff security : ℤ) - 1) :
    ((point security color coin index shift hshift).val : ℤ) =
      integerPoint security color coin index shift := by
  have hs := integerPoint_safe security color coin index shift hshift
  have hn : 0 ≤ integerPoint security color coin index shift :=
    (Int.natCast_nonneg _).trans hs.1
  exact Int.toNat_of_nonneg hn

theorem point_safe (security : ℕ) (color : Palette security) (coin : Bool)
    (index : Index security) (shift : ℤ)
    (hshift : |shift| ≤ (Parameters.sourceCutoff security : ℤ) - 1) :
    SafeColor security (point security color coin index shift hshift) := by
  unfold SafeColor
  rw [point_value]
  exact integerPoint_safe security color coin index shift hshift

theorem point_index_injective (security : ℕ) (color : Palette security) (coin : Bool)
    (shift : ℤ) (hshift : |shift| ≤ (Parameters.sourceCutoff security : ℤ) - 1) :
    Function.Injective (fun index => point security color coin index shift hshift) := by
  intro first second hequal
  have h := congrArg (fun output : Palette security => (output.val : ℤ)) hequal
  change ((point security color coin first shift hshift).val : ℤ) =
    ((point security color coin second shift hshift).val : ℤ) at h
  rw [point_value, point_value] at h
  unfold integerPoint offset at h
  split_ifs at h <;> apply Fin.ext <;> omega

/-- One sign column is the pushforward of the actual uniform anchor index. -/
def fixedCoinLaw (security : ℕ) (color : Palette security) (coin : Bool)
    (shift : ℤ) (hshift : |shift| ≤ (Parameters.sourceCutoff security : ℤ) - 1) :
    FiniteDist (Palette security) :=
  (FiniteDist.uniform (Index security)).map (fun index => point security color coin index shift hshift)

/-- The complete midpoint convention uses one independent fair coin. -/
def shiftedAnchorLaw (security : ℕ) (color : Palette security)
    (shift : ℤ) (hshift : |shift| ≤ (Parameters.sourceCutoff security : ℤ) - 1) :
    FiniteDist (Palette security) :=
  (FiniteDist.uniform Bool).mix (fun coin => fixedCoinLaw security color coin shift hshift)

private theorem zero_shift_bound (security : ℕ) :
    |(0 : ℤ)| ≤ (Parameters.sourceCutoff security : ℤ) - 1 := by
  have h := sourceCutoff_pos security
  simp only [abs_zero]
  omega

def anchorLaw (security : ℕ) (color : Palette security) : FiniteDist (Palette security) :=
  shiftedAnchorLaw security color 0 (zero_shift_bound security)

theorem scalar_bound (security : ℕ) (sample : ScalarSample security) :
    |(sample : ℤ)| ≤ (Parameters.sourceCutoff security : ℤ) - 1 := by
  have h := Finset.mem_Icc.mp sample.property
  have hcut := sourceCutoff_pos security
  apply abs_le.mpr
  constructor <;> omega

/-- The current smoothed anchor is convolution by an independent actual
protected Gaussian scalar, implemented by its actual finite source draw. -/
def smoothedAnchorLaw (security : ℕ) (color : Palette security) : FiniteDist (Palette security) :=
  (scalarLaw security).mix (fun sample => shiftedAnchorLaw security color sample (scalar_bound security sample))

theorem anchorLaw_mass (security : ℕ) (color : Palette security) :
    ∑ output, (anchorLaw security color).weight output = 1 := FiniteDist.sum_one _

theorem smoothedAnchorLaw_mass (security : ℕ) (color : Palette security) :
    ∑ output, (smoothedAnchorLaw security color).weight output = 1 := FiniteDist.sum_one _

theorem fixedCoinLaw_zero_outside (security : ℕ) (color : Palette security) (coin : Bool)
    (shift : ℤ) (hshift : |shift| ≤ (Parameters.sourceCutoff security : ℤ) - 1)
    (output : Palette security) (hunsafe : ¬SafeColor security output) :
    (fixedCoinLaw security color coin shift hshift).weight output = 0 := by
  rw [fixedCoinLaw, FiniteDist.map_weight]
  apply Finset.sum_eq_zero
  intro index _
  have hne : point security color coin index shift hshift ≠ output := by
    intro hequal
    apply hunsafe
    rw [← hequal]
    exact point_safe security color coin index shift hshift
  simp only [if_neg hne]

theorem shiftedAnchorLaw_zero_outside (security : ℕ) (color : Palette security)
    (shift : ℤ) (hshift : |shift| ≤ (Parameters.sourceCutoff security : ℤ) - 1)
    (output : Palette security) (hunsafe : ¬SafeColor security output) :
    (shiftedAnchorLaw security color shift hshift).weight output = 0 := by
  simp only [shiftedAnchorLaw, FiniteDist.mix_weight,
    fixedCoinLaw_zero_outside security color _ shift hshift output hunsafe, mul_zero, Finset.sum_const_zero]

theorem anchorLaw_zero_outside (security : ℕ) (color output : Palette security)
    (hunsafe : ¬SafeColor security output) : (anchorLaw security color).weight output = 0 :=
  shiftedAnchorLaw_zero_outside security color 0 (zero_shift_bound security) output hunsafe

theorem smoothedAnchorLaw_zero_outside (security : ℕ) (color output : Palette security)
    (hunsafe : ¬SafeColor security output) : (smoothedAnchorLaw security color).weight output = 0 := by
  simp only [smoothedAnchorLaw, FiniteDist.mix_weight,
    shiftedAnchorLaw_zero_outside security color _ _ output hunsafe, mul_zero, Finset.sum_const_zero]

theorem fixedCoinLaw_height (security : ℕ) (color : Palette security) (coin : Bool)
    (shift : ℤ) (hshift : |shift| ≤ (Parameters.sourceCutoff security : ℤ) - 1)
    (output : Palette security) :
    (fixedCoinLaw security color coin shift hshift).weight output ≤
      1 / (Parameters.anchorWidth security : ℝ) := by
  rw [fixedCoinLaw, FiniteDist.map_weight]
  by_cases hexists : ∃ index, point security color coin index shift hshift = output
  · obtain ⟨index, hindex⟩ := hexists
    have heq (other : Index security) : point security color coin other shift hshift = output ↔ other = index := by
      constructor
      · intro hother
        exact point_index_injective security color coin shift hshift (hother.trans hindex.symm)
      · rintro rfl
        exact hindex
    simp only [heq, Finset.sum_ite_eq', Finset.mem_univ, if_true, FiniteDist.uniform_weight,
      Fintype.card_fin, one_div]
    exact le_rfl
  · have hnone (index : Index security) : point security color coin index shift hshift ≠ output :=
      fun hpoint => hexists ⟨index, hpoint⟩
    simp only [if_neg (hnone _), Finset.sum_const_zero]
    positivity

theorem shiftedAnchorLaw_height (security : ℕ) (color : Palette security)
    (shift : ℤ) (hshift : |shift| ≤ (Parameters.sourceCutoff security : ℤ) - 1)
    (output : Palette security) :
    (shiftedAnchorLaw security color shift hshift).weight output ≤
      1 / (Parameters.anchorWidth security : ℝ) := by
  rw [shiftedAnchorLaw, FiniteDist.mix_weight]
  calc
    _ ≤ ∑ coin, (FiniteDist.uniform Bool).weight coin * (1 / (Parameters.anchorWidth security : ℝ)) :=
      Finset.sum_le_sum (fun coin _ => mul_le_mul_of_nonneg_left
        (fixedCoinLaw_height security color coin shift hshift output) (FiniteDist.nonneg _ _))
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

theorem anchorLaw_height (security : ℕ) (color output : Palette security) :
    (anchorLaw security color).weight output ≤ 1 / (Parameters.anchorWidth security : ℝ) :=
  shiftedAnchorLaw_height security color 0 (zero_shift_bound security) output

theorem smoothedAnchorLaw_height (security : ℕ) (color output : Palette security) :
    (smoothedAnchorLaw security color).weight output ≤ 1 / (Parameters.anchorWidth security : ℝ) := by
  rw [smoothedAnchorLaw, FiniteDist.mix_weight]
  calc
    _ ≤ ∑ sample, (scalarLaw security).weight sample * (1 / (Parameters.anchorWidth security : ℝ)) :=
      Finset.sum_le_sum (fun sample _ => mul_le_mul_of_nonneg_left
        (shiftedAnchorLaw_height security color sample (scalar_bound security sample) output)
          (FiniteDist.nonneg _ _))
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

private theorem integer_fiber_sum_le_one (security : ℕ) (value : ℤ) :
    (∑ color : Palette security, if (color.val : ℤ) = value then (1 : ℝ) else 0) ≤ 1 := by
  by_cases hexists : ∃ color : Palette security, (color.val : ℤ) = value
  · obtain ⟨color, hcolor⟩ := hexists
    have heq (other : Palette security) : (other.val : ℤ) = value ↔ other = color := by
      constructor
      · intro hother
        apply Fin.ext
        omega
      · rintro rfl
        exact hcolor
    simp [heq]
  · have hnone (color : Palette security) : ¬(color.val : ℤ) = value :=
      fun hcolor => hexists ⟨color, hcolor⟩
    simp [hnone]

/-- For a fixed index and coin, each output can arise from at most one
input in each of the two inward directions. This includes the midpoint. -/
theorem point_row_count_le_two (security : ℕ) (coin : Bool) (index : Index security)
    (shift : ℤ) (hshift : |shift| ≤ (Parameters.sourceCutoff security : ℤ) - 1)
    (output : Palette security) :
    (∑ color : Palette security,
      if point security color coin index shift hshift = output then (1 : ℝ) else 0) ≤ 2 := by
  let positiveInput : ℤ := (Parameters.modulus security : ℤ) - 1 + offset security index + shift - output.val
  let negativeInput : ℤ := (Parameters.modulus security : ℤ) - 1 - offset security index + shift - output.val
  have hpoint (color : Palette security) :
      (if point security color coin index shift hshift = output then (1 : ℝ) else 0) ≤
        (if (color.val : ℤ) = positiveInput then (1 : ℝ) else 0) +
          (if (color.val : ℤ) = negativeInput then (1 : ℝ) else 0) := by
    by_cases hequal : point security color coin index shift hshift = output
    · have hvalue := congrArg (fun point : Palette security => (point.val : ℤ)) hequal
      change ((point security color coin index shift hshift).val : ℤ) = (output.val : ℤ) at hvalue
      rw [point_value] at hvalue
      unfold integerPoint at hvalue
      cases hdirection : positiveDirection security color coin
      · simp only [hdirection, Bool.false_eq_true, if_false] at hvalue
        have hinput : (color.val : ℤ) = negativeInput := by dsimp [negativeInput]; omega
        simp only [if_pos hequal, if_pos hinput]
        split_ifs <;> norm_num
      · simp only [hdirection, if_true] at hvalue
        have hinput : (color.val : ℤ) = positiveInput := by dsimp [positiveInput]; omega
        simp only [if_pos hequal, if_pos hinput]
        split_ifs <;> norm_num
    · simp only [if_neg hequal]
      split_ifs <;> norm_num
  calc
    _ ≤ ∑ color : Palette security,
        ((if (color.val : ℤ) = positiveInput then (1 : ℝ) else 0) +
          (if (color.val : ℤ) = negativeInput then (1 : ℝ) else 0)) :=
      Finset.sum_le_sum (fun color _ => hpoint color)
    _ ≤ _ := by
      rw [Finset.sum_add_distrib]
      linarith [integer_fiber_sum_le_one security positiveInput,
        integer_fiber_sum_le_one security negativeInput]

/-- The actual sign-column has row sum at most two, with no loss
depending on the palette or anchor width. -/
theorem fixedCoinLaw_row_sum_le_two (security : ℕ) (coin : Bool)
    (shift : ℤ) (hshift : |shift| ≤ (Parameters.sourceCutoff security : ℤ) - 1)
    (output : Palette security) :
    (∑ color, (fixedCoinLaw security color coin shift hshift).weight output) ≤ 2 := by
  simp only [fixedCoinLaw, FiniteDist.map_weight, FiniteDist.uniform_weight, Fintype.card_fin]
  rw [Finset.sum_comm]
  calc
    _ = ∑ index : Index security, (Parameters.anchorWidth security : ℝ)⁻¹ *
        ∑ color : Palette security,
          if point security color coin index shift hshift = output then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro index _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro color _
      split_ifs <;> simp
    _ ≤ ∑ _index : Index security, (Parameters.anchorWidth security : ℝ)⁻¹ * 2 :=
      Finset.sum_le_sum (fun index _ => mul_le_mul_of_nonneg_left
        (point_row_count_le_two security coin index shift hshift output) (by positivity))
    _ = 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have ha : (Parameters.anchorWidth security : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (anchorWidth_pos security).ne'
      field_simp

theorem shiftedAnchorLaw_row_sum_le_two (security : ℕ)
    (shift : ℤ) (hshift : |shift| ≤ (Parameters.sourceCutoff security : ℤ) - 1)
    (output : Palette security) :
    (∑ color, (shiftedAnchorLaw security color shift hshift).weight output) ≤ 2 := by
  simp only [shiftedAnchorLaw, FiniteDist.mix_weight]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  calc
    _ ≤ ∑ coin, (FiniteDist.uniform Bool).weight coin * 2 :=
      Finset.sum_le_sum (fun coin _ => mul_le_mul_of_nonneg_left
        (fixedCoinLaw_row_sum_le_two security coin shift hshift output) (FiniteDist.nonneg _ _))
    _ = 2 := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

theorem anchorLaw_row_sum_le_two (security : ℕ) (output : Palette security) :
    (∑ color, (anchorLaw security color).weight output) ≤ 2 :=
  shiftedAnchorLaw_row_sum_le_two security 0 (zero_shift_bound security) output

theorem smoothedAnchorLaw_row_sum_le_two (security : ℕ) (output : Palette security) :
    (∑ color, (smoothedAnchorLaw security color).weight output) ≤ 2 := by
  simp only [smoothedAnchorLaw, FiniteDist.mix_weight]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  calc
    _ ≤ ∑ sample, (scalarLaw security).weight sample * 2 :=
      Finset.sum_le_sum (fun sample _ => mul_le_mul_of_nonneg_left
        (shiftedAnchorLaw_row_sum_le_two security sample (scalar_bound security sample) output)
          (FiniteDist.nonneg _ _))
    _ = 2 := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

end

end CurrentAFT.InwardAnchor
