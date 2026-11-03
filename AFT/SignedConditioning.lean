import AFT.RootSlice
import AFT.TotalVariation

/-! # Restriction and normalization of an actual signed output law -/

namespace AFT.SignedConditioning

open scoped BigOperators Classical

noncomputable section

variable {Color : Type*} [Fintype Color]

def restricted (mass : Color → ℝ) (event : Color → Prop) (color : Color) : ℝ :=
  if event color then mass color else 0

def conditionalMass (mass : Color → ℝ) (event : Color → Prop) (color : Color) : ℝ :=
  restricted mass event color / ∑ x, restricted mass event x

theorem restriction_l1_le (first second : Color → ℝ) (event : Color → Prop) :
    (∑ color, |restricted first event color - restricted second event color|) ≤
      ∑ color, |first color - second color| := by
  apply Finset.sum_le_sum
  intro color _
  unfold restricted
  split_ifs <;> simp [abs_nonneg]

theorem mass_difference_le_l1 (first second : Color → ℝ) :
    |(∑ color, first color) - ∑ color, second color| ≤ ∑ color, |first color - second color| := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _

/-- Normalizing a signed mass loses at most twice its L1 error divided by
its actual positive mass. Only the reference mass needs pointwise positivity. -/
theorem normalized_signed_l1 (signed reference : Color → ℝ)
    (href : ∀ color, 0 ≤ reference color)
    (hsigned : 0 < ∑ color, signed color) (hreference : 0 < ∑ color, reference color) :
    (∑ color, |signed color / (∑ x, signed x) - reference color / (∑ x, reference x)|) ≤
      2 * (∑ color, |signed color - reference color|) / (∑ color, signed color) := by
  let total := ∑ color, signed color
  let referenceTotal := ∑ color, reference color
  let error := ∑ color, |signed color - reference color|
  have hmass : |referenceTotal - total| ≤ error := by
    simpa only [abs_sub_comm] using mass_difference_le_l1 signed reference
  have hpoint (color) : |signed color / total - reference color / referenceTotal| ≤
      |signed color - reference color| / total +
        reference color * |referenceTotal - total| / (total * referenceTotal) := by
    have heq : signed color / total - reference color / referenceTotal =
        (signed color - reference color) / total +
          reference color * (referenceTotal - total) / (total * referenceTotal) := by
      dsimp only [total, referenceTotal]
      field_simp
      ring
    rw [heq]
    exact (abs_add_le _ _).trans_eq (by
      rw [abs_div, abs_div, abs_mul, abs_of_pos hsigned,
        abs_of_pos (mul_pos hsigned hreference), abs_of_nonneg (href color)])
  have hh := Finset.sum_le_sum (fun color (_ : color ∈ Finset.univ) => hpoint color)
  simp only [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul] at hh
  have heq : (∑ color, |signed color - reference color|) / total +
      (∑ color, reference color) * |referenceTotal - total| / (total * referenceTotal) =
        (error + |referenceTotal - total|) / total := by
    dsimp only [error, total, referenceTotal]
    field_simp
  rw [heq] at hh
  apply hh.trans
  apply div_le_div_of_nonneg_right _ hsigned.le
  linarith

/-- A target event of probability at least `lower` remains positive under
an L1 perturbation at most `lower/2`. This includes signed perturbations. -/
theorem conditional_signed_l1 (signed : Color → ℝ) (reference : FiniteDist Color)
    (event : Color → Prop) (lower error : ℝ) (hlower : 0 < lower)
    (hevent : lower ≤ reference.eventMass event)
    (herror : (∑ color, |signed color - reference.weight color|) ≤ error)
    (hsmall : error ≤ lower / 2) :
    0 < (∑ color, restricted signed event color) ∧
      (∑ color, |conditionalMass signed event color - conditionalMass reference.weight event color|) ≤
        4 * error / lower := by
  let first := restricted signed event
  let second := restricted reference.weight event
  have hl1 : (∑ color, |first color - second color|) ≤ error :=
    (restriction_l1_le signed reference.weight event).trans herror
  have hmass := (mass_difference_le_l1 first second).trans hl1
  have hsecond : ∑ color, second color = reference.eventMass event := rfl
  have hfirst : lower / 2 ≤ ∑ color, first color := by
    have hh := (abs_le.mp hmass).1
    rw [hsecond] at hh
    linarith
  have hpos : 0 < ∑ color, first color := lt_of_lt_of_le (by positivity) hfirst
  refine ⟨hpos, ?_⟩
  have hnorm := normalized_signed_l1 first second
    (fun color => by dsimp only [second, restricted]; split_ifs; exact reference.nonneg color; rfl)
    hpos (by rw [hsecond]; exact hlower.trans_le hevent)
  have he0 : 0 ≤ error := (Finset.sum_nonneg fun color _ => abs_nonneg (first color - second color)).trans hl1
  apply hnorm.trans
  calc
    _ ≤ (2 * error) / (∑ color, first color) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hl1 (by norm_num)) hpos.le
    _ ≤ (2 * error) / (lower / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hfirst
    _ = _ := by ring

end

end AFT.SignedConditioning
