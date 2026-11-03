import CurrentAFT.CurrentReferenceDraw
import AFT.FiniteProductVariation

/-! Actual approximation bounds for the executed primary and safe-body draws.
The table-precision conditions are the explicit current primary-positivity
budget, rather than an assumption on an unspecified proposal oracle. -/
namespace CurrentAFT.CurrentReferenceDrawRates
open AFT ProposalPrimary CurrentReferenceDraw
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 600000
noncomputable local instance safeFintype (security : ℕ) : Fintype (ActualControls.SafePalette security) := by
  classical
  exact Subtype.fintype _

theorem primary_table_l1 (security bits : ℕ)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    (∑ color, |(RationalProposalProgram.approximatePrimaryLaw security bits).weight color -
      (primaryLaw security).weight color|) ≤
      (Parameters.modulus security : ℝ) * (64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits)) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun color _ =>
    RationalProposalProgram.primary_error security bits color hprecision hbudget)
  simpa only [FiniteDist.weight, RationalProposalProgram.approximatePrimaryLaw, primaryLaw,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h

theorem body_table_l1 (security bits : ℕ)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    (∑ color : ActualControls.SafePalette security,
      |(RationalProposalProgram.approximateBodyReference security bits).weight color -
        (ActualControls.bodyReference security).weight color|) ≤
      (Parameters.modulus security : ℝ) * ((64 * (Parameters.base security : ℝ) * Parameters.dimension security *
        Parameters.modulus security + 2) * (1 / (2 : ℝ)^bits)) := by
  let error := (64 * (Parameters.base security : ℝ) * Parameters.dimension security * Parameters.modulus security + 2) *
    (1 / (2 : ℝ)^bits)
  have he : 0 ≤ error := by dsimp [error]; positivity
  have h := Finset.sum_le_sum (s := Finset.univ) (fun color : ActualControls.SafePalette security => fun _ =>
    RationalProposalProgram.center_error security bits color.val hprecision hbudget)
  have hc : Fintype.card (ActualControls.SafePalette security) ≤ Parameters.modulus security := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
      (Subtype.val : ActualControls.SafePalette security → FirstHistogram.Palette security) Subtype.val_injective
  change (∑ color : ActualControls.SafePalette security,
    |(RationalProposalProgram.center security bits color.val.val : ℝ) - centerProfile security color.val|) ≤ _
  calc
    _ ≤ (Fintype.card (ActualControls.SafePalette security) : ℝ) * error := by
      simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h
    _ ≤ (Parameters.modulus security : ℝ) * error := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) he

theorem primary_draw_l1 (security tableBits drawBits : ℕ) (cache : Cache security tableBits)
    (hprecision : 1 / (2 : ℝ)^tableBits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^tableBits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    (∑ color, |(primaryDrawLaw security tableBits drawBits cache).weight color - (primaryLaw security).weight color|) ≤
      1 / (2 : ℝ)^drawBits + (Parameters.modulus security : ℝ) *
        (64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^tableBits)) := by
  apply le_trans _ (add_le_add (primaryDraw_rounding security tableBits drawBits cache)
    (primary_table_l1 security tableBits hprecision hbudget))
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun color _ => abs_sub_le _
    ((RationalProposalProgram.approximatePrimaryLaw security tableBits).weight color) _)

theorem body_draw_l1 (security tableBits drawBits : ℕ) (cache : Cache security tableBits)
    (hprecision : 1 / (2 : ℝ)^tableBits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^tableBits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    (∑ color, |(bodyDrawLaw security tableBits drawBits cache).weight color - (ActualControls.bodyReference security).weight color|) ≤
      1 / (2 : ℝ)^drawBits + (Parameters.modulus security : ℝ) *
        ((64 * (Parameters.base security : ℝ) * Parameters.dimension security * Parameters.modulus security + 2) *
          (1 / (2 : ℝ)^tableBits)) := by
  apply le_trans _ (add_le_add (bodyDraw_rounding security tableBits drawBits cache)
    (body_table_l1 security tableBits hprecision hbudget))
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun color _ => abs_sub_le _
    ((RationalProposalProgram.approximateBodyReference security tableBits).weight color) _)

end
end CurrentAFT.CurrentReferenceDrawRates
