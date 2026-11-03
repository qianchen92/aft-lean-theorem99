import AFT.PairedTableEnvelope
import AFT.ActualPairedPublic
import AFT.ActualChargeTransfer

/-! # The complete paired public weight on the one actual full body-charge slice -/
namespace AFT.V7Calibration
open GaussianSource Filter FiniteDist RepresentedPolynomial
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance actualPairedChargeMomentFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance actualPairedChargeMomentSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- Every paired compensator is counted among the actual body centers.
The charge error is uniform in all primary marks, the residue, the pool
embedding, and the original finite table. -/
theorem actual_paired_table_charge_power_transfer_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,
      (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) (order power : ℕ) :
    ∀ᶠ n in atTop, ∀ required : Fin (Parameters.modulus n),
      ∃ hpos : 0 < ((actualBodyLaw C n (beta n)).sumLaw (Parameters.bodies n)).weight required,
      ∀ primaryPool bodyPool : ℕ, 0 < primaryPool → 0 < bodyPool → order ≤ primaryPool → order ≤ bodyPool →
      ∀ table : Table (InputSeed (Fin (Parameters.modulus n))),
      (∀ powers ∈ table.support, finiteControlCount (monomialOccurrences powers) ≤ order) →
      ∀ embedding : (Fin primaryPool ⊕ Fin bodyPool) ↪ Fin (Parameters.bodies n),
      ∀ marks : (Fin primaryPool ⊕ Fin bodyPool) → Fin (Parameters.modulus n),
      let score := fun centers => tablePairedStatistic (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
        (fun color center => publicAnchorKernel (Parameters.modulus n) (Parameters.anchorWidth n) color center.val)
        (v7Activation C n) primaryPool bodyPool table (pairedRetainedWord primaryPool bodyPool embedding marks centers)
      |(chargeWordLaw (Slot := Fin (Parameters.bodies n)) (actualBodyLaw C n (beta n)) required (by simpa using hpos)).expectation
          (fun centers => score centers ^ power) -
        (independent (fun _ : Fin (Parameters.bodies n) => actualBodyLaw C n (beta n))).expectation
          (fun centers => score centers ^ power)| ≤
        actualChargeError C n (beta n) (power*order) *
          tablePairedEnvelope 772 (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
            primaryPool bodyPool ((n : ℝ)^2) table order ^ power := by
  filter_upwards [actual_charge_all_local_ratios_eventually C hC beta hbeta (power*order),
    actual_public_anchor_comparison_eventually C hC beta hbeta, eventually_ge_atTop 2]
    with n ht hcompare hn required
  obtain ⟨hpos, hratio⟩ := ht required
  refine ⟨hpos, ?_⟩
  intro primaryPool bodyPool hp hb hpl hbl table ho embedding marks
  dsimp only
  let primary := actualPrimaryLaw C n (beta n)
  let body := actualBodyLaw C n (beta n)
  let anchor := fun color center : Fin (Parameters.modulus n) => publicAnchorKernel (Parameters.modulus n) (Parameters.anchorWidth n) color center.val
  have hr : (1 : ℝ) ≤ (n : ℝ)^2 := one_le_pow₀ (by exact_mod_cast (show 1 ≤ n by omega))
  let term (index : TableLocalIndex primaryPool bodyPool table) (centers : Fin (Parameters.bodies n) → Fin (Parameters.modulus n)) :=
    tablePairedLocalTerm primary body anchor (v7Activation C n) primaryPool bodyPool table index
      (pairedRetainedWord primaryPool bodyPool embedding marks centers)
  let bound (index : TableLocalIndex primaryPool bodyPool table) :=
    (774 : ℝ)^(2*order) * tableLocalBound primary body primaryPool bodyPool ((n : ℝ)^2) table order index
  have hbound (index) : 0 ≤ bound index := mul_nonneg (by positivity)
    (tableLocalBound_nonneg _ _ _ _ _ (sq_nonneg _) _ _ index)
  have hpoint (index) (centers) : |term index centers| ≤ bound index := by
    simpa only [show (772 : ℝ)+2=774 by norm_num] using tablePairedLocalTerm_bound primary body anchor (v7Activation C n) 772
      (activation_positive _ _ _ _ (legFeatureCount_positive C n hC (by omega))).le
      (activation_le_one _ _ _ _) (by norm_num) (fun color center => publicAnchorKernel_nonneg _ _ _ _)
      (fun color => (actual_anchor_safe_mass n color).1) hcompare primaryPool bodyPool hp hb _ hr table order ho index _
  have hh := chargeWordLaw_local_sum_power_deviation
    (Slot := Fin (Parameters.bodies n)) body required (by simpa using hpos)
    (tablePairedBodyScope primaryPool bodyPool table embedding) term
    (tablePairedLocalTerm_body_depends primary body anchor (v7Activation C n) primaryPool bodyPool table embedding marks)
    bound hbound hpoint order power
    (fun index => tablePairedBodyScope_card_le primaryPool bodyPool table embedding index order (ho index.1.val index.1.property))
    (actualChargeError C n (beta n) (power*order)) (actualChargeError_nonneg ..)
    (by simpa only [Fintype.card_fin] using hratio)
  have he (centers) : (∑ index, term index centers) = tablePairedStatistic primary body anchor (v7Activation C n)
      primaryPool bodyPool table (pairedRetainedWord primaryPool bodyPool embedding marks centers) :=
    (tablePairedStatistic_local_sum primary body anchor (v7Activation C n) primaryPool bodyPool table _).symm
  have htotal : (∑ index, bound index) = tablePairedEnvelope 772 primary body primaryPool bodyPool ((n : ℝ)^2) table order := by
    unfold bound tablePairedEnvelope
    rw [← Finset.mul_sum, tableLocalBound_sum primary body primaryPool bodyPool _ table order ho hpl hbl]
    norm_num
    rfl
  simpa only [he, htotal] using hh
end
end AFT.V7Calibration
