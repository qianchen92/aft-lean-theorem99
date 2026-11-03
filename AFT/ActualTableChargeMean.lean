import AFT.RepresentedLocalSum
import AFT.ActualChargeTransfer

/-! # The literal control table on the one actual full center-charge slice: first moment -/
namespace AFT.V7Calibration
open GaussianSource Filter FiniteDist RepresentedPolynomial
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance actualTableChargeMeanFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance actualTableChargeMeanSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- All local monomials and all of their injection placements are evaluated
on the same full charge slice. The primary word is arbitrary and held fixed. -/
theorem actual_table_charge_mean_transfer_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,
      (Parameters.legs n : ℝ) / (2 * Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2 * (Parameters.legs n : ℝ) / Parameters.dimension n) (order : ℕ) :
    ∀ᶠ n in atTop, ∀ required : Fin (Parameters.modulus n),
      ∃ hpos : 0 < ((actualBodyLaw C n (beta n)).sumLaw (Parameters.bodies n)).weight required,
      ∀ primaryPool bodyPool : ℕ, 0 < primaryPool → 0 < bodyPool → order ≤ primaryPool → order ≤ bodyPool →
      ∀ table : Table (InputSeed (Fin (Parameters.modulus n))),
      (∀ powers ∈ table.support, finiteControlCount (monomialOccurrences powers) ≤ order) →
      ∀ bodyEmbedding : Fin bodyPool ↪ Fin (Parameters.bodies n),
      ∀ primaryWord : Fin primaryPool → Fin (Parameters.modulus n),
      |(chargeWordLaw (Slot := Fin (Parameters.bodies n)) (actualBodyLaw C n (beta n)) required (by simpa using hpos)).expectation
          (fun word => tableInputStatistic primaryPool bodyPool table (Sum.elim primaryWord (word ∘ bodyEmbedding)) ) -
        (independent (fun _ : Fin (Parameters.bodies n) => actualBodyLaw C n (beta n))).expectation
          (fun word => tableInputStatistic primaryPool bodyPool table (Sum.elim primaryWord (word ∘ bodyEmbedding)) )| ≤
        actualChargeError C n (beta n) order *
          tableInputEnvelope (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
            primaryPool bodyPool ((n : ℝ)^2) table order  := by
  filter_upwards [actual_charge_all_local_ratios_eventually C hC beta hbeta order,
    eventually_ge_atTop 2] with n ht hn required
  obtain ⟨hpos, hratio⟩ := ht required
  refine ⟨hpos, ?_⟩
  intro primaryPool bodyPool hp hb hpl hbl table ho bodyEmbedding primaryWord
  have hr : (1 : ℝ) ≤ (n : ℝ)^2 := one_le_pow₀ (by exact_mod_cast (show 1 ≤ n by omega))
  let term (index : TableLocalIndex primaryPool bodyPool table) (word : Fin (Parameters.bodies n) → Fin (Parameters.modulus n)) :=
    tableLocalTerm primaryPool bodyPool table index (Sum.elim primaryWord (word ∘ bodyEmbedding))
  let bound := tableLocalBound (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) primaryPool bodyPool ((n : ℝ)^2) table order
  have hh := chargeWordLaw_local_sum_power_deviation
    (Slot := Fin (Parameters.bodies n)) (actualBodyLaw C n (beta n)) required (by simpa using hpos)
    (tableBodyScope primaryPool bodyPool table bodyEmbedding) term
    (tableLocalTerm_body_depends primaryPool bodyPool table bodyEmbedding primaryWord) bound
    (tableLocalBound_nonneg _ _ _ _ _ (sq_nonneg _) _ _)
    (fun index word => tableLocalTerm_bound _ _ primaryPool bodyPool hp hb _ hr table order ho index _)
    order 1
    (fun index => tableBodyScope_card_le primaryPool bodyPool table bodyEmbedding index order (ho index.1.val index.1.property))
    (actualChargeError C n (beta n) order) (actualChargeError_nonneg ..)
    (by simpa only [Fintype.card_fin, one_mul] using hratio)
  have he (word) : (∑ index, term index word) =
      tableInputStatistic primaryPool bodyPool table (Sum.elim primaryWord (word ∘ bodyEmbedding)) :=
    (tableInputStatistic_local_sum primaryPool bodyPool table _).symm
  have hbound : (∑ index, bound index) =
      tableInputEnvelope (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) primaryPool bodyPool ((n : ℝ)^2) table order :=
    tableLocalBound_sum _ _ _ _ _ table order ho hpl hbl
  simpa only [he, hbound, pow_one] using hh

end
end AFT.V7Calibration
