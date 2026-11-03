import CurrentAFT.CurrentFlagPublicProgram

/-! Actual canonical branch laws on the generated finite chart array. -/

namespace CurrentAFT.CurrentFlagIdealArrays

open AFT AFT.BoundaryCalibration AffineFlagCalibration CurrentFlagMarkedArray
open CurrentRationalFlagLaw AFT.BinaryArithmetic
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 400000

local instance idealArrayPrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩
local instance idealArrayNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩

def model (security : ℕ) (baseline : ℤ) (hbaseline : |baseline| ≤ legOffsetBound security)
    (mark : Fin (Parameters.modulus security)) :=
  CurrentFlagProgram.current security baseline hbaseline ((ZMod.finEquiv (Parameters.modulus security)) mark)
    (1 / 2 : ℚ) (by norm_num) (by norm_num)

def regularLaw (security : ℕ) (baseline : ℤ) (hbaseline : |baseline| ≤ legOffsetBound security)
    (mark : Fin (Parameters.modulus security)) :
    FiniteDist (Fin (Parameters.modulus security * (Parameters.modulus security * Parameters.modulus security))) :=
  (model security baseline hbaseline mark).model.regular.map (finiteChartEquiv (Parameters.modulus security)).symm

def markedLaw (security : ℕ) (baseline : ℤ) (hbaseline : |baseline| ≤ legOffsetBound security)
    (mark : Fin (Parameters.modulus security)) :
    FiniteDist (Fin (Parameters.modulus security * (Parameters.modulus security * Parameters.modulus security))) :=
  (model security baseline hbaseline mark).model.marked.map (finiteChartEquiv (Parameters.modulus security)).symm

theorem regular_weight (security : ℕ) (baseline : ℤ) (hbaseline : |baseline| ≤ legOffsetBound security)
    (mark : Fin (Parameters.modulus security))
    (point : Fin (Parameters.modulus security * (Parameters.modulus security * Parameters.modulus security))) :
    (regularLaw security baseline hbaseline mark).weight point =
      (CurrentFlagProgram.regularDensity
        (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security))
        (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline)
        ((ZMod.finEquiv (Parameters.modulus security)) mark) (1 / 2)
        (finiteChartEquiv (Parameters.modulus security) point) : ℝ) /
      (Parameters.modulus security * (Parameters.modulus security * Parameters.modulus security)) := by
  rw [regularLaw, FiniteDist.map_equiv_weight]
  have ht := (model security baseline hbaseline mark).table_cast
    (false, finiteChartEquiv (Parameters.modulus security) point)
  change ((CurrentFlagProgram.current security baseline hbaseline _ (1 / 2) _ _).table _ : ℝ) = _ at ht
  rw [current_table, CurrentFlagProgram.table] at ht
  rw [(model security baseline hbaseline mark).model.decomposition] at ht
  norm_num only [Bool.false_eq_true, if_false, Rat.cast_sub, Rat.cast_one, Rat.cast_mul, Rat.cast_inv,
    Rat.cast_natCast, Rat.cast_div, Rat.cast_ofNat] at ht
  have hc := Fintype.card_congr (finiteChartEquiv (Parameters.modulus security))
  simp only [Fintype.card_fin] at hc
  rw [← hc] at ht
  simp only [Equiv.symm_symm, Nat.cast_mul, div_eq_mul_inv] at ht ⊢
  nlinarith [ht]

theorem marked_weight (security : ℕ) (baseline : ℤ) (hbaseline : |baseline| ≤ legOffsetBound security)
    (mark : Fin (Parameters.modulus security))
    (point : Fin (Parameters.modulus security * (Parameters.modulus security * Parameters.modulus security))) :
    (markedLaw security baseline hbaseline mark).weight point =
      (chartSpikeProgram (Parameters.modulus security * (Parameters.modulus security * Parameters.modulus security))
        (fiber (finiteChartEquiv (Parameters.modulus security))
          (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security))
          (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline)
          ((ZMod.finEquiv (Parameters.modulus security)) mark)) point : ℝ) /
      (Parameters.modulus security * (Parameters.modulus security * Parameters.modulus security)) := by
  rw [markedLaw, FiniteDist.map_equiv_weight, spike_eq]
  have ht := (model security baseline hbaseline mark).table_cast
    (true, finiteChartEquiv (Parameters.modulus security) point)
  change ((CurrentFlagProgram.current security baseline hbaseline _ (1 / 2) _ _).table _ : ℝ) = _ at ht
  rw [current_table, CurrentFlagProgram.table] at ht
  rw [(model security baseline hbaseline mark).model.decomposition] at ht
  norm_num only [if_true, Rat.cast_mul, Rat.cast_inv, Rat.cast_natCast, Rat.cast_div,
    Rat.cast_one, Rat.cast_ofNat] at ht
  have hc := Fintype.card_congr (finiteChartEquiv (Parameters.modulus security))
  simp only [Fintype.card_fin] at hc
  rw [← hc] at ht
  simp only [Equiv.symm_symm, Nat.cast_mul, div_eq_mul_inv] at ht ⊢
  nlinarith [ht]

end
end CurrentAFT.CurrentFlagIdealArrays
