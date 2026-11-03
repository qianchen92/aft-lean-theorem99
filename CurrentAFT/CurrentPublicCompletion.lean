import CurrentAFT.CurrentChartsDraw
import CurrentAFT.CurrentEdgeDrawProgram

/-!
# Completing a finite public-core result into a full affine sample

The cached leg inputs are read by the chart program.  They are uniquely
determined by the public core, and their equality is a proof field.  The
completion observes no hidden source.  Failed core attempts remain `none`.
-/

namespace CurrentAFT.CurrentPublicCompletion

open AFT GaussianSource RationalNumerics BinaryArithmetic AFT.RationalRejectionProgram
open CurrentAffineData ActualPublicCharge
open scoped BigOperators
set_option maxHeartbeats 600000
attribute [local irreducible] Parameters.legCount CurrentChartsDraw.draw CurrentEdgeDrawProgram.draw

structure CachedCore (security : ℕ) where
  core : Core security
  inputs : CurrentChartsDraw.InputVector security
  correct : inputs = CurrentChartsDraw.inputsOfCore security core

abbrev Tapes (security drawBits edgeBits : ℕ) :=
  CurrentChartsDraw.Tapes security drawBits × (Fin (windowTicketBits (DiffuseProfiles.edgeCutoff security) edgeBits) → Fin 2)

def complete (security : ℕ) (input : Option (CachedCore security)) (precisionBits drawBits edgeBits : ℕ)
    (word : Tapes security drawBits edgeBits) : CountedValue (Option (CurrentPublicAffineSample.Sample security)) :=
  match input with
  | none => ⟨none, 1⟩
  | some cached =>
    let charts := CurrentChartsDraw.draw security cached.inputs precisionBits drawBits word.1
    let edge := CurrentEdgeDrawProgram.draw security edgeBits word.2
    ⟨some ((cached.core, charts.value), edge.value), charts.work + edge.work + 3⟩

theorem complete_none (security precisionBits drawBits edgeBits : ℕ) (word : Tapes security drawBits edgeBits) :
    (complete security none precisionBits drawBits edgeBits word).value = none := rfl

theorem complete_some (security : ℕ) (cached : CachedCore security) (precisionBits drawBits edgeBits : ℕ)
    (word : Tapes security drawBits edgeBits) :
    (complete security (some cached) precisionBits drawBits edgeBits word).value =
      some ((cached.core, (CurrentChartsDraw.draw security cached.inputs precisionBits drawBits word.1).value),
        (CurrentEdgeDrawProgram.draw security edgeBits word.2).value) := rfl

noncomputable section
open scoped Classical

def coreEquiv (security : ℕ) : CachedCore security ≃ Core security where
  toFun cached := cached.core
  invFun core := ⟨core, CurrentChartsDraw.inputsOfCore security core, rfl⟩
  left_inv cached := by
    cases cached with
    | mk core inputs correct => cases correct; rfl
  right_inv _ := rfl

instance cachedCoreFintype (security : ℕ) : Fintype (CachedCore security) :=
  Fintype.ofEquiv (Core security) (coreEquiv security).symm

def tapeLaw (security drawBits edgeBits : ℕ) : FiniteDist (Tapes security drawBits edgeBits) :=
  (CurrentChartsDraw.tapeLaw security drawBits).prod
    (FiniteDist.independent (fun _ : Fin (windowTicketBits (DiffuseProfiles.edgeCutoff security) edgeBits) => FiniteDist.uniform (Fin 2)))

def kernel (security precisionBits drawBits edgeBits : ℕ) (input : Option (CachedCore security)) :
    FiniteDist (Option (CurrentPublicAffineSample.Sample security)) :=
  (tapeLaw security drawBits edgeBits).map (fun word => (complete security input precisionBits drawBits edgeBits word).value)

def targetKernel (security : ℕ) : Option (CachedCore security) → FiniteDist (Option (CurrentPublicAffineSample.Sample security))
  | none => CanonicalMoments.pointLaw none
  | some cached => ((CurrentPublicAffineSample.chartsLaw security cached.core).prod (DiffuseProfiles.edgeLaw security)).map
    (fun pair => some ((cached.core, pair.1), pair.2))

def errorBound (security precisionBits drawBits edgeBits : ℕ) : ℝ :=
  (Parameters.legCount security : ℝ) * (1 / (2 : ℝ) ^ drawBits + 4 * (1 / (2 : ℝ) ^ precisionBits)) +
    1 / (2 : ℝ) ^ edgeBits

theorem kernel_none (security precisionBits drawBits edgeBits : ℕ) :
    kernel security precisionBits drawBits edgeBits none = targetKernel security none := by
  ext point
  cases point <;> simp [kernel, complete_none, targetKernel, CanonicalMoments.pointLaw, FiniteDist.map_const_weight]

theorem kernel_some (security : ℕ) (cached : CachedCore security) (precisionBits drawBits edgeBits : ℕ) :
    kernel security precisionBits drawBits edgeBits (some cached) =
      (((CurrentChartsDraw.tapeLaw security drawBits).map
        (fun word => (CurrentChartsDraw.draw security cached.inputs precisionBits drawBits word).value)).prod
        ((FiniteDist.independent (fun _ : Fin (windowTicketBits (DiffuseProfiles.edgeCutoff security) edgeBits) => FiniteDist.uniform (Fin 2))).map
          (fun word => (CurrentEdgeDrawProgram.draw security edgeBits word).value))).map
        (fun pair => some ((cached.core, pair.1), pair.2)) := by
  simp only [kernel, tapeLaw, complete_some]
  rw [← FiniteDist.prod_map_functions, FiniteDist.map_map]

theorem completion_l1 (security precisionBits drawBits edgeBits : ℕ) (hprecision : 1 ≤ precisionBits)
    (input : Option (CachedCore security)) :
    (∑ sample, |(kernel security precisionBits drawBits edgeBits input).weight sample -
      (targetKernel security input).weight sample|) ≤ errorBound security precisionBits drawBits edgeBits := by
  cases input with
  | none =>
    rw [kernel_none]
    simp only [sub_self, abs_zero, Finset.sum_const_zero]
    unfold errorBound
    positivity
  | some cached =>
    rw [kernel_some]
    let approxCharts := (CurrentChartsDraw.tapeLaw security drawBits).map
      (fun word => (CurrentChartsDraw.draw security cached.inputs precisionBits drawBits word).value)
    let approxEdge := (FiniteDist.independent (fun _ : Fin (windowTicketBits (DiffuseProfiles.edgeCutoff security) edgeBits) => FiniteDist.uniform (Fin 2))).map
      (fun word => (CurrentEdgeDrawProgram.draw security edgeBits word).value)
    let exactCharts := CurrentPublicAffineSample.chartsLaw security cached.core
    let exactEdge := DiffuseProfiles.edgeLaw security
    have hm := FiniteDist.l1_map_le (approxCharts.prod approxEdge) (exactCharts.prod exactEdge)
      (fun pair => some ((cached.core, pair.1), pair.2))
    have hp := FiniteDist.l1_prod_le approxCharts exactCharts approxEdge exactEdge
    have hc := CurrentChartsDraw.core_draw_l1 security cached.core precisionBits drawBits hprecision
    rw [← cached.correct] at hc
    exact hm.trans (hp.trans (add_le_add hc (CurrentEdgeDrawProgram.draw_l1 security edgeBits)))

end
end CurrentAFT.CurrentPublicCompletion
