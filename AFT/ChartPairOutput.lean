import AFT.V7ActualChart
import AFT.V7SafePairInput
import AFT.TrimmedPair

/-! # Actual affine-chart joint endpoint output laws -/

namespace AFT

open scoped BigOperators Classical

noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance chartOutputFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

namespace FiniteDist

/-- A deterministic companion retains the entire joint pair law. -/
theorem graph_weight {Color Other : Type*} [Fintype Color] [Fintype Other]
    (p : FiniteDist Color) (companion : Color → Other) (first : Color) (second : Other) :
    (p.map (fun color => (color, companion color))).weight (first,second) =
      p.weight first * (if second = companion first then 1 else 0) := by
  simp only [map_weight, Prod.mk.injEq, ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases h : second = companion first <;> simp [h, eq_comm]

end FiniteDist

namespace BoundaryCalibration

open GaussianSource Filter
open scoped Topology
attribute [local instance] actualModulusNeZero
local instance chartOutputFieldDecEq (parameter : ℕ) : DecidableEq (ZMod (Parameters.modulus parameter)) := Classical.decEq _

def chartPaletteFeature (cutoffScale : ℝ) (parameter : ℕ) (input : V7Input cutoffScale parameter)
    (chart : Chart (ZMod (Parameters.modulus parameter))) : Fin (Parameters.modulus parameter) :=
  (ZMod.finEquiv (Parameters.modulus parameter)).symm
    (feature ((input.1 : ℤ) : ZMod (Parameters.modulus parameter)) ((input.2 : ℤ) : ZMod (Parameters.modulus parameter)) chart)

/-- Draw the actual chart, evaluate the protected feature, and use the
required integer pair sum for its companion. -/
def chartPairOutput (cutoffScale : ℝ) (parameter : ℕ) (baseline : ℤ)
    (chartLaw : FiniteDist (Chart (ZMod (Parameters.modulus parameter))))
    (input : V7Input cutoffScale parameter) : FiniteDist (Fin (Parameters.modulus parameter) × Fin (Parameters.modulus parameter)) :=
  (chartLaw.map (chartPaletteFeature cutoffScale parameter input)).map
    (fun first => (first, paletteEmbedding parameter ((Parameters.modulus parameter : ℤ) - 1 + baseline - input.2 - first.val)))

theorem fieldPalette_uniform (parameter : ℕ) (boundary shift : ℤ) (hb : 0 ≤ boundary)
    (color : Fin (Parameters.modulus parameter)) :
    (if (ZMod.finEquiv (Parameters.modulus parameter)) color ∈ fieldPalette (Parameters.modulus parameter) boundary shift
      then ((fieldPalette (Parameters.modulus parameter) boundary shift).card : ℝ)⁻¹ else 0) =
      TrimmedSlice.law (Parameters.modulus parameter) boundary shift color.val := by
  have hm : (ZMod.finEquiv (Parameters.modulus parameter)) color ∈ fieldPalette (Parameters.modulus parameter) boundary shift ↔
      color ∈ TrimmedSlice.paletteSlice (Parameters.modulus parameter) boundary shift := by
    constructor
    · intro h
      obtain ⟨other, ho, he⟩ := Finset.mem_map.mp h
      have he' : other = color := (ZMod.finEquiv (Parameters.modulus parameter)).injective he
      exact he' ▸ ho
    · intro h
      exact Finset.mem_map.mpr ⟨color, h, rfl⟩
  simp only [hm]
  rw [fieldPalette, Finset.card_map, TrimmedSlice.paletteSlice_card _ _ _ hb]
  simp only [TrimmedSlice.paletteSlice, Finset.mem_filter, Finset.mem_univ, true_and,
    TrimmedSlice.law, TrimmedSlice.slice_card]

theorem chartPaletteFeature_weight (cutoffScale : ℝ) (parameter : ℕ)
    (chartLaw : FiniteDist (Chart (ZMod (Parameters.modulus parameter))))
    (input : V7Input cutoffScale parameter) (color : Fin (Parameters.modulus parameter)) :
    (chartLaw.map (chartPaletteFeature cutoffScale parameter input)).weight color =
      (chartLaw.map (feature ((input.1 : ℤ) : ZMod (Parameters.modulus parameter))
        ((input.2 : ℤ) : ZMod (Parameters.modulus parameter)))).weight
          ((ZMod.finEquiv (Parameters.modulus parameter)) color) := by
  have hh := FiniteDist.map_equiv_weight
    (chartLaw.map (feature ((input.1 : ℤ) : ZMod (Parameters.modulus parameter))
      ((input.2 : ℤ) : ZMod (Parameters.modulus parameter))))
    (ZMod.finEquiv (Parameters.modulus parameter)).symm.toEquiv color
  rw [FiniteDist.map_map] at hh
  exact hh

/-- Safe trimmed endpoints have exactly the integer companion relation;
reducing through the field introduces no extra wraparound mass. -/
theorem slice_companion_graph (parameter : ℕ) (boundary shift : ℤ) (hb : 0 ≤ boundary)
    (first second : Fin (Parameters.modulus parameter)) :
    TrimmedSlice.law (Parameters.modulus parameter) boundary shift first.val *
      (if second = paletteEmbedding parameter ((Parameters.modulus parameter : ℤ) - 1 + shift - first.val) then 1 else 0) =
      TrimmedSlice.orderedPairSlice (Parameters.modulus parameter) boundary shift first second := by
  by_cases hf : (first.val : ℤ) ∈ TrimmedSlice.slice (Parameters.modulus parameter) boundary shift
  · have hs := (TrimmedSlice.mem_slice _ _ _ _).mp hf
    have hzero : 0 ≤ (Parameters.modulus parameter : ℤ) - 1 + shift - first.val := by omega
    have htop : (Parameters.modulus parameter : ℤ) - 1 + shift - first.val < Parameters.modulus parameter := by omega
    have heq : second = paletteEmbedding parameter ((Parameters.modulus parameter : ℤ) - 1 + shift - first.val) ↔
        (second.val : ℤ) = (Parameters.modulus parameter : ℤ) - 1 + shift - first.val := by
      constructor
      · rintro rfl; exact paletteEmbedding_val parameter _ hzero htop
      · intro h
        apply Fin.ext
        have hh := paletteEmbedding_val parameter _ hzero htop
        exact_mod_cast h.trans hh.symm
    simp only [heq, TrimmedSlice.orderedPairSlice]
  · simp only [TrimmedSlice.orderedPairSlice, TrimmedSlice.law, if_neg hf, zero_mul]

/-- Every actual legal chart provides the full pair output at every
protected input, with the Bernoulli atom present exactly at zero input. -/
theorem chart_joint_output (cutoffScale : ℝ) (parameter : ℕ) (boundary baseline : ℤ)
    (hb : 0 ≤ boundary) (mark : Fin (Parameters.modulus parameter))
    (hchart : V7ChartExists cutoffScale parameter boundary baseline
      ((ZMod.finEquiv (Parameters.modulus parameter)) mark)) :
    ∃ chartLaw : FiniteDist (Chart (ZMod (Parameters.modulus parameter))),
      ∀ input : V7Input cutoffScale parameter, ∀ first second : Fin (Parameters.modulus parameter),
      (chartPairOutput cutoffScale parameter baseline chartLaw input).weight (first,second) =
        (1 - if input = (windowZero _,windowZero _) then chartAtom (V7Input cutoffScale parameter) else 0) *
          TrimmedSlice.orderedPairSlice (Parameters.modulus parameter) boundary (baseline - input.2) first second +
        (if input = (windowZero _,windowZero _) then chartAtom (V7Input cutoffScale parameter) else 0) *
          (if first = mark then 1 else 0) *
          (if second = paletteEmbedding parameter ((Parameters.modulus parameter : ℤ) - 1 + baseline - input.2 - mark.val) then 1 else 0) := by
  obtain ⟨interior, spike, law, _, _, _, hzero, hnonzero⟩ := hchart
  refine ⟨law, ?_⟩
  intro input first second
  rw [chartPairOutput, FiniteDist.graph_weight, chartPaletteFeature_weight]
  have hmark : (ZMod.finEquiv (Parameters.modulus parameter)) first =
      (ZMod.finEquiv (Parameters.modulus parameter)) mark ↔ first = mark :=
    (ZMod.finEquiv (Parameters.modulus parameter)).injective.eq_iff
  have hunif : (if (ZMod.finEquiv (Parameters.modulus parameter)) first ∈
      v7ProtectedPalettes cutoffScale parameter boundary baseline input then
        ((v7ProtectedPalettes cutoffScale parameter boundary baseline input).card : ℝ)⁻¹ else 0) =
      TrimmedSlice.law (Parameters.modulus parameter) boundary (baseline - input.2) first.val :=
    fieldPalette_uniform parameter boundary (baseline - input.2) hb first
  have hshift : (Parameters.modulus parameter : ℤ) - 1 + baseline - input.2 - first.val =
      (Parameters.modulus parameter : ℤ) - 1 + (baseline - input.2) - first.val := by ring
  by_cases hi : input = (windowZero _,windowZero _)
  · subst input
    have hz := hzero ((ZMod.finEquiv (Parameters.modulus parameter)) first)
    dsimp only [protectedInputs] at hz
    rw [hz, hunif]
    simp only [hmark, if_true, add_mul, mul_assoc]
    rw [hshift, slice_companion_graph parameter boundary _ hb]
    by_cases hf : first = mark
    · subst first
      simp only [if_true, hshift]
    · simp only [if_neg hf, mul_zero, zero_mul, add_zero]
  · have hn := hnonzero input hi ((ZMod.finEquiv (Parameters.modulus parameter)) first)
    dsimp only [protectedInputs] at hn
    rw [hn, hunif, if_neg hi]
    simp only [sub_zero, one_mul, zero_mul, add_zero]
    rw [hshift]
    exact slice_companion_graph parameter boundary _ hb first second

end BoundaryCalibration
end
end AFT
