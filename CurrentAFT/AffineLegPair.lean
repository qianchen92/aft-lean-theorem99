import CurrentAFT.AffineLegLaw
import CurrentAFT.ActualPublicLegCharge

/-!
# Evaluating the same public affine law at protected leg inputs

The companion is the canonical modular complement of the evaluated primary.
On the supported charts it has the prescribed safe integer lift.  The
reference second scalar is fixed throughout each identity in this file.
-/

namespace CurrentAFT.AffineFlagCalibration

open AFT AFT.BoundaryCalibration ActualPublicLegCharge
open scoped BigOperators Classical

noncomputable section

local instance pairGraphDecidableEq {A B : Type*} : DecidableEq (A × B) := Classical.decEq _

local instance pairModulusPrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩

abbrev Palette (security : ℕ) := ActualControls.Palette security
abbrev Scalar (security : ℕ) := FirstHistogram.Scalar security

def companion (security : ℕ) (shift : ℤ) (primary : Palette security) : Palette security :=
  (ZMod.finEquiv (Parameters.modulus security)).toEquiv.symm
    (-1 + (shift : ZMod (Parameters.modulus security)) -
      (ZMod.finEquiv (Parameters.modulus security)) primary)

def pairProjection (security : ℕ) (shift : ℤ) (primary : Palette security) :
    Palette security × Palette security := (primary, companion security shift primary)

theorem companion_of_integer_sum (security : ℕ) (shift : ℤ)
    (first second : Palette security)
    (hsum : (second.val : ℤ) = (Parameters.modulus security : ℤ) - 1 + shift - first.val) :
    companion security shift first = second := by
  apply (ZMod.finEquiv (Parameters.modulus security)).injective
  have he : (ZMod.finEquiv (Parameters.modulus security)) (companion security shift first) =
      -1 + (shift : ZMod (Parameters.modulus security)) -
        (ZMod.finEquiv (Parameters.modulus security)) first :=
    (ZMod.finEquiv (Parameters.modulus security)).apply_symm_apply _
  rw [he, finEquiv_natCast, finEquiv_natCast]
  have hc := congrArg (fun n : ℤ => (n : ZMod (Parameters.modulus security))) hsum
  push_cast at hc
  simpa only [ZMod.natCast_self, zero_sub] using hc.symm

theorem companion_trimmed_iff (security : ℕ) (shift : ℤ) (first second : Palette security)
    (hfirst : (first.val : ℤ) ∈ TrimmedSlice.slice (Parameters.modulus security) 1 shift) :
    companion security shift first = second ↔
      (second.val : ℤ) = (Parameters.modulus security : ℤ) - 1 + shift - first.val := by
  have hs := (TrimmedSlice.mem_slice _ _ _ _).mp hfirst
  let value : ℤ := (Parameters.modulus security : ℤ) - 1 + shift - first.val
  have hv : 0 ≤ value ∧ value < Parameters.modulus security := by dsimp [value]; omega
  let output : Palette security := ⟨value.toNat, by omega⟩
  have hout : (output.val : ℤ) = value := by dsimp [output]; omega
  have hc : companion security shift first = output :=
    companion_of_integer_sum security shift first output hout
  rw [hc]
  constructor
  · rintro rfl
    exact hout
  · intro he
    apply Fin.ext
    exact_mod_cast hout.trans he.symm

theorem graph_map_weight {A B : Type*} [Fintype A] [Fintype B]
    (law : FiniteDist A) (f : A → B) (a : A) (b : B) :
    (law.map (fun x => (x, f x))).weight (a, b) =
      law.weight a * (if f a = b then 1 else 0) := by
  simp only [FiniteDist.map_weight, Prod.mk.injEq, ite_and,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  split_ifs <;> simp

theorem uniformSlice_pair (security : ℕ) (shift : ℤ)
    (hclear : 2 + |shift| < (Parameters.modulus security : ℤ))
    (first second : Palette security) :
    ((TrimmedSlice.finiteLaw (Parameters.modulus security) 1 shift (by norm_num) hclear).map
      (pairProjection security shift)).weight (first, second) =
        TrimmedSlice.orderedPairSlice (Parameters.modulus security) 1 shift first second := by
  change ((TrimmedSlice.finiteLaw (Parameters.modulus security) 1 shift (by norm_num) hclear).map
    (fun x => (x, companion security shift x))).weight (first, second) = _
  rw [graph_map_weight, TrimmedSlice.finiteLaw_weight]
  unfold TrimmedSlice.orderedPairSlice
  by_cases hc : (first.val : ℤ) ∈ TrimmedSlice.slice (Parameters.modulus security) 1 shift
  · rw [companion_trimmed_iff security shift first second hc]
    split_ifs <;> rfl
  · simp only [TrimmedSlice.law, if_neg hc, zero_mul]

def evaluatedPrimary (security : ℕ) (baseline : ℤ)
    (hbaseline : |baseline| ≤ legOffsetBound security) (mark : Palette security)
    (first second : Scalar security) : FiniteDist (Palette security) :=
  (currentLaw security baseline hbaseline ((ZMod.finEquiv (Parameters.modulus security)) mark)
    (1 / 2) (by norm_num) (by norm_num)).joint.map (fun point =>
      (ZMod.finEquiv (Parameters.modulus security)).toEquiv.symm
        (feature ((first.val : ℤ) : ZMod (Parameters.modulus security))
          ((second.val : ℤ) : ZMod (Parameters.modulus security)) point.2))

def evaluatedPair (security : ℕ) (baseline : ℤ)
    (hbaseline : |baseline| ≤ legOffsetBound security) (mark : Palette security)
    (first second : Scalar security) : FiniteDist (Palette security × Palette security) :=
  (evaluatedPrimary security baseline hbaseline mark first second).map
    (pairProjection security (baseline - second.val))

theorem evaluatedPrimary_weight (security : ℕ) (baseline : ℤ)
    (hbaseline : |baseline| ≤ legOffsetBound security) (mark : Palette security)
    (first second : Scalar security) (color : Palette security) :
    (evaluatedPrimary security baseline hbaseline mark first second).weight color =
      if first.val = 0 then
        (1 / 2 : ℝ) * (if color ∈ TrimmedSlice.paletteSlice (Parameters.modulus security) 1
          (baseline - second.val) then
            ((TrimmedSlice.paletteSlice (Parameters.modulus security) 1 (baseline - second.val)).card : ℝ)⁻¹ else 0) +
          (1 / 2 : ℝ) * (if color = mark then 1 else 0)
      else if color ∈ TrimmedSlice.paletteSlice (Parameters.modulus security) 1 (baseline - second.val) then
        ((TrimmedSlice.paletteSlice (Parameters.modulus security) 1 (baseline - second.val)).card : ℝ)⁻¹ else 0 := by
  let input : ProtectedInput security := (first, second)
  let model := currentLaw security baseline hbaseline
    ((ZMod.finEquiv (Parameters.modulus security)) mark) (1 / 2) (by norm_num) (by norm_num)
  have heq : evaluatedPrimary security baseline hbaseline mark first second =
      (model.joint.map (fun point => feature
        ((first.val : ℤ) : ZMod (Parameters.modulus security))
        ((second.val : ℤ) : ZMod (Parameters.modulus security)) point.2)).map
          (ZMod.finEquiv (Parameters.modulus security)).toEquiv.symm := by
    rw [FiniteDist.map_map]
    rfl
  rw [heq, FiniteDist.map_equiv_weight]
  change (model.joint.map (fun point => feature
    (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security) input).1
    (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security) input).2 point.2)).weight
      ((ZMod.finEquiv (Parameters.modulus security)) color) = _
  by_cases hf : first.val = 0
  · have hon := model.on_line input ((protected_first_cast_eq_zero_iff security input).mpr hf)
      ((ZMod.finEquiv (Parameters.modulus security)) color)
    rw [hon, if_pos hf]
    simp only [input, protectedPalettes, fieldPalette, Finset.mem_map_equiv,
      Finset.card_map, one_div]
    norm_num
  · have hoff := model.off_line input
      (fun hz => hf ((protected_first_cast_eq_zero_iff security input).mp hz))
      ((ZMod.finEquiv (Parameters.modulus security)) color)
    rw [hoff, if_neg hf]
    simp only [input, protectedPalettes, fieldPalette, Finset.mem_map_equiv,
      Finset.card_map]
    have hsym : (ZMod.finEquiv (Parameters.modulus security)).symm
        ((ZMod.finEquiv (Parameters.modulus security)) color) = color :=
      (ZMod.finEquiv (Parameters.modulus security)).symm_apply_apply color
    exact congrArg (fun a : Palette security =>
      if a ∈ TrimmedSlice.paletteSlice (Parameters.modulus security) 1 (baseline - second.val) then
        ((TrimmedSlice.paletteSlice (Parameters.modulus security) 1 (baseline - second.val)).card : ℝ)⁻¹ else 0) hsym

end
end CurrentAFT.AffineFlagCalibration
