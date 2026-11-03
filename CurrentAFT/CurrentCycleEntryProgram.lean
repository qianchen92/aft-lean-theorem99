import CurrentAFT.CyclePatternProgram
import CurrentAFT.CycleRootExpansion
import CurrentAFT.RationalProposalProgram

/-! # Sparse rational entries of the actual selected closed-cycle law

Only ordered distinct selected sites and their touched latent edges are
enumerated. The full body permutation and all unused latent coordinates
are eliminated by exact probability identities. Every entry test below
is an explicit modular indicator, not an input oracle.
-/
namespace CurrentAFT.CurrentCycleEntryProgram

open AFT GaussianSource CycleSelections CyclePatternProgram DiffuseProfiles
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def bodyCount (security : ℕ) : ℕ := (PublicParameterProgram.modulus security).count * (security + 2)^96

def pointTest (colors order : ℕ) (output : Fin order → ℕ) (roots : Fin order → ℤ) : ℚ :=
  if ∀ index, roots index % colors = (output index : ℤ) then 1 else 0

def selectedEntry (security bits order : ℕ) (output : Fin order → ℕ) : ℚ :=
  averagedEvaluate security (edgeCutoff security) bits (bodyCount security) order
    (fun _ => pointTest (PublicParameterProgram.modulus security).count order output)

noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base Parameters.bodySize

local instance modulusNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩

theorem bodyCount_eq (security : ℕ) : bodyCount security = Parameters.bodySize security := by
  simp only [bodyCount, PublicParameterProgram.modulus_value, Parameters.bodySize_eq, Parameters.base]

theorem pointTest_bound (colors order : ℕ) (output : Fin order → ℕ) (roots : Fin order → ℤ) :
    |(pointTest colors order output roots : ℝ)| ≤ 1 := by
  unfold pointTest
  split_ifs <;> norm_num

theorem roots_mod_iff (security order : ℕ) (roots : Fin order → ℤ)
    (output : Fin order → CycleRootExpansion.Root security) :
    (∀ index, roots index % Parameters.modulus security = ((output index).val : ℤ)) ↔
      (fun index => (roots index : CycleRootExpansion.Root security)) = output := by
  have hpoint (integer : ℤ) (color : CycleRootExpansion.Root security) :
      integer % Parameters.modulus security = (color.val : ℤ) ↔
        (integer : CycleRootExpansion.Root security) = color := by
    rw [← ZMod.val_intCast]
    constructor
    · intro hequal
      apply ZMod.val_injective
      exact Int.ofNat_inj.mp hequal
    · intro hequal
      rw [hequal]
  constructor
  · intro h
    funext index
    exact (hpoint _ _).mp (h index)
  · intro h index
    exact (hpoint _ _).mpr (congrFun h index)

theorem selected_probability_source (security order : ℕ)
    (source : FiniteDist (Window (edgeCutoff security)))
    (sites : Selection (Parameters.bodySize security) order)
    (output : Fin order → CycleRootExpansion.Root security) :
    (FiniteDist.independent (fun _ : CycleRootExpansion.Vertex security => source)).expectation
      (fun latent => (pointTest (Parameters.modulus security) order (fun index => (output index).val)
        (fun slot => (latent (sites slot)).val -
          (latent ((finRotate (Parameters.bodySize security)).symm (sites slot))).val) : ℝ)) =
      (selectedLaw (Parameters.bodySize security) order (Parameters.modulus security)
        (source) (fun scalar => ((scalar.val : ℤ) : CycleRootExpansion.Root security)) sites).weight output := by
  rw [selectedLaw, ProtectedCycle.cycleLaw, FiniteDist.map_map]
  simp only [FiniteDist.expectation, FiniteDist.map_weight]
  apply Finset.sum_congr rfl
  intro latent _
  have hequal : (fun slot => PublicCharge.cycleDifference
      (fun vertex => ((latent vertex).val : CycleRootExpansion.Root security)) (sites slot)) = output ↔
      ∀ slot, ((latent (sites slot)).val -
        (latent ((finRotate (Parameters.bodySize security)).symm (sites slot))).val) %
          Parameters.modulus security = ((output slot).val : ℤ) := by
    rw [roots_mod_iff]
    simp only [PublicCharge.cycleDifference, Int.cast_sub]
  unfold pointTest
  by_cases hactual : (fun slot => PublicCharge.cycleDifference
      (fun vertex => ((latent vertex).val : CycleRootExpansion.Root security)) (sites slot)) = output
  · simp only [if_pos hactual, if_pos (hequal.mp hactual), Rat.cast_one, mul_one]
  · have hmod := mt hequal.mpr hactual
    simp only [if_neg hactual, if_neg hmod, Rat.cast_zero, mul_zero]

theorem selected_probability (security order : ℕ)
    (sites : Selection (Parameters.bodySize security) order)
    (output : Fin order → CycleRootExpansion.Root security) :
    (FiniteDist.independent (fun _ : CycleRootExpansion.Vertex security => edgeLaw security)).expectation
      (fun latent => (pointTest (Parameters.modulus security) order (fun index => (output index).val)
        (fun slot => (latent (sites slot)).val -
          (latent ((finRotate (Parameters.bodySize security)).symm (sites slot))).val) : ℝ)) =
      (selectedLaw (Parameters.bodySize security) order (Parameters.modulus security)
        (edgeLaw security) (fun scalar => ((scalar.val : ℤ) : CycleRootExpansion.Root security)) sites).weight output :=
  selected_probability_source security order (edgeLaw security) sites output


theorem selectedEntry_error (security bits order : ℕ) (hroom : order ≤ Parameters.bodySize security)
    (output : Fin order → CycleRootExpansion.Root security) :
    |(selectedEntry security bits order (fun index => (output index).val) : ℝ) -
      (averagedSelectedLaw (Parameters.bodySize security) order (Parameters.modulus security) hroom
        (edgeLaw security) (fun scalar => ((scalar.val : ℤ) : CycleRootExpansion.Root security))).weight output| ≤
      (2 * order : ℕ) / (2 : ℝ)^bits := by
  unfold selectedEntry
  rw [bodyCount_eq, PublicParameterProgram.modulus_value]
  have h := averaged_edge_error security bits (Parameters.bodySize security) order hroom
    (fun _ => pointTest (Parameters.modulus security) order (fun index => (output index).val))
    1 (by norm_num) (fun _ roots => pointTest_bound _ _ _ roots)
  simp only [mul_one] at h
  have hideal : (selectionLaw (Parameters.bodySize security) order hroom).expectation
      (fun sites => (FiniteDist.independent (fun _ : CycleRootExpansion.Vertex security => edgeLaw security)).expectation
        (fun latent => (pointTest (Parameters.modulus security) order (fun index => (output index).val)
          (fun slot => (latent (sites slot)).val -
            (latent ((finRotate (Parameters.bodySize security)).symm (sites slot))).val) : ℝ))) =
      (averagedSelectedLaw (Parameters.bodySize security) order (Parameters.modulus security) hroom
        (edgeLaw security) (fun scalar => ((scalar.val : ℤ) : CycleRootExpansion.Root security))).weight output := by
    simp_rw [selected_probability]
    rfl
  rw [hideal] at h
  exact h

theorem selectedEntry_cast (security bits order : ℕ) (hroom : order ≤ Parameters.bodySize security)
    (output : Fin order → CycleRootExpansion.Root security) :
    (selectedEntry security bits order (fun index => (output index).val) : ℝ) =
      (averagedSelectedLaw (Parameters.bodySize security) order (Parameters.modulus security) hroom
        (RationalNumerics.windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits)
        (fun scalar => ((scalar.val : ℤ) : CycleRootExpansion.Root security))).weight output := by
  unfold selectedEntry
  rw [bodyCount_eq, PublicParameterProgram.modulus_value,
    averagedEvaluate_cast security (edgeCutoff security) bits (Parameters.bodySize security) order hroom]
  simp_rw [gaussianEvaluate_semantics, selected_probability_source]
  rfl

/-- The target is the genuine selected marginal of the permuted closed
cycle, uniformly for every fixed injective label assignment. -/
theorem rootLaw_entry_error (security bits order : ℕ) (hroom : order ≤ Parameters.bodySize security)
    (labels : Selection (Parameters.bodySize security) order)
    (output : Fin order → CycleRootExpansion.Root security) :
    |(selectedEntry security bits order (fun index => (output index).val) : ℝ) -
      ((CycleRootExpansion.rootLaw security).map (fun roots index => roots (labels index))).weight output| ≤
      (2 * order : ℕ) / (2 : ℝ)^bits := by
  rw [CycleRootExpansion.rootLaw_selected security order hroom labels]
  exact selectedEntry_error security bits order hroom output

theorem selected_state_count (security order : ℕ) :
    (∑ sites : Selection (Parameters.bodySize security) order,
      Fintype.card (touched sites → Window (edgeCutoff security))) ≤
        131074^order * Parameters.base security^(164 * order) := by
  have hbody : Parameters.bodySize security ≤ 131074 * Parameters.base security ^ 160 := by
    have hd := (Parameters.dimension_bounds security).2
    have hle : Parameters.bodySize security ≤ Parameters.dimension security := by unfold Parameters.dimension; omega
    exact hle.trans hd
  have hwindow : 2 * edgeCutoff security + 1 ≤ Parameters.base security ^ 2 := by
    have hp : 0 < Parameters.sourceCutoff security := pow_pos (Parameters.base_pos security) _
    unfold edgeCutoff Parameters.sourceCutoff at *
    omega
  apply (pattern_state_count (Parameters.bodySize security) order (edgeCutoff security)).trans
  calc
    _ ≤ (131074 * Parameters.base security ^ 160)^order * (Parameters.base security ^ 2)^(2 * order) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hbody _) (Nat.pow_le_pow_left hwindow _)
    _ = _ := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_assoc, ← pow_add]; congr 2; omega

end
end CurrentAFT.CurrentCycleEntryProgram
