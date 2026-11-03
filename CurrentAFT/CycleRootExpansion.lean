import CurrentAFT.UniformCycleSelection
import CurrentAFT.SupportedHoeffding
import CurrentAFT.CycleRootParameters

/-!
# Exact finite response expansion for the actual permuted closed cycle

The response acts on arbitrary joint, vector-valued tests. Its source law
is the literal uniform body permutation of the complete protected cycle.
The independent term and all singleton cancellations are proved under
support-only positivity, so no inverse of a zero root atom is used.
-/

namespace CurrentAFT.CycleRootExpansion

open AFT CycleSelections
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {Index Color Value : Type*} [Fintype Index] [DecidableEq Index] [Fintype Color]
  [AddCommGroup Value] [Module ℝ Value]

def expectationLinear (law : FiniteDist Color) : (Color → Value) →ₗ[ℝ] Value where
  toFun test := ∑ color, law.weight color • test color
  map_add' first second := by simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' scalar test := by
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro color _
    rw [mul_comm]

def componentResponse (joint : FiniteDist (Index → Color))
    (reference : Index → FiniteDist Color) (selected : Finset Index) :
    ((Index → Color) → Value) →ₗ[ℝ] Value where
  toFun test := ∑ word, ((FiniteDist.independent reference).weight word *
    Hoeffding.densityComponent reference joint.weight selected word) • test word
  map_add' first second := by simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' scalar test := by
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro word _
    rw [mul_comm]

theorem reference_weight_ne_zero (reference : Index → FiniteDist Color)
    (word : Index → Color) (hword : ∀ index, 0 < (reference index).weight (word index)) :
    (FiniteDist.independent reference).weight word ≠ 0 :=
  (Finset.prod_pos (fun index _ => hword index)).ne'

/-- The complete finite response identity retains the joint test as one
object and permits zero reference atoms outside the actual source support. -/
theorem sum_componentResponse (joint : FiniteDist (Index → Color))
    (reference : Index → FiniteDist Color)
    (hsupport : ∀ word, joint.weight word ≠ 0 → ∀ index,
      0 < (reference index).weight (word index)) :
    (∑ selected : Finset Index, componentResponse (Value := Value) joint reference selected) =
      expectationLinear joint := by
  cases Subsingleton.elim (inferInstance : DecidableEq Index) (Classical.decEq Index)
  apply LinearMap.ext
  intro test
  simp only [LinearMap.sum_apply, componentResponse, LinearMap.coe_mk, AddHom.coe_mk,
    expectationLinear]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro word _
  rw [← Finset.sum_smul, ← Finset.mul_sum, Hoeffding.densityComponent_sum]
  by_cases hzero : joint.weight word = 0
  · simp [hzero]
  · rw [mul_div_cancel₀ _ (reference_weight_ne_zero reference word (hsupport word hzero))]

theorem componentResponse_empty (joint : FiniteDist (Index → Color))
    (reference : Index → FiniteDist Color) :
    componentResponse (Value := Value) joint reference ∅ =
      expectationLinear (FiniteDist.independent reference) := by
  cases Subsingleton.elim (inferInstance : DecidableEq Index) (Classical.decEq Index)
  apply LinearMap.ext
  intro test
  simp only [componentResponse, expectationLinear, LinearMap.coe_mk, AddHom.coe_mk,
    Hoeffding.densityComponent, Finset.prod_empty, mul_one, joint.sum_one]

theorem singleton_component_on_support (joint : FiniteDist (Index → Color))
    (reference : Index → FiniteDist Color) (index : Index)
    (hmarginal : joint.map (fun word => word index) = reference index)
    (word : Index → Color) (hword : (reference index).weight (word index) ≠ 0) :
    Hoeffding.densityComponent reference joint.weight {index} word = 0 := by
  cases Subsingleton.elim (inferInstance : DecidableEq Index) (Classical.decEq Index)
  have hmean := FiniteDist.expectation_map joint (fun input => input index)
    (fun color => CycleSelections.centeredRootAtom (reference index) color (word index))
  rw [hmarginal, CycleSelections.centeredRootAtom_mean_zero _ _ hword] at hmean
  simpa only [Hoeffding.densityComponent, Finset.prod_singleton,
    FiniteDist.expectation, Function.comp_apply, SupportedHoeffding.centeredRootAtom_eq] using hmean.symm

/-- Singleton responses vanish as actual weighted operators, including
outside the root-reference support where the density need not vanish. -/
theorem componentResponse_singleton (joint : FiniteDist (Index → Color))
    (reference : Index → FiniteDist Color) (index : Index)
    (hmarginal : joint.map (fun word => word index) = reference index) :
    componentResponse (Value := Value) joint reference {index} = 0 := by
  apply LinearMap.ext
  intro test
  change (∑ word, ((FiniteDist.independent reference).weight word *
    Hoeffding.densityComponent reference joint.weight {index} word) • test word) = 0
  apply Finset.sum_eq_zero
  intro word _
  by_cases hzero : (reference index).weight (word index) = 0
  · have hproduct : (FiniteDist.independent reference).weight word = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ index) hzero
    rw [hproduct, zero_mul, zero_smul]
  · rw [singleton_component_on_support joint reference index hmarginal word hzero,
      mul_zero, zero_smul]

/-- The genuine correlated response differs from independent integration
by precisely the components of size at least two. -/
theorem response_defect_expansion (joint : FiniteDist (Index → Color))
    (reference : Index → FiniteDist Color)
    (hsupport : ∀ word, joint.weight word ≠ 0 → ∀ index,
      0 < (reference index).weight (word index))
    (hmarginal : ∀ index, joint.map (fun word => word index) = reference index) :
    expectationLinear (Value := Value) joint -
      expectationLinear (FiniteDist.independent reference) =
      ∑ selected ∈ (Finset.univ : Finset (Finset Index)).filter (fun selected => 2 ≤ selected.card),
        componentResponse joint reference selected := by
  rw [← sum_componentResponse joint reference hsupport,
    ← componentResponse_empty joint reference]
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Finset Index))
    (componentResponse (Value := Value) joint reference) (Finset.mem_univ ∅)
  rw [← hsplit, add_sub_cancel_right]
  symm
  apply Finset.sum_subset
  · intro selected hselected
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    intro hequal
    have hcard := (Finset.mem_filter.mp hselected).2
    rw [hequal, Finset.card_empty] at hcard
    omega
  · intro selected hselected hnot
    have hnonempty := (Finset.mem_erase.mp hselected).1
    have hcard : selected.card = 1 := by
      have hpositive := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hnonempty)
      have hsmall : ¬ 2 ≤ selected.card := by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hnot
      omega
    obtain ⟨index, rfl⟩ := Finset.card_eq_one.mp hcard
    exact componentResponse_singleton joint reference index (hmarginal index)

/-- Exact marginals already imply the support condition needed above. -/
theorem marginal_support (joint : FiniteDist (Index → Color))
    (reference : Index → FiniteDist Color)
    (hmarginal : ∀ index, joint.map (fun word => word index) = reference index)
    (word : Index → Color) (hword : joint.weight word ≠ 0) (index : Index) :
    0 < (reference index).weight (word index) := by
  have hpositive : 0 < joint.weight word := lt_of_le_of_ne (joint.nonneg word) (Ne.symm hword)
  rw [← hmarginal index, FiniteDist.map_weight]
  apply hpositive.trans_le
  apply (Finset.single_le_sum (s := Finset.univ)
    (f := fun input => if input index = word index then joint.weight input else 0)
    (fun input _ => by dsimp only; split_ifs; exact joint.nonneg input; exact le_rfl)
    (Finset.mem_univ word)).trans'
  simp only [if_true, le_refl]

section Actual

local instance currentModulusNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩

abbrev Root (security : ℕ) := ZMod (Parameters.modulus security)
abbrev Vertex (security : ℕ) := Fin (Parameters.bodySize security)

def rootReference (security : ℕ) : FiniteDist (Root security) :=
  ProtectedCycle.differenceLaw (DiffuseProfiles.edgeLaw security)
    (fun scalar => ((scalar : ℤ) : Root security))

/-- The body permutation is genuinely averaged independently of the latent
edges; the complete closing edge is part of every conditional law. -/
def rootLaw (security : ℕ) : FiniteDist (Vertex security → Root security) :=
  (FiniteDist.uniform (Equiv.Perm (Vertex security))).mix
    (ProtectedCycle.relabeledCycleLaw (Parameters.bodySize security) (Parameters.modulus security)
      (DiffuseProfiles.edgeLaw security) (fun scalar => ((scalar : ℤ) : Root security)))

theorem rootLaw_selected (security order : ℕ) (horder : order ≤ Parameters.bodySize security)
    (labels : Selection (Parameters.bodySize security) order) :
    (rootLaw security).map (fun roots slot => roots (labels slot)) =
      averagedSelectedLaw (Parameters.bodySize security) order (Parameters.modulus security) horder
        (DiffuseProfiles.edgeLaw security) (fun scalar => ((scalar : ℤ) : Root security)) := by
  rw [rootLaw, FiniteDist.map_mix]
  exact uniform_permuted_selectedLaw _ _ _ horder _ _ labels

theorem current_body_two_le (security : ℕ) : 2 ≤ Parameters.bodySize security := by
  have hbase := Parameters.base_ge_two security
  have hmod := (Parameters.modulus_spec security).2.two_le
  have hpower : 1 ≤ Parameters.base security ^ 96 := one_le_pow₀ (by omega)
  rw [Parameters.bodySize_eq]
  exact hmod.trans (by simpa using Nat.mul_le_mul_left (Parameters.modulus security) hpower)

theorem rootLaw_coordinate (security : ℕ) (index : Vertex security) :
    (rootLaw security).map (fun roots => roots index) = rootReference security := by
  let labels : Selection (Parameters.bodySize security) 1 :=
    ⟨fun _ => index, fun first second _ => Subsingleton.elim first second⟩
  have h := congrArg (fun law : FiniteDist (Fin 1 → Root security) =>
    law.map (fun roots => roots 0))
    (rootLaw_selected security 1 (by have := current_body_two_le security; omega) labels)
  dsimp only at h
  rw [FiniteDist.map_map] at h
  exact h.trans (averagedSelectedLaw_coordinate _ _ _ _
    (current_body_two_le security) _ _ 0)

def actualComponent (security : ℕ) (selected : Finset (Vertex security)) :
    ((Vertex security → Root security) → Value) →ₗ[ℝ] Value :=
  componentResponse (rootLaw security) (fun _ => rootReference security) selected

theorem actualComponent_canonical (security : ℕ) (selected : Finset (Vertex security)) :
    Hoeffding.Canonical (fun _ => rootReference security) selected
      (Hoeffding.densityComponent (fun _ => rootReference security) (rootLaw security).weight selected) :=
  SupportedHoeffding.densityComponent_canonical_of_support _ _
    (marginal_support _ _ (rootLaw_coordinate security)) selected

/-- Exact operator expansion for the current actual law, with no residual
support, marginal, independence, or likelihood hypothesis. -/
theorem actual_response_defect (security : ℕ) :
    expectationLinear (Value := Value) (rootLaw security) -
      expectationLinear (FiniteDist.independent (fun _ : Vertex security => rootReference security)) =
      ∑ selected ∈ (Finset.univ : Finset (Finset (Vertex security))).filter
          (fun selected => 2 ≤ selected.card), actualComponent security selected :=
  response_defect_expansion _ _ (marginal_support _ _ (rootLaw_coordinate security))
    (rootLaw_coordinate security)

theorem actualComponent_singleton (security : ℕ) (index : Vertex security) :
    actualComponent (Value := Value) security {index} = 0 :=
  componentResponse_singleton _ _ index (rootLaw_coordinate security index)

def selectedCoefficient (security order : ℕ)
    (labels : Selection (Parameters.bodySize security) order) : (Fin order → Root security) → ℝ :=
  centeredRootDensity ((rootLaw security).map (fun roots slot => roots (labels slot)))
    (fun _ => rootReference security)

/-- The full permutation experiment is exactly the selected-root law used
in the quantitative cycle estimate. The complete coefficient norm is
controlled, uniformly over all fixed distinct output labels. -/
theorem selectedCoefficient_norm (security order : ℕ) (hpositive : 1 ≤ order)
    (hbody : 2 * order ≤ Parameters.bodySize security)
    (labels : Selection (Parameters.bodySize security) order) :
    Real.sqrt ((FiniteDist.independent (fun _ : Fin order => rootReference security)).l2Sq
      (selectedCoefficient security order labels)) ≤
      (((2 * (order + 1) : ℕ) : ℝ) ^ order) * currentRootTag security ^ order := by
  unfold selectedCoefficient
  rw [rootLaw_selected security order (by omega) labels]
  exact current_averaged_centered_norm_le security order hpositive hbody

/-- One common threshold works for every fixed selected order and every
distinct label tuple, with the actual inverse-base-power root tag. -/
theorem selectedCoefficient_norm_eventually (maximum : ℕ) :
    ∃ threshold : ℕ, ∀ security ≥ threshold, ∀ order, 1 ≤ order → order ≤ maximum →
      ∀ labels : Selection (Parameters.bodySize security) order,
        Real.sqrt ((FiniteDist.independent (fun _ : Fin order => rootReference security)).l2Sq
          (selectedCoefficient security order labels)) ≤
          (((2 * (order + 1) : ℕ) : ℝ) ^ order) *
            (1 / (Parameters.base security : ℝ) ^ 79) ^ order := by
  refine ⟨2 * maximum, ?_⟩
  intro security hsecurity order hpositive horder labels
  have h := selectedCoefficient_norm security order hpositive
    (current_body_fixed_orders maximum security hsecurity order horder) labels
  rwa [currentRootTag_eq] at h

variable {Control : Type*} [Fintype Control]

/-- Source independence is applied once to the entire public joint
kernel. It never requires that the control kernel factor by coordinates. -/
theorem selectedCoefficient_joint_energy (security order : ℕ)
    (labels : Selection (Parameters.bodySize security) order)
    (control : FiniteDist Control) (kernel : Control → ℝ) :
    ((FiniteDist.independent (fun _ : Fin order => rootReference security)).prod control).l2Sq
      (fun pair => selectedCoefficient security order labels pair.1 * kernel pair.2) =
      (FiniteDist.independent (fun _ : Fin order => rootReference security)).l2Sq
        (selectedCoefficient security order labels) * control.l2Sq kernel := by
  simp only [FiniteDist.l2Sq, FiniteDist.expectation, FiniteDist.prod_weight,
    Fintype.sum_prod_type, mul_pow]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro roots _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro controls _
  ring

end Actual

end

end CurrentAFT.CycleRootExpansion
