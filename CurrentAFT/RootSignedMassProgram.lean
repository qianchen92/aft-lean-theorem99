import CurrentAFT.CurrentCycleEntryProgram
import CurrentAFT.SelectedRootComponent

/-! # Root centering as a signed mass with no root-atom inverse

After multiplication by its actual root-reference mass, the selected
coefficient is an expectation of products `delta - marginal`. This is an
identity of coefficient data, before physical evaluation. The rational
program evaluates those explicit bounded tests on sparse cycle patterns.
-/
namespace CurrentAFT.RootSignedMassProgram

open AFT GaussianSource CycleSelections CyclePatternProgram CycleRootExpansion
  CurrentCycleEntryProgram DiffuseProfiles
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def referenceEntry (security bits output : ℕ) : ℚ :=
  selectedEntry security bits 1 (fun _ => output)

def signedTest (security bits order : ℕ) (output : Fin order → ℕ) (roots : Fin order → ℤ) : ℚ :=
  ∏ index, ((if roots index % (PublicParameterProgram.modulus security).count = (output index : ℤ)
    then (1 : ℚ) else 0) - referenceEntry security bits (output index))

def weightedEntry (security bits order : ℕ) (output : Fin order → ℕ) : ℚ :=
  averagedEvaluate security (edgeCutoff security) bits (bodyCount security) order
    (fun _ => signedTest security bits order output)

def oneEquiv (Color : Type*) : (Fin 1 → Color) ≃ Color where
  toFun word := word 0
  invFun color _ := color
  left_inv word := by
    funext index
    exact congrArg word (Subsingleton.elim (0 : Fin 1) index)
  right_inv _ := rfl

noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base Parameters.bodySize

local instance modulusNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩

theorem weighted_density (Index Color : Type*) [Fintype Index] [DecidableEq Index] [Fintype Color] [DecidableEq Color]
    (joint : FiniteDist (Index → Color)) (reference : Index → FiniteDist Color)
    (hsupport : ∀ input, joint.weight input ≠ 0 → ∀ index, 0 < (reference index).weight (input index))
    (output : Index → Color) :
    (∏ index, (reference index).weight (output index)) * centeredRootDensity joint reference output =
      joint.expectation (fun input => ∏ index,
        ((if input index = output index then (1 : ℝ) else 0) - (reference index).weight (output index))) := by
  unfold centeredRootDensity FiniteDist.expectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro input _
  by_cases hzero : joint.weight input = 0
  · simp only [hzero, zero_mul, mul_zero]
  · have hpoint (index : Index) : (reference index).weight (output index) *
        centeredRootAtom (reference index) (input index) (output index) =
          (if input index = output index then (1 : ℝ) else 0) - (reference index).weight (output index) := by
      by_cases hout : (reference index).weight (output index) = 0
      · have hne : input index ≠ output index := by
          intro hequal
          have hpos := hsupport input hzero index
          rw [hequal, hout] at hpos
          exact (lt_irrefl 0) hpos
        simp only [centeredRootAtom, hout, hne, if_false, zero_mul, sub_zero]
      · unfold centeredRootAtom
        by_cases hequal : input index = output index
        · simp only [if_pos hequal]
          field_simp
        · simp only [if_neg hequal]
          field_simp
    calc
      _ = joint.weight input *
          ((∏ index, (reference index).weight (output index)) *
            ∏ index, centeredRootAtom (reference index) (input index) (output index)) := by ring
      _ = joint.weight input * (∏ index, (reference index).weight (output index) *
          centeredRootAtom (reference index) (input index) (output index)) := by rw [Finset.prod_mul_distrib]
      _ = _ := by congr 1; exact Finset.prod_congr rfl (fun index _ => hpoint index)

theorem actual_weighted_coefficient (security order : ℕ)
    (labels : Selection (Parameters.bodySize security) order) (output : Fin order → Root security) :
    (∏ index, (rootReference security).weight (output index)) * selectedCoefficient security order labels output =
      ((rootLaw security).map (fun roots index => roots (labels index))).expectation
        (fun input => ∏ index, ((if input index = output index then (1 : ℝ) else 0) -
          (rootReference security).weight (output index))) := by
  unfold selectedCoefficient
  apply weighted_density
  apply marginal_support
  intro index
  rw [FiniteDist.map_map]
  exact rootLaw_coordinate security (labels index)

theorem singleton_probability (security : ℕ) (source : FiniteDist (Window (edgeCutoff security)))
    (output : Root security) :
    (averagedSelectedLaw (Parameters.bodySize security) 1 (Parameters.modulus security)
      (by have := current_body_two_le security; omega) source
      (fun scalar => ((scalar.val : ℤ) : Root security))).weight (fun _ => output) =
        (ProtectedCycle.differenceLaw source (fun scalar => ((scalar.val : ℤ) : Root security))).weight output := by
  have h := congrArg (fun law : FiniteDist (Root security) => law.weight output)
    (averagedSelectedLaw_coordinate (Parameters.bodySize security) 1 (Parameters.modulus security)
      (by have := current_body_two_le security; omega) (current_body_two_le security) source
      (fun scalar => ((scalar.val : ℤ) : Root security)) 0)
  change ((averagedSelectedLaw (Parameters.bodySize security) 1 (Parameters.modulus security) _ source _).map
    (oneEquiv (Root security))).weight output = _ at h
  rw [FiniteDist.map_equiv_weight] at h
  exact h

theorem referenceEntry_cast (security bits : ℕ) (output : Root security) :
    (referenceEntry security bits output.val : ℝ) =
      (ProtectedCycle.differenceLaw
        (RationalNumerics.windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits)
        (fun scalar => ((scalar.val : ℤ) : Root security))).weight output := by
  rw [referenceEntry, selectedEntry_cast security bits 1 (by have := current_body_two_le security; omega)
    (fun _ => output), singleton_probability]

theorem referenceEntry_bounds (security bits : ℕ) (output : Root security) :
    0 ≤ (referenceEntry security bits output.val : ℝ) ∧ (referenceEntry security bits output.val : ℝ) ≤ 1 := by
  rw [referenceEntry_cast]
  exact ⟨FiniteDist.nonneg _ _, FiniteDist.atom_le_one _ _⟩

theorem referenceEntry_error (security bits : ℕ) (output : Root security) :
    |(referenceEntry security bits output.val : ℝ) - (rootReference security).weight output| ≤
      2 / (2 : ℝ)^bits := by
  have h := selectedEntry_error security bits 1 (by have := current_body_two_le security; omega) (fun _ => output)
  rw [singleton_probability] at h
  exact h

theorem root_mod_iff (security : ℕ) (integer : ℤ) (output : Root security) :
    integer % Parameters.modulus security = (output.val : ℤ) ↔ (integer : Root security) = output := by
  rw [← ZMod.val_intCast]
  constructor
  · intro h
    apply ZMod.val_injective
    exact Int.ofNat_inj.mp h
  · intro h
    rw [h]

theorem signedTest_cast (security bits order : ℕ) (output : Fin order → Root security) (roots : Fin order → ℤ) :
    (signedTest security bits order (fun index => (output index).val) roots : ℝ) =
      ∏ index, ((if (roots index : Root security) = output index then (1 : ℝ) else 0) -
        (referenceEntry security bits (output index).val : ℝ)) := by
  simp only [signedTest, PublicParameterProgram.modulus_value, Rat.cast_prod, Rat.cast_sub]
  apply Finset.prod_congr rfl
  intro index _
  by_cases hequal : (roots index : Root security) = output index
  · rw [if_pos ((root_mod_iff security _ _).mpr hequal), if_pos hequal, Rat.cast_one]
  · rw [if_neg (mt (root_mod_iff security _ _).mp hequal), if_neg hequal, Rat.cast_zero]

theorem signedTest_bound (security bits order : ℕ) (output : Fin order → Root security) (roots : Fin order → ℤ) :
    |(signedTest security bits order (fun index => (output index).val) roots : ℝ)| ≤ 1 := by
  rw [signedTest_cast, Finset.abs_prod]
  apply Finset.prod_le_one
  · intro _ _
    exact abs_nonneg _
  · intro index _
    have h := referenceEntry_bounds security bits (output index)
    split_ifs <;> exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem abs_prod_difference {Index : Type*} [DecidableEq Index]
    (first second : Index → ℝ) (hfirst : ∀ index, |first index| ≤ 1) (hsecond : ∀ index, |second index| ≤ 1)
    (indices : Finset Index) :
    |(∏ index ∈ indices, first index) - ∏ index ∈ indices, second index| ≤
      ∑ index ∈ indices, |first index - second index| := by
  have hprod (set : Finset Index) : |∏ index ∈ set, second index| ≤ 1 := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun index _ => hsecond index)
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert index indices hnot ih =>
    rw [Finset.prod_insert hnot, Finset.prod_insert hnot, Finset.sum_insert hnot]
    have hrewrite : first index * (∏ other ∈ indices, first other) -
        second index * (∏ other ∈ indices, second other) =
        first index * ((∏ other ∈ indices, first other) - ∏ other ∈ indices, second other) +
          (first index - second index) * (∏ other ∈ indices, second other) := by ring
    rw [hrewrite]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul]
    calc
      _ ≤ 1 * (∑ other ∈ indices, |first other - second other|) + |first index - second index| * 1 :=
        add_le_add (mul_le_mul (hfirst index) ih (abs_nonneg _) (by positivity))
          (mul_le_mul_of_nonneg_left (hprod indices) (abs_nonneg _))
      _ = _ := by ring

def signedKernel (security bits order : ℕ) (output input : Fin order → Root security) : ℝ :=
  ∏ index, ((if input index = output index then (1 : ℝ) else 0) -
    (referenceEntry security bits (output index).val : ℝ))

theorem weightedEntry_source_error (security bits order : ℕ) (hroom : order ≤ Parameters.bodySize security)
    (output : Fin order → Root security) :
    |(weightedEntry security bits order (fun index => (output index).val) : ℝ) -
      (averagedSelectedLaw (Parameters.bodySize security) order (Parameters.modulus security) hroom
        (edgeLaw security) (fun scalar => ((scalar.val : ℤ) : Root security))).expectation
          (signedKernel security bits order output)| ≤ (2 * order : ℕ) / (2 : ℝ)^bits := by
  unfold weightedEntry
  rw [bodyCount_eq]
  have h := averaged_edge_error security bits (Parameters.bodySize security) order hroom
    (fun _ => signedTest security bits order (fun index => (output index).val)) 1 (by norm_num)
    (fun _ roots => signedTest_bound security bits order output roots)
  simp only [mul_one] at h
  have hideal : (selectionLaw (Parameters.bodySize security) order hroom).expectation
      (fun sites => (FiniteDist.independent (fun _ : Vertex security => edgeLaw security)).expectation
        (fun latent => (signedTest security bits order (fun index => (output index).val)
          (fun slot => (latent (sites slot)).val -
            (latent ((finRotate (Parameters.bodySize security)).symm (sites slot))).val) : ℝ))) =
      (averagedSelectedLaw (Parameters.bodySize security) order (Parameters.modulus security) hroom
        (edgeLaw security) (fun scalar => ((scalar.val : ℤ) : Root security))).expectation
          (signedKernel security bits order output) := by
    rw [averagedSelectedLaw, FiniteDist.expectation_mix]
    apply congrArg (FiniteDist.expectation _)
    funext sites
    rw [selectedLaw, ProtectedCycle.cycleLaw, FiniteDist.expectation_map, FiniteDist.expectation_map]
    apply congrArg (FiniteDist.expectation _)
    funext latent
    rw [signedTest_cast]
    unfold signedKernel
    apply Finset.prod_congr rfl
    intro index _
    simp only [PublicCharge.cycleDifference, Int.cast_sub]
  rw [hideal] at h
  exact h

theorem signedKernel_error (security bits order : ℕ) (output input : Fin order → Root security) :
    |signedKernel security bits order output input -
      (∏ index, ((if input index = output index then (1 : ℝ) else 0) -
        (rootReference security).weight (output index)))| ≤ (2 * order : ℕ) / (2 : ℝ)^bits := by
  have hdelta (index : Fin order) (rate : ℝ) (hrate : 0 ≤ rate ∧ rate ≤ 1) :
      |(if input index = output index then (1 : ℝ) else 0) - rate| ≤ 1 := by
    split_ifs <;> exact abs_le.mpr ⟨by linarith, by linarith⟩
  apply (abs_prod_difference
    (fun index => (if input index = output index then (1 : ℝ) else 0) -
      (referenceEntry security bits (output index).val : ℝ))
    (fun index => (if input index = output index then (1 : ℝ) else 0) -
      (rootReference security).weight (output index))
    (fun index => hdelta index _ (referenceEntry_bounds security bits (output index)))
    (fun index => hdelta index _ ⟨(rootReference security).nonneg _, (rootReference security).atom_le_one _⟩)
    Finset.univ).trans
  calc
    _ ≤ ∑ _index : Fin order, 2 / (2 : ℝ)^bits := by
      apply Finset.sum_le_sum
      intro index _
      have hequal : ((if input index = output index then (1 : ℝ) else 0) -
          (referenceEntry security bits (output index).val : ℝ)) -
          ((if input index = output index then (1 : ℝ) else 0) -
            (rootReference security).weight (output index)) =
          -((referenceEntry security bits (output index).val : ℝ) -
            (rootReference security).weight (output index)) := by ring
      rw [hequal, abs_neg]
      exact referenceEntry_error security bits (output index)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]; ring

/-- A genuine sparse rational program for the actual weighted root
coefficient. Zero marginal atoms cause no division or precision loss. -/
theorem weightedEntry_error (security bits order : ℕ) (hroom : order ≤ Parameters.bodySize security)
    (labels : Selection (Parameters.bodySize security) order) (output : Fin order → Root security) :
    |(weightedEntry security bits order (fun index => (output index).val) : ℝ) -
      (∏ index, (rootReference security).weight (output index)) * selectedCoefficient security order labels output| ≤
      (4 * order : ℕ) / (2 : ℝ)^bits := by
  let joint := averagedSelectedLaw (Parameters.bodySize security) order (Parameters.modulus security) hroom
    (edgeLaw security) (fun scalar => ((scalar.val : ℤ) : Root security))
  have hweighted := actual_weighted_coefficient security order labels output
  rw [rootLaw_selected security order hroom labels] at hweighted
  rw [hweighted]
  have hkernel : |joint.expectation (signedKernel security bits order output) -
      joint.expectation (fun input => ∏ index, ((if input index = output index then (1 : ℝ) else 0) -
        (rootReference security).weight (output index)))| ≤ (2 * order : ℕ) / (2 : ℝ)^bits := by
    rw [← FiniteDist.expectation_sub]
    exact FiniteDist.abs_average_le_bound joint _ _ (signedKernel_error security bits order output)
  calc
    _ ≤ |(weightedEntry security bits order (fun index => (output index).val) : ℝ) -
        joint.expectation (signedKernel security bits order output)| +
      |joint.expectation (signedKernel security bits order output) -
        joint.expectation (fun input => ∏ index, ((if input index = output index then (1 : ℝ) else 0) -
          (rootReference security).weight (output index)))| := abs_sub_le _ _ _
    _ ≤ (2 * order : ℕ) / (2 : ℝ)^bits + (2 * order : ℕ) / (2 : ℝ)^bits :=
      add_le_add (weightedEntry_source_error security bits order hroom output) hkernel
    _ = _ := by push_cast; ring

end
end CurrentAFT.RootSignedMassProgram
