import AFT.RepresentedControlKernel
import AFT.MixedReindex
import AFT.ActualFiniteControlTail

/-! # Literal seed products as the actual finite physical control input -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance representedFiniteKernelFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {Color : Type*} [Fintype Color]

def controlProductRole : (seeds : List (InputSeed Color)) → ControlProductSlot seeds → Bool
  | [], slot => PEmpty.elim slot
  | _seed :: rest, slot => Sum.elim (Fin.addCases (fun _ => true) (fun _ => false)) (controlProductRole rest) slot

omit [Fintype Color] in
/-- The analytic radius is paid exactly once for each body input, while
primary input coordinates carry no additional radius factor. -/
theorem controlProductRole_radius_prod (radius : ℝ) (seeds : List (InputSeed Color)) :
    (∏ slot : ControlProductSlot seeds, if controlProductRole seeds slot then 1 else radius) =
      radius ^ controlProductBodyOrder seeds := by
  induction seeds with
  | nil => simp [ControlProductSlot, controlProductBodyOrder]
  | cons seed rest ih =>
    change (∏ slot : Fin (seed.primaryOrder + seed.bodyOrder) ⊕ ControlProductSlot rest,
      if Sum.elim (Fin.addCases (fun _ => true) (fun _ => false)) (controlProductRole rest) slot then 1 else radius) = _
    rw [Fintype.prod_sum_type, Fin.prod_univ_add]
    simp only [Sum.elim_inl, Sum.elim_inr, Fin.addCases_left, Fin.addCases_right,
      Bool.false_eq_true, if_false, if_true, Finset.prod_const_one, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, one_mul, ih, controlProductBodyOrder,
      List.map_cons, List.sum_cons, pow_add]

omit [Fintype Color] in
theorem controlProductRate_role (primaryPool bodyPool : ℝ) (seeds : List (InputSeed Color))
    (slot : ControlProductSlot seeds) :
    controlProductRate primaryPool bodyPool seeds slot =
      if controlProductRole seeds slot then (Real.sqrt primaryPool)⁻¹ else (Real.sqrt bodyPool)⁻¹ := by
  induction seeds with
  | nil => exact PEmpty.elim slot
  | cons seed rest ih =>
    cases slot with
    | inr slot => exact ih slot
    | inl slot =>
      cases slot using Fin.addCases <;>
        simp only [controlProductRate, controlProductRole, Sum.elim_inl,
          inputRate, Fin.addCases_left, Fin.addCases_right, Bool.false_eq_true, if_false, if_true]

theorem controlProductReference_role (primary body : FiniteDist Color) (seeds : List (InputSeed Color))
    (slot : ControlProductSlot seeds) :
    controlProductReference primary body seeds slot = if controlProductRole seeds slot then primary else body := by
  induction seeds with
  | nil => exact PEmpty.elim slot
  | cons seed rest ih =>
    cases slot with
    | inr slot => exact ih slot
    | inl slot =>
      cases slot using Fin.addCases <;>
        simp only [controlProductReference, controlProductRole, Sum.elim_inl,
          inputReference, Fin.addCases_left, Fin.addCases_right, Bool.false_eq_true, if_false, if_true]

abbrev finiteControlCount (seeds : List (InputSeed Color)) : ℕ := Fintype.card (ControlProductSlot seeds)

def finiteControlRole (seeds : List (InputSeed Color)) : Fin (finiteControlCount seeds) → Bool :=
  fun slot => controlProductRole seeds ((Fintype.equivFin (ControlProductSlot seeds)).symm slot)

def finiteControlKernel (seeds : List (InputSeed Color)) : (Fin (finiteControlCount seeds) → Color) → ℝ :=
  fun word => controlProductKernel seeds (word ∘ Fintype.equivFin (ControlProductSlot seeds))

omit [Fintype Color] in
theorem finiteControlRole_radius_prod (radius : ℝ) (seeds : List (InputSeed Color)) :
    (∏ slot, if finiteControlRole seeds slot then 1 else radius) = radius ^ controlProductBodyOrder seeds := by
  have he := (Fintype.equivFin (ControlProductSlot seeds)).symm.prod_comp
    (fun slot => if controlProductRole seeds slot then (1 : ℝ) else radius)
  exact he.trans (controlProductRole_radius_prod radius seeds)

/-- The actual finite input word is only a renaming of the literal
disjoint seed occurrences, and thus retains exact canonicality. -/
theorem finiteControlKernel_canonical (primary body : FiniteDist Color) (seeds : List (InputSeed Color))
    (hc : ∀ seed ∈ seeds, Hoeffding.Canonical (inputReference primary body seed) Finset.univ seed.kernel) :
    Hoeffding.Canonical (fun slot => if finiteControlRole seeds slot then primary else body)
      Finset.univ (finiteControlKernel seeds) := by
  have he := MixedKernel.CoordinateTransport.canonical_equiv (Fintype.equivFin (ControlProductSlot seeds))
    (controlProductReference primary body seeds) (controlProductKernel seeds)
    (controlProductKernel_canonical primary body seeds hc)
  simpa only [controlProductReference_role, finiteControlRole, finiteControlKernel] using he

/-- Every mixed fiber and every pool rate is preserved by the literal
renaming into the finite physical control input. -/
theorem finiteControlKernel_activity (primary body : FiniteDist Color) (primaryPool bodyPool radius : ℝ)
    (seeds : List (InputSeed Color)) :
    radius ^ controlProductBodyOrder seeds *
      MixedKernel.activity
        (fun slot => controlProductRate primaryPool bodyPool seeds ((Fintype.equivFin (ControlProductSlot seeds)).symm slot))
        (fun slot => if finiteControlRole seeds slot then primary else body)
        (finiteControlKernel seeds) = controlProductActivity primary body primaryPool bodyPool radius seeds := by
  have he := MixedKernel.CoordinateTransport.activity_equiv (Fintype.equivFin (ControlProductSlot seeds))
    (controlProductRate primaryPool bodyPool seeds) (controlProductReference primary body seeds) (controlProductKernel seeds)
  have hh := congrArg (radius ^ controlProductBodyOrder seeds * ·) he
  simpa only [controlProductReference_role, finiteControlRole, finiteControlKernel, controlProductActivity] using hh

end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section

/-- A concrete seed-product monomial becomes the actual canonical physical
control once its distinct marked output slots have been placed. -/
def actualControlFromSeeds (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (seeds : List (InputSeed (Fin (Parameters.modulus parameter))))
    (selected : Finset (blockIndex parameter))
    (placement : ActualTaggedPlacement parameter (finiteControlCount seeds) (finiteControlRole seeds) selected)
    (hc : ∀ seed ∈ seeds, Hoeffding.Canonical
      (inputReference (actualPrimaryLaw cutoffScale parameter beta) (actualBodyLaw cutoffScale parameter beta) seed)
      Finset.univ seed.kernel) : ActualCanonicalControl cutoffScale parameter beta where
  count := finiteControlCount seeds
  role := finiteControlRole seeds
  selected := selected
  placement := placement
  kernel := finiteControlKernel seeds
  canonical := finiteControlKernel_canonical _ _ seeds hc

end
end AFT.V7Calibration
