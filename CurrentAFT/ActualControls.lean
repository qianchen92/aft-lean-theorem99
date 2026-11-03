import CurrentAFT.PairedResponse
import CurrentAFT.ControlCoordinates

/-!
# The actual positive reference controls

The primary and center laws constructed from the current numerical parameters
are supplied to the canonical coefficient space. Restricting the center law
to the safe alphabet discards only zero atoms. The inward anchor has the same
support, so its restriction is still a probability kernel. In particular,
positivity of these reference laws is a theorem, not an input certificate.
-/

namespace CurrentAFT.ActualControls

open AFT DiffuseProfiles ProposalPrimary
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base
  ProposalPrimary.primaryLaw ProposalPrimary.centerLaw
  InwardAnchor.smoothedAnchorLaw

abbrev Palette (security : ℕ) := Fin (Parameters.modulus security)

abbrev SafePalette (security : ℕ) :=
  {color : Palette security // InwardAnchor.SafeColor security color}

/-- Restriction to a support containing every positive atom preserves mass. -/
def supportedLaw {State : Type*} [Fintype State] (law : FiniteDist State)
    (safe : State → Prop) (hzero : ∀ state, ¬safe state → law.weight state = 0) :
    FiniteDist {state // safe state} where
  weight state := law.weight state.val
  nonneg state := law.nonneg state.val
  sum_one := by
    have hsplit := Fintype.sum_subtype_add_sum_subtype safe law.weight
    have houtside : (∑ state : {state // ¬safe state}, law.weight state.val) = 0 := by
      apply Finset.sum_eq_zero
      intro state _
      exact hzero state.val state.property
    rw [houtside, add_zero, law.sum_one] at hsplit
    exact hsplit

theorem supportedLaw_expectation {State : Type*} [Fintype State]
    (law : FiniteDist State) (safe : State → Prop)
    (hzero : ∀ state, ¬safe state → law.weight state = 0) (test : State → ℝ) :
    (supportedLaw law safe hzero).expectation (fun state => test state.val) =
      law.expectation test := by
  have hsplit := Fintype.sum_subtype_add_sum_subtype safe
    (fun state => law.weight state * test state)
  have houtside : (∑ state : {state // ¬safe state}, law.weight state.val * test state.val) = 0 := by
    apply Finset.sum_eq_zero
    intro state _
    rw [hzero state.val state.property, zero_mul]
  rw [houtside, add_zero] at hsplit
  exact hsplit

def bodyReference (security : ℕ) : FiniteDist (SafePalette security) :=
  supportedLaw (centerLaw security) (InwardAnchor.SafeColor security)
    (fun color hunsafe => by
      simp only [centerLaw]
      exact centerProfile_zero_outside security color hunsafe)

def anchorReference (security : ℕ) (color : Palette security) :
    FiniteDist (SafePalette security) :=
  supportedLaw (InwardAnchor.smoothedAnchorLaw security color)
    (InwardAnchor.SafeColor security)
    (InwardAnchor.smoothedAnchorLaw_zero_outside security color)

theorem primaryReference_positive (security : ℕ) (color : Palette security) :
    0 < (primaryLaw security).weight color := by
  have hq := FirstResponse.modulus_pos security
  exact (by positivity : (0 : ℝ) < 1 / (2 * (Parameters.modulus security : ℝ))).trans_le
    (by simpa only [primaryLaw] using primaryProfile_atom_lower security color)

theorem bodyReference_lower (security : ℕ) (color : SafePalette security) :
    1 / (2 * (Parameters.modulus security : ℝ)) ≤ (bodyReference security).weight color :=
  PairedResponse.centerLaw_safe_atom_lower security color.val color.property

theorem bodyReference_positive (security : ℕ) (color : SafePalette security) :
    0 < (bodyReference security).weight color := by
  have hq := FirstResponse.modulus_pos security
  exact (by positivity : (0 : ℝ) < 1 / (2 * (Parameters.modulus security : ℝ))).trans_le
    (bodyReference_lower security color)

theorem bodyReference_upper (security : ℕ) (color : SafePalette security) :
    (bodyReference security).weight color ≤ 4 / (Parameters.modulus security : ℝ) :=
  centerLaw_height security color.val

/-- This is the actual coefficient space with the two proved positive laws. -/
abbrev Coefficients (security order : ℕ) :=
  ControlCoordinates.CoefficientSpace (primaryLaw security) (bodyReference security) order

instance coefficients_finiteDimensional (security order : ℕ) :
    FiniteDimensional ℝ (Coefficients security order) := by infer_instance

/-- The finite representation of primary colors is equivalent to the paper's
`ZMod` representation. -/
noncomputable def primaryEquiv (security : ℕ) :
    Palette security ≃ ControlCoordinates.CurrentPrimaryAlphabet security :=
  (ZMod.finEquiv (Parameters.modulus security)).toEquiv

private theorem finEquiv_val (modulus : ℕ) [NeZero modulus] (color : Fin modulus) :
    ((ZMod.finEquiv modulus) color).val = color.val := by
  cases modulus with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ modulus => rfl

private theorem finEquiv_symm_val (modulus : ℕ) [NeZero modulus] (color : ZMod modulus) :
    ((ZMod.finEquiv modulus).symm color).val = color.val := by
  cases modulus with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ modulus => rfl

private noncomputable def safeResidueEquiv (modulus margin : ℕ) [NeZero modulus] :
    {color : Fin modulus // (margin : ℤ) ≤ color.val ∧
      (color.val : ℤ) < (modulus : ℤ) - margin} ≃
      ControlCoordinates.BodyAlphabet modulus margin where
  toFun color := ⟨(ZMod.finEquiv modulus) color.val, by
    rw [finEquiv_val]
    have h := color.property
    omega⟩
  invFun color := ⟨(ZMod.finEquiv modulus).symm color.val, by
    rw [finEquiv_symm_val]
    have h := color.property
    omega⟩
  left_inv color := by apply Subtype.ext; exact (ZMod.finEquiv modulus).left_inv color.val
  right_inv color := by apply Subtype.ext; exact (ZMod.finEquiv modulus).right_inv color.val

/-- The inclusive safe intervals coincide after changing residue notation. -/
noncomputable def bodyEquiv (security : ℕ) :
    SafePalette security ≃ ControlCoordinates.CurrentBodyAlphabet security :=
  safeResidueEquiv (Parameters.modulus security) (Parameters.safeMargin security)

def primaryResidueReference (security : ℕ) :
    FiniteDist (ControlCoordinates.CurrentPrimaryAlphabet security) :=
  (primaryLaw security).map (primaryEquiv security)

def bodyResidueReference (security : ℕ) :
    FiniteDist (ControlCoordinates.CurrentBodyAlphabet security) :=
  (bodyReference security).map (bodyEquiv security)

theorem primaryResidueReference_positive (security : ℕ)
    (color : ControlCoordinates.CurrentPrimaryAlphabet security) :
    0 < (primaryResidueReference security).weight color := by
  rw [primaryResidueReference, FiniteDist.map_equiv_weight]
  exact primaryReference_positive security _

theorem bodyResidueReference_positive (security : ℕ)
    (color : ControlCoordinates.CurrentBodyAlphabet security) :
    0 < (bodyResidueReference security).weight color := by
  rw [bodyResidueReference, FiniteDist.map_equiv_weight]
  exact bodyReference_positive security _

end

end CurrentAFT.ActualControls
