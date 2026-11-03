import CurrentAFT.CurrentFlagIteration

/-!
# Executable finite arrays for the simultaneous flag repair

Every protected input on the zero-first-coordinate line is excluded from
the defect.  This differs from a repair with a single distinguished input.
The definitions use finite sums, rational arithmetic, and explicit Boolean
masks.  Their semantics are the canonical rational response of this branch.
-/

namespace CurrentAFT.CurrentFlagArray

open AFT AFT.BoundaryCalibration CurrentRationalFlagLaw CurrentFlagIteration
open scoped BigOperators

variable {C I : Type*} [Fintype C] [Fintype I] [DecidableEq C]

def mean (charts : ℕ) (profile : Fin charts → ℚ) : ℚ := (∑ point, profile point) / charts

def conditional (charts : ℕ) (feature : Fin charts → C) (profile : Fin charts → ℚ) (color : C) : ℚ :=
  (Fintype.card C : ℚ) * mean charts (fun point => if feature point = color then profile point else 0)

def component (charts : ℕ) (feature : Fin charts → C) (allowed : Finset C)
    (profile : Fin charts → ℚ) (point : Fin charts) : ℚ :=
  if feature point ∈ allowed then conditional charts feature profile (feature point) -
    (∑ color ∈ allowed, conditional charts feature profile color) / allowed.card else 0

def projection (charts : ℕ) (features : I → Fin charts → C) (allowed : I → Finset C)
    (profile : Fin charts → ℚ) (point : Fin charts) : ℚ :=
  mean charts profile + ∑ index, component charts (features index) (allowed index) profile point

def deletion (charts : ℕ) (features : I → Fin charts → C) (allowed : I → Finset C)
    (safe : Fin charts → Bool) (profile : Fin charts → ℚ) (point : Fin charts) : ℚ :=
  projection charts features allowed (fun input => if safe input then 0 else profile input) point

def defect (charts : ℕ) (features : I → Fin charts → C) (allowed : I → Finset C)
    (line : I → Bool) (spike : Fin charts → ℚ) (point : Fin charts) : ℚ :=
  ∑ index, if line index then 0 else component charts (features index) (allowed index) spike point

def target (charts : ℕ) (features : I → Fin charts → C) (allowed : I → Finset C)
    (line : I → Bool) (atom : ℚ) (spike : Fin charts → ℚ) (point : Fin charts) : ℚ :=
  1 - atom / (1 - atom) * defect charts features allowed line spike point

def iterate (charts : ℕ) (features : I → Fin charts → C) (allowed : I → Finset C)
    (safe : Fin charts → Bool) (rhs : Fin charts → ℚ) : ℕ → Vector ℚ charts
  | 0 => Vector.replicate charts 0
  | steps + 1 =>
    let previous := iterate charts features allowed safe rhs steps
    Vector.ofFn (fun point => rhs point + deletion charts features allowed safe previous.get point)

def regular (charts : ℕ) (features : I → Fin charts → C) (allowed : I → Finset C)
    (line : I → Bool) (safe : Fin charts → Bool) (atom : ℚ) (spike : Fin charts → ℚ)
    (steps : ℕ) : Vector ℚ charts :=
  let raw := iterate charts features allowed safe (target charts features allowed line atom spike) steps
  Vector.ofFn (fun point => if safe point then raw.get point else 0)

noncomputable section
open scoped Classical
set_option maxHeartbeats 1200000

theorem mean_eq (charts : ℕ) (profile : Fin charts → ℚ) :
    mean charts profile = expectationQ profile := by
  simp only [mean, expectationQ, LinearMap.coe_mk, AddHom.coe_mk, Fintype.card_fin, div_eq_mul_inv]
  ring

theorem conditional_eq (charts : ℕ) (feature : Fin charts → C) (profile : Fin charts → ℚ) (color : C) :
    conditional charts feature profile color = conditionalQ feature profile color := by
  simp only [conditional, mean_eq, conditionalQ, LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  apply congrArg expectationQ
  funext point
  split_ifs <;> rfl

theorem component_eq (charts : ℕ) (feature : Fin charts → C) (allowed : Finset C)
    (profile : Fin charts → ℚ) (point : Fin charts) :
    component charts feature allowed profile point = featureProjectionQ feature allowed profile point := by
  simp only [component, conditional_eq, featureProjectionQ, LinearMap.comp_apply, LinearMap.funLeft_apply,
    centerAllowedQ, LinearMap.coe_mk, AddHom.coe_mk]
  split_ifs <;> rfl

theorem projection_eq (charts : ℕ) (features : I → Fin charts → C) (allowed : I → Finset C)
    (profile : Fin charts → ℚ) (point : Fin charts) :
    projection charts features allowed profile point = projectionQ features allowed profile point := by
  simp only [projection, mean_eq, component_eq, projectionQ, LinearMap.coe_mk, AddHom.coe_mk]

theorem deletion_eq (charts : ℕ) (features : I → Fin charts → C) (allowed : I → Finset C)
    (safe : Fin charts → Bool) (profile : Fin charts → ℚ) (point : Fin charts) :
    deletion charts features allowed safe profile point =
      projectionQ features allowed (badMaskQ (fun input => safe input = true) profile) point := by
  rw [deletion, projection_eq]
  apply congrArg (fun value => projectionQ features allowed value point)
  funext input
  simp only [badMaskQ, LinearMap.coe_mk, AddHom.coe_mk]
  split_ifs <;> rfl

theorem defect_eq (charts : ℕ) (features : I → Fin charts → C) (allowed : I → Finset C)
    (line : I → Bool) (spike : Fin charts → ℚ) :
    defect charts features allowed line spike = offLineDefectQ features allowed (fun index => line index = true) spike := by
  funext point
  simp only [defect, offLineDefectQ, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro index _
  split_ifs <;> first | rfl | exact component_eq charts _ _ _ _

theorem target_eq (charts : ℕ) (features : I → Fin charts → C) (allowed : I → Finset C)
    (line : I → Bool) (atom : ℚ) (spike : Fin charts → ℚ) :
    target charts features allowed line atom spike =
      1 - (atom / (1 - atom)) • offLineDefectQ features allowed (fun index => line index = true) spike := by
  rw [← defect_eq charts features allowed line spike]
  rfl

theorem iterate_eq (charts : ℕ) (features : I → Fin charts → C) (allowed : I → Finset C)
    (safe : Fin charts → Bool) (rhs : Fin charts → ℚ) (steps : ℕ) (point : Fin charts) :
    (iterate charts features allowed safe rhs steps).get point =
      CurrentFlagIteration.iterate features allowed (fun input => safe input = true) rhs steps point := by
  induction steps generalizing point with
  | zero => simp [iterate, CurrentFlagIteration.iterate, AFT.RationalNumerics.linearIteration]
  | succ steps ih =>
    simp only [iterate, Vector.get_ofFn]
    have he : (iterate charts features allowed safe rhs steps).get =
        CurrentFlagIteration.iterate features allowed (fun input => safe input = true) rhs steps := funext ih
    rw [he, deletion_eq]
    change _ = (rhs - AFT.RationalNumerics.matrixApply
      (CurrentFlagIteration.iterationMatrix features allowed (fun input => safe input = true))
      (CurrentFlagIteration.iterate features allowed (fun input => safe input = true) rhs steps)) point
    rw [CurrentFlagIteration.matrixApply_eq]
    simp only [responseQ, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, Pi.sub_apply]
    ring

theorem regular_eq (charts : ℕ) (features : I → Fin charts → C) (allowed : I → Finset C)
    (line : I → Bool) (safe : Fin charts → Bool) (atom : ℚ) (spike : Fin charts → ℚ)
    (steps : ℕ) (point : Fin charts) :
    (regular charts features allowed line safe atom spike steps).get point =
      CurrentFlagIteration.regularIterate features allowed (fun index => line index = true)
        (fun input => safe input = true) atom spike steps point := by
  simp only [regular, Vector.get_ofFn, CurrentFlagIteration.regularIterate]
  split_ifs <;> simp only [iterate_eq, target_eq]

end
end CurrentAFT.CurrentFlagArray
