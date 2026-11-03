import AFT.ChannelCentering
import AFT.FiniteDisintegration

/-! # Exact root-coordinate averaging and centering on joint control inputs -/
namespace CurrentAFT.RootCoordinateProjection
open AFT
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

variable {Index Root Control : Type*} [Fintype Index] [DecidableEq Index]
  [Fintype Root] [Fintype Control]

abbrev Input := (Index → Root) × Control

def reference (root : FiniteDist Root) (control : FiniteDist Control) :
    FiniteDist (Input (Index := Index) (Root := Root) (Control := Control)) :=
  (FiniteDist.independent (fun _ : Index => root)).prod control

def average (root : FiniteDist Root) (index : Index) :
    (Input (Index := Index) (Root := Root) (Control := Control) → ℝ) →ₗ[ℝ]
      (Input (Index := Index) (Root := Root) (Control := Control) → ℝ) where
  toFun score sample := root.expectation (fun value => score (Function.update sample.1 index value, sample.2))
  map_add' first second := by funext sample; exact FiniteDist.expectation_add root _ _
  map_smul' scalar score := by funext sample; exact FiniteDist.expectation_const_mul root scalar _

def center (root : FiniteDist Root) (index : Index) :
    (Input (Index := Index) (Root := Root) (Control := Control) → ℝ) →ₗ[ℝ]
      (Input (Index := Index) (Root := Root) (Control := Control) → ℝ) :=
  LinearMap.id - average root index

omit [Fintype Index] [Fintype Control] in
theorem average_apply (root : FiniteDist Root) (index : Index)
    (score : Input (Index := Index) (Root := Root) (Control := Control) → ℝ) (sample : Input) :
    average root index score sample = root.expectation (fun value =>
      score (Function.update sample.1 index value, sample.2)) := rfl

omit [Fintype Index] [Fintype Control] in
theorem center_apply (root : FiniteDist Root) (index : Index)
    (score : Input (Index := Index) (Root := Root) (Control := Control) → ℝ) (sample : Input) :
    center root index score sample = score sample - average root index score sample := rfl

def insert (index : Index) (value : Root) (rest : {other : Index // other ≠ index} → Root) : Index → Root :=
  (Equiv.funSplitAt index Root).symm (value, rest)

omit [Fintype Index] [Fintype Root] in
theorem update_insert (index : Index) (first second : Root)
    (rest : {other : Index // other ≠ index} → Root) :
    Function.update (insert index first rest) index second = insert index second rest := by
  funext other
  by_cases hequal : other = index
  · subst other
    simp [insert, Equiv.funSplitAt, Equiv.piSplitAt]
  · simp [insert, Equiv.funSplitAt, Equiv.piSplitAt, hequal]

theorem energy_split (root : FiniteDist Root) (control : FiniteDist Control) (index : Index)
    (score : Input (Index := Index) (Root := Root) (Control := Control) → ℝ) :
    (reference (Index := Index) root control).l2Sq score =
      ∑ ctrl, control.weight ctrl * ∑ rest : {other : Index // other ≠ index} → Root,
        (∏ other : {other : Index // other ≠ index}, root.weight (rest other)) *
          root.l2Sq (fun value => score (insert index value rest, ctrl)) := by
  cases Subsingleton.elim (inferInstance : DecidableEq Index) (Classical.decEq Index)
  unfold reference FiniteDist.l2Sq
  rw [FiniteDist.expectation_prod, FiniteDist.expectation_comm]
  change (∑ ctrl, control.weight ctrl * (FiniteDist.independent (fun _ : Index => root)).expectation
    (fun roots => score (roots, ctrl) ^ 2)) = _
  apply Finset.sum_congr rfl
  intro ctrl _
  apply congrArg (fun value => control.weight ctrl * value)
  have h := FiniteDist.expectation_independent_split (fun _ : Index => root) index
    (fun roots => score (roots, ctrl) ^ 2)
  exact h

theorem average_energy_le (root : FiniteDist Root) (control : FiniteDist Control) (index : Index)
    (score : Input (Index := Index) (Root := Root) (Control := Control) → ℝ) :
    (reference (Index := Index) root control).l2Sq (average root index score) ≤
      (reference (Index := Index) root control).l2Sq score := by
  rw [energy_split root control index, energy_split root control index]
  apply Finset.sum_le_sum
  intro ctrl _
  apply mul_le_mul_of_nonneg_left _ (control.nonneg ctrl)
  apply Finset.sum_le_sum
  intro rest _
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun other _ => root.nonneg (rest other))
  simp only [average_apply, update_insert, FiniteDist.l2Sq, FiniteDist.expectation_const]
  exact BlockFock.mean_square_le root _

theorem center_energy_le (root : FiniteDist Root) (control : FiniteDist Control) (index : Index)
    (score : Input (Index := Index) (Root := Root) (Control := Control) → ℝ) :
    (reference (Index := Index) root control).l2Sq (center root index score) ≤
      (reference (Index := Index) root control).l2Sq score := by
  rw [energy_split root control index, energy_split root control index]
  apply Finset.sum_le_sum
  intro ctrl _
  apply mul_le_mul_of_nonneg_left _ (control.nonneg ctrl)
  apply Finset.sum_le_sum
  intro rest _
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun other _ => root.nonneg (rest other))
  simp only [center_apply, average_apply, update_insert]
  exact TensorChannel.center_energy_le root (fun value => score (insert index value rest, ctrl))

omit [Fintype Index] [Fintype Control] in
theorem average_fixed_of_invariant (root : FiniteDist Root) (index : Index)
    (score : Input (Index := Index) (Root := Root) (Control := Control) → ℝ)
    (hinvariant : ∀ sample value, score (Function.update sample.1 index value, sample.2) = score sample) :
    average root index score = score := by
  funext sample
  simp only [average_apply, hinvariant, FiniteDist.expectation_const]

omit [Fintype Index] [Fintype Control] in
theorem center_fixed_of_centered (root : FiniteDist Root) (index : Index)
    (score : Input (Index := Index) (Root := Root) (Control := Control) → ℝ)
    (hcentered : ∀ sample : Input (Index := Index) (Root := Root) (Control := Control), root.expectation (fun value => score (Function.update sample.1 index value, sample.2)) = 0) :
    center root index score = score := by
  funext sample
  simp only [center_apply, average_apply, hcentered, sub_zero]

omit [Fintype Index] [Fintype Control] in
theorem average_idempotent (root : FiniteDist Root) (index : Index)
    (score : Input (Index := Index) (Root := Root) (Control := Control) → ℝ) :
    average root index (average root index score) = average root index score := by
  funext sample
  simp only [average_apply, Function.update_idem, FiniteDist.expectation_const]

omit [Fintype Index] [Fintype Control] in
theorem center_mean_zero (root : FiniteDist Root) (index : Index)
    (score : Input (Index := Index) (Root := Root) (Control := Control) → ℝ) :
    average root index (center root index score) = 0 := by
  change average root index (score - average root index score) = 0
  rw [map_sub, average_idempotent, sub_self]

omit [Fintype Index] [Fintype Control] in
theorem average_commute (root : FiniteDist Root) (first second : Index) (hne : first ≠ second)
    (score : Input (Index := Index) (Root := Root) (Control := Control) → ℝ) :
    average root first (average root second score) = average root second (average root first score) := by
  funext sample
  simp only [average_apply]
  rw [FiniteDist.expectation_comm]
  apply congrArg root.expectation
  funext secondValue
  apply congrArg root.expectation
  funext firstValue
  rw [Function.update_comm hne]

omit [Fintype Index] [Fintype Control] in
theorem average_center_commute (root : FiniteDist Root) (first second : Index) (hne : first ≠ second)
    (score : Input (Index := Index) (Root := Root) (Control := Control) → ℝ) :
    average root first (center root second score) = center root second (average root first score) := by
  change average root first (score - average root second score) =
    average root first score - average root second (average root first score)
  rw [map_sub, average_commute root first second hne]

omit [Fintype Index] [Fintype Control] in
theorem center_commute (root : FiniteDist Root) (first second : Index) (hne : first ≠ second)
    (score : Input (Index := Index) (Root := Root) (Control := Control) → ℝ) :
    center root first (center root second score) = center root second (center root first score) := by
  change center root second score - average root first (center root second score) =
    center root second (score - average root first score)
  rw [map_sub, average_center_commute root first second hne]

def coordinate (root : FiniteDist Root) (index : Index) (tagged : Bool) :
    (Input (Index := Index) (Root := Root) (Control := Control) → ℝ) →ₗ[ℝ]
      (Input (Index := Index) (Root := Root) (Control := Control) → ℝ) :=
  if tagged then center root index else average root index

theorem coordinate_energy_le (root : FiniteDist Root) (control : FiniteDist Control) (index : Index)
    (tagged : Bool) (score : Input (Index := Index) (Root := Root) (Control := Control) → ℝ) :
    (reference (Index := Index) root control).l2Sq (coordinate root index tagged score) ≤
      (reference (Index := Index) root control).l2Sq score := by
  cases tagged
  · exact average_energy_le root control index score
  · exact center_energy_le root control index score

omit [Fintype Index] [Fintype Control] in
theorem coordinate_commute (root : FiniteDist Root) (first second : Index) (hne : first ≠ second)
    (firstTag secondTag : Bool) (score : Input (Index := Index) (Root := Root) (Control := Control) → ℝ) :
    coordinate root first firstTag (coordinate root second secondTag score) =
      coordinate root second secondTag (coordinate root first firstTag score) := by
  cases firstTag <;> cases secondTag
  · exact average_commute root first second hne score
  · exact average_center_commute root first second hne score
  · exact (average_center_commute root second first hne.symm score).symm
  · exact center_commute root first second hne score

def sequence (root : FiniteDist Root) : List (Index × Bool) →
    ((Input (Index := Index) (Root := Root) (Control := Control) → ℝ) →ₗ[ℝ]
      (Input (Index := Index) (Root := Root) (Control := Control) → ℝ))
  | [] => LinearMap.id
  | (index, tagged) :: rest => (coordinate root index tagged).comp (sequence root rest)

theorem sequence_energy_le (root : FiniteDist Root) (control : FiniteDist Control)
    (coordinates : List (Index × Bool)) (score : Input (Index := Index) (Root := Root) (Control := Control) → ℝ) :
    (reference (Index := Index) root control).l2Sq (sequence root coordinates score) ≤
      (reference (Index := Index) root control).l2Sq score := by
  induction coordinates with
  | nil => exact le_rfl
  | cons item rest ih =>
    exact (coordinate_energy_le root control item.1 item.2 (sequence root rest score)).trans ih

omit [Fintype Index] [Fintype Control] in
theorem sequence_fixed (root : FiniteDist Root) (coordinates : List (Index × Bool))
    (score : Input (Index := Index) (Root := Root) (Control := Control) → ℝ)
    (hfixed : ∀ item ∈ coordinates, coordinate root item.1 item.2 score = score) :
    sequence root coordinates score = score := by
  induction coordinates with
  | nil => rfl
  | cons item rest ih =>
    change coordinate root item.1 item.2 (sequence root rest score) = score
    rw [ih (fun other hother => hfixed other (List.mem_cons_of_mem item hother))]
    exact hfixed item List.mem_cons_self

end
end CurrentAFT.RootCoordinateProjection
