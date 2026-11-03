import AFT.FiniteJointExpectation
import AFT.RootSlice

/-! # Exact finite disintegration on the positive-probability public cells -/
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {State Record Output : Type*} [Fintype State] [Fintype Record] [Fintype Output]

omit [Fintype Record] [Fintype Output] in
theorem sum_positive_support (law : FiniteDist State) (value : State → ℝ)
    (hzero : ∀ point, law.weight point = 0 → value point = 0) :
    (∑ point : {point // 0 < law.weight point}, value point.val) = ∑ point, value point := by
  have hz : (∑ point : {point // ¬ 0 < law.weight point}, value point.val) = 0 := by
    apply Finset.sum_eq_zero
    intro point _
    exact hzero point.val (le_antisymm (le_of_not_gt point.property) (law.nonneg point.val))
  have hh := Fintype.sum_subtype_add_sum_subtype (fun point => 0 < law.weight point) value
  rwa [hz, add_zero] at hh

omit [Fintype Record] [Fintype Output] in
/-- Removing zero-mass states is exact, with no renormalization. -/
def positiveSupportLaw (law : FiniteDist State) : FiniteDist {point // 0 < law.weight point} where
  weight point := law.weight point.val
  nonneg point := law.nonneg point.val
  sum_one := (sum_positive_support law law.weight (by intro point hz; exact hz)).trans law.sum_one

omit [Fintype Record] [Fintype Output] in
theorem positiveSupportLaw_map (law : FiniteDist State) :
    (positiveSupportLaw law).map Subtype.val = law := by
  ext point
  rw [map_weight]
  change (∑ source : {point // 0 < law.weight point}, if source.val = point then law.weight source.val else 0) = _
  rw [sum_positive_support law (fun source => if source = point then law.weight source else 0) (by intro source hz; simp [hz])]
  simp

omit [Fintype Output] in
/-- The entire retained public record is the skeleton; impossible cells
are excluded, so all later conditional means are meaningful. -/
def recordSkeleton (law : FiniteDist State) (record : State → Record) :=
  positiveSupportLaw (law.map record)

omit [Fintype Output] in
def recordConditional (law : FiniteDist State) (record : State → Record)
    (cell : {value // 0 < (law.map record).weight value}) : FiniteDist State :=
  law.condition (fun point => record point = cell.val) cell.property

omit [Fintype Output] in
theorem recordSkeleton_disintegration (law : FiniteDist State) (record : State → Record) :
    (recordSkeleton law record).mix (recordConditional law record) = law := by
  ext point
  change (∑ cell : {value // 0 < (law.map record).weight value},
    (law.map record).weight cell.val *
      ((if record point = cell.val then law.weight point else 0) / (law.map record).weight cell.val)) = _
  have hcancel (cell : {value // 0 < (law.map record).weight value}) :
      (law.map record).weight cell.val *
        ((if record point = cell.val then law.weight point else 0) / (law.map record).weight cell.val) =
        (if record point = cell.val then law.weight point else 0) :=
    mul_div_cancel₀ _ cell.property.ne'
  simp_rw [hcancel]
  have hz (value : Record) (hzero : (law.map record).weight value = 0) :
      (if record point = value then law.weight point else 0) = 0 := by
    split_ifs with he
    · by_contra hne
      have hp : 0 < law.weight point := lt_of_le_of_ne (law.nonneg point) (Ne.symm hne)
      have hh := law.eventMass_positive_of_atom (fun source => record source = value) point he hp
      change 0 < (law.map record).weight value at hh
      rw [hzero] at hh
      exact (lt_irrefl _ hh)
    · rfl
  rw [sum_positive_support (law.map record) (fun value => if record point = value then law.weight point else 0) hz]
  simp

omit [Fintype Record] in
theorem expectation_mix (law : FiniteDist State) (conditional : State → FiniteDist Output)
    (value : Output → ℝ) :
    (law.mix conditional).expectation value =
      law.expectation (fun point => (conditional point).expectation value) := by
  simp only [expectation, mix_weight, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

omit [Fintype Output] in
/-- Averaging conditional moments uses the original law exactly, even
when some public cells have arbitrarily small probability. -/
theorem recordSkeleton_expectation (law : FiniteDist State) (record : State → Record)
    (value : State → ℝ) :
    (recordSkeleton law record).expectation (fun cell => (recordConditional law record cell).expectation value) =
      law.expectation value := by
  rw [← expectation_mix, recordSkeleton_disintegration]

/-- Any additional randomness depending on the state can be drawn after
the public disintegration without changing its averaged test functions. -/
theorem recordSkeleton_joint_expectation (law : FiniteDist State) (record : State → Record)
    (conditional : State → FiniteDist Output) (value : State × Output → ℝ) :
    (recordSkeleton law record).expectation (fun cell =>
      (joint (recordConditional law record cell) conditional).expectation value) =
      (joint law conditional).expectation value := by
  simp only [expectation_joint]
  exact recordSkeleton_expectation law record _
end
end AFT.FiniteDist
