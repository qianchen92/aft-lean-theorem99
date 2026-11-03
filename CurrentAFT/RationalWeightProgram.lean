import CurrentAFT.NumericalWeightEvaluation
import CurrentAFT.CyclePatternProgram

/-! # Finite rational evaluation of the current public weight

The array contains every joint kernel entry. The recursion applies the
computed paired operator to each primary slot, then averages distinct
choices in the two pools. All arithmetic in the program is rational.
-/
namespace CurrentAFT.RationalWeightProgram
open AFT ActualControls ControlCoordinates GradedControlAlgebra CalibrationPointCoordinates
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

abbrev RawTable (order : ℕ) := (arity : TruncatedArity order) →
  (Fin arity.val.1.val → ℕ) → (Fin arity.val.2.val → ℕ) → ℚ

def pairedTensor (security bits : ℕ) : (count : ℕ) → ((Fin count → ℕ) → ℚ) →
    (Fin count → ℕ × ℕ) → ℚ
  | 0, kernel, _ => kernel Fin.elim0
  | count + 1, kernel, groups =>
      RationalPairedLiftProgram.current security bits
        (fun color => pairedTensor security bits count (fun rest => kernel (Fin.cons color rest))
          (fun index => groups index.succ)) (groups 0).1 (groups 0).2

def average (r s primaryPool bodyPool : ℕ)
    (kernel : (Fin r → ℕ × ℕ) → (Fin s → ℕ) → ℚ)
    (groups : Fin primaryPool → ℕ × ℕ) (centers : Fin bodyPool → ℕ) : ℚ :=
  letI := CyclePatternProgram.selectionFintype primaryPool r
  letI := CyclePatternProgram.selectionFintype bodyPool s
  (∑ selection : (Fin r ↪ Fin primaryPool) × (Fin s ↪ Fin bodyPool),
    kernel (groups ∘ selection.1) (centers ∘ selection.2)) /
      ((primaryPool.descFactorial r : ℚ) * (bodyPool.descFactorial s : ℚ))

def current (security bits order primaryPool bodyPool : ℕ) (table : RawTable order)
    (groups : Fin primaryPool → ℕ × ℕ) (centers : Fin bodyPool → ℕ) : ℚ :=
  table (zeroArity order) Fin.elim0 Fin.elim0 +
    ∑ arity : PositiveArity order,
      average arity.val.1.val arity.val.2.val primaryPool bodyPool
        (fun selected selectedCenters => pairedTensor security bits arity.val.1.val
          (fun colors => table (positiveArity order arity) colors selectedCenters) selected) groups centers

noncomputable section
open scoped Classical
local instance weightFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

def realTable (security order : ℕ) (table : RawTable order) :
    PointTable (ActualControls.Palette security) (SafePalette security) order :=
  fun point => table point.1 (fun index => (point.2.1 index).val) (fun index => (point.2.2 index).val.val)

def groupValues (security : ℕ) (group : SafeControlGroups.SafeGroup security) : ℕ × ℕ :=
  (group.1.val, group.2.val.val)

theorem pairedTensor_cast (security bits count : ℕ) (kernel : (Fin count → ℕ) → ℚ)
    (groups : Fin count → SafeControlGroups.SafeGroup security) :
    (pairedTensor security bits count kernel (fun index => groupValues security (groups index)) : ℝ) =
      TensorChannel.apply count (fun _ => PairedScoreApproximation.approximate security bits)
        (fun colors => (kernel (fun index => (colors index).val) : ℝ)) groups := by
  induction count with
  | zero =>
      simp only [pairedTensor, TensorChannel.apply]
      exact congrArg (fun word : Fin 0 → ℕ => (kernel word : ℝ)) (Subsingleton.elim _ _)
  | succ count ih =>
      simp only [pairedTensor, groupValues]
      rw [RationalPairedLiftProgram.current_cast security bits _ (groups 0).1 (groups 0).2]
      change PairedScoreApproximation.approximate security bits
        (fun color => (pairedTensor security bits count (fun rest => kernel (Fin.cons color.val rest))
          (fun index => groupValues security (groups index.succ)) : ℝ)) (groups 0) = _
      simp_rw [ih]
      have hcons (color : ActualControls.Palette security) (rest : Fin count → ActualControls.Palette security) :
          (fun index : Fin (count + 1) => (Fin.cons (α := fun _ => ActualControls.Palette security) color rest index).val) = Fin.cons color.val (fun index => (rest index).val) := by
        funext index
        exact Fin.cases rfl (fun _ => rfl) index
      apply congrArg (fun score => PairedScoreApproximation.approximate security bits score (groups 0))
      funext color
      apply congrArg (fun profile => TensorChannel.apply count
        (fun _ => PairedScoreApproximation.approximate security bits) profile (fun index => groups index.succ))
      funext rest
      exact congrArg (fun word => (kernel word : ℝ)) (hcons color rest).symm

theorem average_cast (r s primaryPool bodyPool : ℕ)
    (kernel : (Fin r → ℕ × ℕ) → (Fin s → ℕ) → ℚ)
    (groups : Fin primaryPool → ℕ × ℕ) (centers : Fin bodyPool → ℕ) :
    (average r s primaryPool bodyPool kernel groups centers : ℝ) =
      twoPoolUStatistic primaryPool bodyPool (fun selected selectedCenters =>
        (kernel selected selectedCenters : ℝ)) groups centers := by
  unfold average twoPoolUStatistic
  simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_sum]
  apply congrArg (fun numerator : ℝ => numerator /
    ((primaryPool.descFactorial r : ℝ) * (bodyPool.descFactorial s : ℝ)))
  apply Finset.sum_congr (by ext selection; simp)
  intro selection _
  rfl

theorem current_cast (security bits order primaryPool bodyPool : ℕ) (table : RawTable order)
    (groups : Fin primaryPool → SafeControlGroups.SafeGroup security)
    (centers : Fin bodyPool → SafePalette security) :
    (current security bits order primaryPool bodyPool table
      (fun index => groupValues security (groups index)) (fun index => (centers index).val.val) : ℝ) =
      NumericalWeightEvaluation.evaluate security bits order primaryPool bodyPool
        (realTable security order table) groups centers := by
  unfold current NumericalWeightEvaluation.evaluate
  simp only [Rat.cast_add, Rat.cast_sum]
  apply congrArg₂ (· + ·)
  · unfold realTable
    apply congrArg (fun value : ℚ => (value : ℝ))
    apply congrArg₂ (table (zeroArity order))
    all_goals
      change (Fin.elim0 : Fin 0 → ℕ) = _
      exact Subsingleton.elim _ _
  apply Finset.sum_congr (by ext arity; simp)
  intro arity _
  rw [average_cast]
  unfold twoPoolUStatistic
  congr 1
  apply Finset.sum_congr rfl
  intro selection _
  exact pairedTensor_cast security bits arity.val.1.val _ (groups ∘ selection.1)

theorem current_error (security bits order primaryPool bodyPool : ℕ)
    (family : KernelFamily (ProposalPrimary.primaryLaw security) (bodyReference security) order)
    (table : RawTable order) (bound error : ℝ) (hb : 0 ≤ bound) (he : 0 ≤ error)
    (hfamily : ∀ point, |encode (ProposalPrimary.primaryLaw security) (bodyReference security) order family point| ≤ bound)
    (htable : ∀ point, |realTable security order table point -
      encode (ProposalPrimary.primaryLaw security) (bodyReference security) order family point| ≤ error)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤
      1/(4*(Parameters.modulus security:ℝ)))
    (groups : Fin primaryPool → SafeControlGroups.SafeGroup security)
    (centers : Fin bodyPool → SafePalette security) :
    |(current security bits order primaryPool bodyPool table
        (fun index => groupValues security (groups index)) (fun index => (centers index).val.val) : ℝ) -
      PhysicalSynthesis.coefficientWeight security order primaryPool bodyPool
        (familyToCoefficients (ProposalPrimary.primaryLaw security) (bodyReference security) order family)
        (fun index => SafeControlGroups.unwrap security (groups index)) centers| ≤
      error + (Fintype.card (PositiveArity order) : ℝ) *
        (NumericalWeightEvaluation.factor security^order *
          (error + order * NumericalWeightEvaluation.localError security bits * bound)) := by
  rw [current_cast]
  exact NumericalWeightEvaluation.evaluate_error security bits order primaryPool bodyPool family
    (realTable security order table) bound error hb he hfamily htable hprecision hbudget groups centers

end
end CurrentAFT.RationalWeightProgram
