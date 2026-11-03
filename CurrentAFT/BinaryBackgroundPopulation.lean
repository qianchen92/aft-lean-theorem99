import CurrentAFT.BinaryLegBackground
import CurrentAFT.BinaryBackgroundPopulationCounts
import CurrentAFT.BinaryPopulationSemantics

/-! # The complete original fixed-queue background, executed on binary data -/
namespace CurrentAFT.BinaryBackgroundPopulation
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open BinaryFamilyProduct FixedFamilyPrograms
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

inductive Role where | free | queue | leg deriving DecidableEq

def population (role : Role) (counts : BinaryBackgroundPopulationCounts.Counts) : ℕ :=
  match role with | .free => counts.free | .queue => counts.queue | .leg => counts.leg
def idealPopulation (role : Role) (security : ℕ) : ℕ :=
  match role with
  | .free => RationalBackgroundPopulationProgram.freeCount security
  | .queue => (PublicParameterProgram.modulus security).count
  | .leg => (security+2)^128

def atom (role : Role) (security bits order : ℕ) (programs : List (Entry order)) (queue : IntegerBits) : CoefficientProgram order :=
  match role with
  | .free => BinaryBackgroundLeaves.current .free security bits order IntegerBits.zero
  | .queue => BinaryBackgroundLeaves.current .translation security bits order queue
  | .leg => BinaryLegBackground.current security bits order programs
def atomIdeal (role : Role) (security bits order : ℕ) (queue : ℤ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  match role with
  | .free => RationalBackgroundProgram.free security bits order
  | .queue => RationalBackgroundProgram.translation security bits order queue
  | .leg => RationalLegBackgroundProgram.current security bits order

def factor (role : Role) (security bits order : ℕ) (programs : List (Entry order)) (queue : IntegerBits) : CoefficientProgram order :=
  fun arity inputs centers =>
    let counts := BinaryBackgroundPopulationCounts.current security
    let result := BinaryFamilyBinomial.current order (population role counts) programs
      (atom role security bits order programs queue) arity inputs centers
    ⟨result.value,counts.work+result.work+2⟩
def factorIdeal (role : Role) (security bits order : ℕ) (queue : ℤ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  RationalFamilyProductProgram.binomial order (idealPopulation role security) (atomIdeal role security bits order queue)

def freeQueue (security bits order : ℕ) (programs : List (Entry order)) (queue : IntegerBits) : CoefficientProgram order :=
  BinaryFamilyArithmetic.multiply order programs (factor .free security bits order programs queue) (factor .queue security bits order programs queue)
def current (security bits order : ℕ) (programs : List (Entry order)) (queue : IntegerBits) : CoefficientProgram order :=
  BinaryFamilyArithmetic.multiply order programs (freeQueue security bits order programs queue) (factor .leg security bits order programs queue)

noncomputable section
theorem population_value (role : Role) (security : ℕ) : population role (BinaryBackgroundPopulationCounts.current security)=idealPopulation role security := by
  have h := BinaryBackgroundPopulationCounts.current_value security
  cases role
  · exact h.1
  · exact h.2.1
  · exact h.2.2

theorem atom_value (role : Role) (security bits order : ℕ) (programs : List (Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs) (queue : IntegerBits)
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hi : ∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) (hb : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    (atom role security bits order programs queue arity inputs centers).value.decode=atomIdeal role security bits order queue.decode arity inputs.get centers.get := by
  cases role
  · exact BinaryBackgroundLeaves.current_value .free security bits order IntegerBits.zero arity inputs centers hi hb
  · exact BinaryBackgroundLeaves.current_value .translation security bits order queue arity inputs centers hi hb
  · exact BinaryLegBackground.current_value security bits order programs hcorrect hcomplete arity inputs centers hi hb

theorem factor_value (role : Role) (security bits order : ℕ) (programs : List (Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs) (queue : IntegerBits)
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hi : ∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) (hb : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    (factor role security bits order programs queue arity inputs centers).value.decode=factorIdeal role security bits order queue.decode arity inputs.get centers.get := by
  unfold factor
  rw [BinaryPopulationSemantics.binomial_value order _ (BinaryFirstInverseProgram.colors security) programs hcorrect hcomplete _ _
    (atom_value role security bits order programs hcorrect hcomplete queue) arity inputs centers hi hb,population_value]
  rfl

theorem freeQueue_value (security bits order : ℕ) (programs : List (Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs) (queue : IntegerBits)
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hi : ∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) (hb : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    (freeQueue security bits order programs queue arity inputs centers).value.decode=
      RationalFamilyProductProgram.product order (factorIdeal .free security bits order queue.decode)
        (factorIdeal .queue security bits order queue.decode) arity inputs.get centers.get :=
  BinaryFamilyValidSemantics.multiply_value order (BinaryFirstInverseProgram.colors security) programs hcorrect hcomplete _ _ _ _
    (factor_value .free security bits order programs hcorrect hcomplete queue)
    (factor_value .queue security bits order programs hcorrect hcomplete queue) arity inputs centers hi hb

theorem current_value (security bits order : ℕ) (programs : List (Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs) (queue : IntegerBits)
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hi : ∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) (hb : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    (current security bits order programs queue arity inputs centers).value.decode=
      RationalBackgroundPopulationProgram.current security bits order queue.decode arity inputs.get centers.get :=
  BinaryFamilyValidSemantics.multiply_value order (BinaryFirstInverseProgram.colors security) programs hcorrect hcomplete _ _ _ _
    (freeQueue_value security bits order programs hcorrect hcomplete queue)
    (factor_value .leg security bits order programs hcorrect hcomplete queue) arity inputs centers hi hb

noncomputable def atomHeightPolynomial (role : Role) (order : ℕ) (programs : List (Entry order)) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  match role with
  | .free => BinaryBackgroundLeaves.heightPolynomial .free precision queueBits
  | .queue => BinaryBackgroundLeaves.heightPolynomial .translation precision queueBits
  | .leg => BinaryLegBackground.heightPolynomial order programs precision
noncomputable def atomWorkPolynomial (role : Role) (order : ℕ) (programs : List (Entry order)) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  match role with
  | .free => BinaryBackgroundLeaves.workPolynomial .free order precision queueBits
  | .queue => BinaryBackgroundLeaves.workPolynomial .translation order precision queueBits
  | .leg => BinaryLegBackground.workPolynomial order programs precision
noncomputable def factorHeightPolynomial (role : Role) (order : ℕ) (programs : List (Entry order)) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyBinomial.heightPolynomial order programs BinaryProposalMetadata.sizePolynomial (atomHeightPolynomial role order programs precision queueBits)
noncomputable def factorWorkPolynomial (role : Role) (order : ℕ) (programs : List (Entry order)) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryBackgroundPopulationCounts.workPolynomial+
    BinaryFamilyBinomial.workPolynomial order programs BinaryProposalMetadata.sizePolynomial
      (atomHeightPolynomial role order programs precision queueBits) (atomWorkPolynomial role order programs precision queueBits)+2
noncomputable def freeQueueHeightPolynomial (order : ℕ) (programs : List (Entry order)) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyArithmetic.heightPolynomial order programs
    (factorHeightPolynomial .free order programs precision queueBits+factorHeightPolynomial .queue order programs precision queueBits)
noncomputable def freeQueueWorkPolynomial (order : ℕ) (programs : List (Entry order)) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyArithmetic.workPolynomial order programs
    (factorHeightPolynomial .free order programs precision queueBits+factorHeightPolynomial .queue order programs precision queueBits)
    (factorWorkPolynomial .free order programs precision queueBits+factorWorkPolynomial .queue order programs precision queueBits)
noncomputable def heightPolynomial (order : ℕ) (programs : List (Entry order)) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyArithmetic.heightPolynomial order programs
    (freeQueueHeightPolynomial order programs precision queueBits+factorHeightPolynomial .leg order programs precision queueBits)
noncomputable def workPolynomial (order : ℕ) (programs : List (Entry order)) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyArithmetic.workPolynomial order programs
    (freeQueueHeightPolynomial order programs precision queueBits+factorHeightPolynomial .leg order programs precision queueBits)
    (freeQueueWorkPolynomial order programs precision queueBits+factorWorkPolynomial .leg order programs precision queueBits)

theorem atom_bounds (role : Role) (security order : ℕ) (programs : List (Entry order)) (precision queueBits : Polynomial ℕ)
    (queue : IntegerBits) (hq : queue.digits.length ≤ queueBits.eval security)
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hi : ∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) (hb : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    HeightBound (atom role security (precision.eval security) order programs queue arity inputs centers).value.decode
      ((atomHeightPolynomial role order programs precision queueBits).eval security) ∧
    (atom role security (precision.eval security) order programs queue arity inputs centers).work ≤
      (atomWorkPolynomial role order programs precision queueBits).eval security := by
  cases role
  · exact BinaryBackgroundLeaves.current_bounds .free security order precision queueBits IntegerBits.zero (by simp [IntegerBits.zero]) arity inputs centers hi hb
  · exact BinaryBackgroundLeaves.current_bounds .translation security order precision queueBits queue hq arity inputs centers hi hb
  · exact BinaryLegBackground.current_bounds security order programs precision arity inputs centers hi hb

theorem factor_bounds (role : Role) (security order : ℕ) (programs : List (Entry order)) (precision queueBits : Polynomial ℕ)
    (queue : IntegerBits) (hq : queue.digits.length ≤ queueBits.eval security)
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hi : ∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) (hb : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    HeightBound (factor role security (precision.eval security) order programs queue arity inputs centers).value.decode
      ((factorHeightPolynomial role order programs precision queueBits).eval security) ∧
    (factor role security (precision.eval security) order programs queue arity inputs centers).work ≤
      (factorWorkPolynomial role order programs precision queueBits).eval security := by
  let counts := BinaryBackgroundPopulationCounts.current security
  have hp : population role counts ≤ BinaryProposalMetadata.sizePolynomial.eval security := by
    rw [BinaryProposalMetadata.sizePolynomial_eval]
    have h := BinaryBackgroundPopulationCounts.current_sizes security
    cases role
    · exact h.1
    · exact h.2.1
    · exact h.2.2
  have h := BinaryFamilyBinomial.polynomial_bounds order (population role counts) (BinaryFirstInverseProgram.colors security) security programs
    (atom role security (precision.eval security) order programs queue) BinaryProposalMetadata.sizePolynomial
    (atomHeightPolynomial role order programs precision queueBits) (atomWorkPolynomial role order programs precision queueBits) hp
    (atom_bounds role security order programs precision queueBits queue hq) arity inputs centers hi hb
  refine ⟨h.1,?_⟩
  have wc := BinaryBackgroundPopulationCounts.current_work security
  change counts.work+(BinaryFamilyBinomial.current _ _ _ _ _ _ _).work+2 ≤ _
  simp only [factorWorkPolynomial,Polynomial.eval_add,Polynomial.eval_ofNat]
  dsimp only [counts] at h ⊢
  omega

theorem freeQueue_bounds (security order : ℕ) (programs : List (Entry order)) (precision queueBits : Polynomial ℕ)
    (queue : IntegerBits) (hq : queue.digits.length ≤ queueBits.eval security)
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hi : ∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) (hb : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    HeightBound (freeQueue security (precision.eval security) order programs queue arity inputs centers).value.decode
      ((freeQueueHeightPolynomial order programs precision queueBits).eval security) ∧
    (freeQueue security (precision.eval security) order programs queue arity inputs centers).work ≤
      (freeQueueWorkPolynomial order programs precision queueBits).eval security :=
  BinaryCoefficientOperations.multiply_bounds order (BinaryFirstInverseProgram.colors security) security programs _ _ _ _ _ _
    (factor_bounds .free security order programs precision queueBits queue hq)
    (factor_bounds .queue security order programs precision queueBits queue hq) arity inputs centers hi hb

theorem current_bounds (security order : ℕ) (programs : List (Entry order)) (precision queueBits : Polynomial ℕ)
    (queue : IntegerBits) (hq : queue.digits.length ≤ queueBits.eval security)
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hi : ∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) (hb : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    HeightBound (current security (precision.eval security) order programs queue arity inputs centers).value.decode
      ((heightPolynomial order programs precision queueBits).eval security) ∧
    (current security (precision.eval security) order programs queue arity inputs centers).work ≤
      (workPolynomial order programs precision queueBits).eval security :=
  BinaryCoefficientOperations.multiply_bounds order (BinaryFirstInverseProgram.colors security) security programs _ _ _ _ _ _
    (freeQueue_bounds security order programs precision queueBits queue hq)
    (factor_bounds .leg security order programs precision queueBits queue hq) arity inputs centers hi hb

end
end CurrentAFT.BinaryBackgroundPopulation
