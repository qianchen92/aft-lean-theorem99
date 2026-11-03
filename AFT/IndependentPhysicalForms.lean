import AFT.IndependentPolynomialReplacement
import AFT.PendingPrimaryExpansion

/-! # Physical paired polynomial channels and original-coordinate marking -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Color Output : Type*} [Fintype Color]
local instance independentPhysicalFormsUnitDecEq : DecidableEq Unit := Classical.decEq _

theorem polynomialLinear_profile_expansion (operator : (Color → ℝ) →ₗ[ℝ] Table Output)
    (profile : Color → ℝ) :
    operator profile=∑ color,MvPolynomial.C (profile color)*operator (Pi.single color 1) := by
  have he : profile=∑ color,profile color • (Pi.single color 1 : Color → ℝ) := by
    funext input
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.single_apply]
    simp
  conv_lhs => rw [he]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro color _
  rw [map_smul,MvPolynomial.smul_eq_C_mul]

theorem jointChannelPolynomial_singleton_linear (primary : FiniteDist Color)
    (operator : (Color → ℝ) →ₗ[ℝ] Table Output) (kernel : Color → ℝ) :
    jointChannelPolynomial (fun _ : Unit => primary) (fun _ color => operator (Pi.single color 1))
      (fun word => kernel (word ())) = operator (fun color => primary.weight color*kernel color) := by
  rw [polynomialLinear_profile_expansion]
  unfold jointChannelPolynomial
  rw [← (Equiv.funUnique Unit Color).symm.sum_comp]
  simp only [Fintype.prod_unique,Equiv.funUnique_symm_apply,uniqueElim_const]
  apply Finset.sum_congr rfl
  intro color _
  congr 2
  ring

end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration RepresentedPolynomial MixedKernel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance pendingPhysicalFormsUnitDecEq : DecidableEq Unit := Classical.decEq _
local instance pendingPhysicalFormsFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

def independentPairedPolynomialLinear (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark) :
    (Fin (Parameters.modulus n) → ℝ) →ₗ[ℝ] Table (Fin (Parameters.modulus n)) :=
  (centeredGeneratingLinear (actualReferenceLaw C n beta).weight).comp
    (∑ roots,(pairedRootReference n).weight roots • actualPairedChannel C n beta charts roots.1 roots.2 0)

theorem independentPairedPolynomialLinear_apply (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (profile : Fin (Parameters.modulus n) → ℝ) :
    independentPairedPolynomialLinear C n beta charts profile=
      centeredGeneratingLinear (actualReferenceLaw C n beta).weight (independentPairedNumerator C n beta charts profile) := by
  unfold independentPairedPolynomialLinear
  rw [LinearMap.comp_apply]
  congr 1
  funext word
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
    independentPairedNumerator,actualJointPairedNumerator,actualPairedChannel,LinearMap.coe_mk,AddHom.coe_mk]

def independentPairedForm (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (color : Fin (Parameters.modulus n)) : Table (Fin (Parameters.modulus n)) :=
  independentPairedPolynomialLinear C n beta charts (Pi.single color 1)

def pendingPhysicalForms (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (state : PendingInput (Fin (Parameters.modulus n))) :
    Fin (state.seed.primaryOrder+state.seed.bodyOrder) → Fin (Parameters.modulus n) → Table (Fin (Parameters.modulus n)) :=
  Fin.addCases (fun index => if index∈state.pending then independentPairedForm C n beta charts
      else channelForm (actualPrimaryChannel C n)) (fun _ => channelForm (actualBodyChannel n))

def pendingPhysicalPolynomial (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (state : PendingInput (Fin (Parameters.modulus n))) : Table (Fin (Parameters.modulus n)) :=
  jointChannelPolynomial (inputReference (actualPrimaryLaw C n beta) (actualBodyLaw C n beta) state.seed)
    (pendingPhysicalForms C n beta charts state) state.seed.kernel

theorem pendingPhysicalPolynomial_empty (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (state : PendingInput (Fin (Parameters.modulus n))) (he : state.pending=∅) :
    pendingPhysicalPolynomial C n beta charts state=actualLeadingOutput C n beta (MvPolynomial.X state.seed) := by
  rw [actualLeadingOutput,outputHom_X,seedOutput_indexed,indexedOutput_joint]
  unfold pendingPhysicalPolynomial
  congr 1
  funext slot
  cases slot using Fin.addCases <;> simp [pendingPhysicalForms,seedChannel,he]

variable {Rest : Type} [Fintype Rest] [DecidableEq Rest]

theorem independentPairedForm_sum (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (other : Rest → FiniteDist (Fin (Parameters.modulus n)))
    (forms : Rest → Fin (Parameters.modulus n) → Table (Fin (Parameters.modulus n)))
    (kernel : Fin (Parameters.modulus n) → (Rest → Fin (Parameters.modulus n)) → ℝ) :
    jointChannelPolynomial (Sum.elim (fun _ : Unit => actualPrimaryLaw C n beta) other)
      (Sum.elim (fun _ : Unit => independentPairedForm C n beta charts) forms) (singletonJoin kernel)=
      polynomialRemainingOutput other forms (fun rest => centeredGeneratingLinear (actualReferenceLaw C n beta).weight
        (independentPairedNumerator C n beta charts (fun color => (actualPrimaryLaw C n beta).weight color*kernel color rest))) := by
  rw [jointChannelPolynomial_sum]
  unfold polynomialRemainingOutput
  simp only [LinearMap.coe_mk,AddHom.coe_mk]
  apply Finset.sum_congr rfl
  intro rest _
  congr 2
  have hs : (fun word : Unit → Fin (Parameters.modulus n) => singletonJoin kernel (Sum.elim word rest))=
      fun word => kernel (word ()) rest := by funext word; rfl
  rw [hs]
  change jointChannelPolynomial _ (fun _ color => independentPairedPolynomialLinear C n beta charts (Pi.single color 1)) _=_
  exact (jointChannelPolynomial_singleton_linear (actualPrimaryLaw C n beta)
    (independentPairedPolynomialLinear C n beta charts) (fun color => kernel color rest)).trans
      (independentPairedPolynomialLinear_apply C n beta charts _)

end
end AFT.V7Calibration
