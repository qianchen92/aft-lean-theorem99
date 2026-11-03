import AFT.IndependentPublicMixedSeed
import AFT.PairedTableLinear

/-! # Rebundling input monomials preserves the full nonlinear independent polynomial -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Color Output : Type*} [Fintype Color]

def controlProductForms (primary body : Color → Table Output) :
    (seeds : List (InputSeed Color)) → ControlProductSlot seeds → Color → Table Output
  | [],slot => PEmpty.elim slot
  | _seed::rest,slot => Sum.elim (Fin.addCases (fun _ => primary) (fun _ => body))
      (controlProductForms primary body rest) slot

omit [Fintype Color] in
theorem controlProductForms_role (primary body : Color → Table Output)
    (seeds : List (InputSeed Color)) (slot : ControlProductSlot seeds) :
    controlProductForms primary body seeds slot=if controlProductRole seeds slot then primary else body := by
  induction seeds with
  | nil => exact PEmpty.elim slot
  | cons seed rest ih =>
    cases slot with
    | inr slot => exact ih slot
    | inl slot => cases slot using Fin.addCases <;> simp [controlProductForms,controlProductRole]

theorem controlProduct_joint_polynomial (primary body : FiniteDist Color)
    (first second : Color → Table Output) (seeds : List (InputSeed Color)) :
    jointChannelPolynomial (controlProductReference primary body seeds)
      (controlProductForms first second seeds) (controlProductKernel seeds)=
      (seeds.map (fun seed => jointChannelPolynomial (inputReference primary body seed)
        (Fin.addCases (fun _ : Fin seed.primaryOrder => first) (fun _ : Fin seed.bodyOrder => second)) seed.kernel)).prod := by
  induction seeds with
  | nil => simp [jointChannelPolynomial,ControlProductSlot,controlProductKernel]
  | cons seed rest ih =>
    have he := jointChannelPolynomial_tensor (inputReference primary body seed)
      (controlProductReference primary body rest)
      (Fin.addCases (fun _ : Fin seed.primaryOrder => first) (fun _ : Fin seed.bodyOrder => second))
      (controlProductForms first second rest) seed.kernel (controlProductKernel rest)
    change jointChannelPolynomial _ _ (MixedKernel.tensor seed.kernel (controlProductKernel rest))=_
    have ht : jointChannelPolynomial (controlProductReference primary body (seed::rest))
        (controlProductForms first second (seed::rest)) (MixedKernel.tensor seed.kernel (controlProductKernel rest))=
      jointChannelPolynomial (Sum.elim (inputReference primary body seed) (controlProductReference primary body rest))
        (Sum.elim (Fin.addCases (fun _ : Fin seed.primaryOrder => first) (fun _ : Fin seed.bodyOrder => second))
          (controlProductForms first second rest)) (MixedKernel.tensor seed.kernel (controlProductKernel rest)) := by
      unfold jointChannelPolynomial
      apply Finset.sum_congr (by ext word; simp)
      intro word _
      rfl
    rw [ht,he,ih]
    rfl

end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance independentProductPolynomialFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance independentProductPolynomialSumDecEq {First Second : Type*} : DecidableEq (First ⊕ Second) := Classical.decEq _

/-- This is the original entire joint polynomial, not only its linear
response; the finite changes of input coordinate names preserve it exactly. -/
theorem pendingPhysicalPolynomial_mixedProductSeed (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (seeds : List (InputSeed (Fin (Parameters.modulus n)))) :
    pendingPhysicalPolynomial C n beta charts (initialPendingInput (mixedProductSeed seeds))=
      (seeds.map (fun seed => pendingPhysicalPolynomial C n beta charts (initialPendingInput seed))).prod := by
  rw [mixedProductSeed,pendingPhysicalPolynomial_mixedFiniteSeed]
  have he := jointChannelPolynomial_equiv (controlPoolEquiv seeds).symm
    (controlProductReference (actualPrimaryLaw C n beta) (actualBodyLaw C n beta) seeds)
    (controlProductForms (independentPairedForm C n beta charts) (channelForm (actualBodyChannel n)) seeds)
    (controlProductKernel seeds)
  have hf : (fun slot => controlProductForms (independentPairedForm C n beta charts)
      (channelForm (actualBodyChannel n)) seeds (controlPoolEquiv seeds slot))=
      Sum.elim (fun _ : ControlPrimarySlot seeds => independentPairedForm C n beta charts)
        (fun _ : ControlBodySlot seeds => channelForm (actualBodyChannel n)) := by
    funext slot
    cases slot with
    | inl slot => simp [controlPoolEquiv,controlProductForms_role,slot.property]
    | inr slot => simp [controlPoolEquiv,controlProductForms_role,slot.property]
  simp only [Equiv.symm_symm,controlPool_reference,hf] at he
  apply he.trans
  rw [controlProduct_joint_polynomial]
  congr 1
  apply List.map_congr_left
  intro seed _
  unfold pendingPhysicalPolynomial
  congr 1
  funext slot
  cases slot using Fin.addCases <;> simp [pendingPhysicalForms,initialPendingInput]

theorem pendingPhysicalPolynomial_mixedMonomialSeed (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (powers : InputSeed (Fin (Parameters.modulus n)) →₀ ℕ) :
    pendingPhysicalPolynomial C n beta charts (initialPendingInput (mixedMonomialSeed powers))=
      powers.prod (fun seed count => (pendingPhysicalPolynomial C n beta charts (initialPendingInput seed))^count) := by
  rw [mixedMonomialSeed,pendingPhysicalPolynomial_mixedProductSeed,monomialOccurrences_product]

theorem pendingPhysicalPolynomial_mixed_singleton (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (seed : InputSeed (Fin (Parameters.modulus n))) :
    pendingPhysicalPolynomial C n beta charts (initialPendingInput (mixedMonomialSeed (Finsupp.single seed 1)))=
      pendingPhysicalPolynomial C n beta charts (initialPendingInput seed) := by
  rw [mixedMonomialSeed,monomialOccurrences_single,pendingPhysicalPolynomial_mixedProductSeed]
  simp

end
end AFT.V7Calibration
