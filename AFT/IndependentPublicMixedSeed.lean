import AFT.IndependentPublicNormalized
import AFT.PolynomialCoordinateOutput

/-! # Arbitrary public role orders realize the same complete mixed seed -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance publicMixedSeedFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance publicMixedSeedSumDecEq {First Second : Type*} : DecidableEq (First ⊕ Second) := Classical.decEq _
local instance publicMixedSeedSubtypeDecEq {First : Type*} {predicate : First → Prop} : DecidableEq (Subtype predicate) := Classical.decEq _
attribute [local instance] actualModulusNeZero

variable {Primary Body : Type} [Fintype Primary] [Fintype Body]

theorem pendingPhysicalPolynomial_mixedFiniteSeed (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (kernel : (Primary ⊕ Body → Fin (Parameters.modulus n)) → ℝ) :
    pendingPhysicalPolynomial C n beta charts (initialPendingInput (mixedFiniteSeed kernel))=
    jointChannelPolynomial
      (Sum.elim (fun _ : Primary => actualPrimaryLaw C n beta) (fun _ : Body => actualBodyLaw C n beta))
      (Sum.elim (fun _ : Primary => independentPairedForm C n beta charts) (fun _ : Body => channelForm (actualBodyChannel n))) kernel := by
  have hf : pendingPhysicalForms C n beta charts (initialPendingInput (mixedFiniteSeed kernel))=
      fun slot => Sum.elim (fun _ : Primary => independentPairedForm C n beta charts)
        (fun _ : Body => channelForm (actualBodyChannel n)) (mixedFiniteEquiv.symm slot) := by
    funext slot
    obtain ⟨slot,rfl⟩ := mixedFiniteEquiv.surjective slot
    cases slot with
    | inl slot => simp [mixedFiniteSeed,mixedFiniteEquiv,pendingPhysicalForms,initialPendingInput]
    | inr slot => simp [mixedFiniteSeed,mixedFiniteEquiv,pendingPhysicalForms,initialPendingInput]
  unfold pendingPhysicalPolynomial
  rw [hf]
  change jointChannelPolynomial (inputReference _ _ (mixedFiniteSeed kernel)) _ _=_
  rw [mixedFiniteSeed_reference]
  exact jointChannelPolynomial_equiv mixedFiniteEquiv _ _ kernel

/-- Reindexing by the public roles changes neither a nonlinear paired
channel nor the original joint dependence of the input kernel. -/
theorem publicIndependent_mixed_seed (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (count : ℕ) (role : Fin count → Bool)
    (kernel : (Fin count → Fin (Parameters.modulus n)) → ℝ) :
    jointChannelPolynomial (publicRoleReference C n beta role) (publicIndependentForms C n beta charts role) kernel=
    pendingPhysicalPolynomial C n beta charts
      (initialPendingInput (mixedFiniteSeed (fun word => kernel (word ∘ (rolePartition role).symm)))) := by
  rw [pendingPhysicalPolynomial_mixedFiniteSeed]
  have he := jointChannelPolynomial_equiv (rolePartition role).symm
    (publicRoleReference C n beta role) (publicIndependentForms C n beta charts role) kernel
  simp only [Equiv.symm_symm] at he
  have hr : (fun slot => publicRoleReference C n beta role (rolePartition role slot))=
      Sum.elim (fun _ : PrimaryRoles role => actualPrimaryLaw C n beta) (fun _ : BodyRoles role => actualBodyLaw C n beta) := by
    funext slot
    rcases slot with slot|slot
    · simp [publicRoleReference,rolePartition,slot.property]
    · simp [publicRoleReference,rolePartition,slot.property]
  have hf : (fun slot => publicIndependentForms C n beta charts role (rolePartition role slot))=
      Sum.elim (fun _ : PrimaryRoles role => independentPairedForm C n beta charts) (fun _ : BodyRoles role => channelForm (actualBodyChannel n)) := by
    funext slot
    rcases slot with slot|slot
    · simp [publicIndependentForms,rolePartition,slot.property]
    · simp [publicIndependentForms,rolePartition,slot.property]
  rw [hr,hf] at he
  exact he.symm

theorem publicRole_canonical_of_partition (C : ℝ) (n : ℕ) (beta : ℝ)
    (count : ℕ) (role : Fin count → Bool)
    (kernel : (Fin count → Fin (Parameters.modulus n)) → ℝ)
    (hk : Hoeffding.Canonical (Sum.elim (fun _ : PrimaryRoles role => actualPrimaryLaw C n beta)
      (fun _ : BodyRoles role => actualBodyLaw C n beta)) Finset.univ
      (fun word => kernel (word ∘ (rolePartition role).symm))) :
    Hoeffding.Canonical (publicRoleReference C n beta role) Finset.univ kernel := by
  have hh := MixedKernel.CoordinateTransport.canonical_equiv (rolePartition role)
    (Sum.elim (fun _ : PrimaryRoles role => actualPrimaryLaw C n beta) (fun _ : BodyRoles role => actualBodyLaw C n beta))
    (fun word => kernel (word ∘ (rolePartition role).symm)) hk
  have hr : (fun slot => Sum.elim (fun _ : PrimaryRoles role => actualPrimaryLaw C n beta)
      (fun _ : BodyRoles role => actualBodyLaw C n beta) ((rolePartition role).symm slot))=
      publicRoleReference C n beta role := by
    funext slot
    obtain ⟨slot,rfl⟩ := (rolePartition role).surjective slot
    rcases slot with slot|slot
    · simp [publicRoleReference,rolePartition,slot.property]
    · simp [publicRoleReference,rolePartition,slot.property]
  have he : (fun word => kernel ((word ∘ rolePartition role) ∘ (rolePartition role).symm))=kernel := by
    funext word
    congr 1
    funext slot
    simp
  rw [hr,he] at hh
  exact hh

end
end AFT.V7Calibration
