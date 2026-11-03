import AFT.IndependentPublicMixedSeed

/-! # The role-indexed realization of a literal mixed input seed -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance publicRoleSeedFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance publicRoleSeedSumDecEq {First Second : Type*} : DecidableEq (First ⊕ Second) := Classical.decEq _
local instance publicRoleSeedSubtypeDecEq {First : Type*} {predicate : First → Prop} : DecidableEq (Subtype predicate) := Classical.decEq _
attribute [local instance] actualModulusNeZero

private theorem activity_instance_eq {Slot Color : Type*} [Fintype Color]
    (first second : Fintype Slot) (firstDec secondDec : DecidableEq Slot)
    (rate : Slot → ℝ) (reference : Slot → FiniteDist Color) (kernel : (Slot → Color) → ℝ) :
    @MixedKernel.activity Slot Color first firstDec _ rate reference kernel=
      @MixedKernel.activity Slot Color second secondDec _ rate reference kernel := by
  cases Subsingleton.elim first second
  cases Subsingleton.elim firstDec secondDec
  rfl

def publicRoleKernel {Color : Type*} (seed : InputSeed Color) :
    (PrimaryRoles (inputSeedRole seed) ⊕ BodyRoles (inputSeedRole seed) → Color) → ℝ :=
  fun word => seed.kernel (word ∘ (rolePartition (inputSeedRole seed)).symm)

def publicRoleSeed {Color : Type*} [Fintype Color] (seed : InputSeed Color) : InputSeed Color :=
  mixedFiniteSeed (publicRoleKernel seed)

theorem publicRoleKernel_canonical {Color : Type*} [Fintype Color]
    (primary body : FiniteDist Color) (seed : InputSeed Color)
    (hc : Hoeffding.Canonical (inputReference primary body seed) Finset.univ seed.kernel) :
    Hoeffding.Canonical (Sum.elim (fun _ : PrimaryRoles (inputSeedRole seed) => primary)
      (fun _ : BodyRoles (inputSeedRole seed) => body)) Finset.univ (publicRoleKernel seed) := by
  have hh := MixedKernel.CoordinateTransport.canonical_equiv (rolePartition (inputSeedRole seed)).symm
    (inputReference primary body seed) seed.kernel hc
  have hr : (fun slot => inputReference primary body seed (rolePartition (inputSeedRole seed) slot))=
      Sum.elim (fun _ : PrimaryRoles (inputSeedRole seed) => primary)
        (fun _ : BodyRoles (inputSeedRole seed) => body) := by
    have href (slot) : inputReference primary body seed slot=
        if inputSeedRole seed slot then primary else body := by
      cases slot using Fin.addCases <;> simp [inputReference,inputSeedRole]
    funext slot
    rcases slot with slot|slot
    · simp [href,rolePartition,slot.property]
    · simp [href,rolePartition,slot.property]
  simpa only [Equiv.symm_symm,hr,publicRoleKernel] using hh

@[simp] theorem publicRoleSeed_primaryOrder {Color : Type*} [Fintype Color] (seed : InputSeed Color) :
    (publicRoleSeed seed).primaryOrder=seed.primaryOrder := inputSeedRole_primary_card seed

@[simp] theorem publicRoleSeed_bodyOrder {Color : Type*} [Fintype Color] (seed : InputSeed Color) :
    (publicRoleSeed seed).bodyOrder=seed.bodyOrder := inputSeedRole_body_card seed

theorem publicRoleSeed_weight {Color : Type*} [Fintype Color]
    (primary body : FiniteDist Color) (primaryPool bodyPool radius : ℝ) (seed : InputSeed Color) :
    inputWeight primary body primaryPool bodyPool radius (publicRoleSeed seed)=
      inputWeight primary body primaryPool bodyPool radius seed := by
  rw [publicRoleSeed,mixedFiniteSeed_weight,inputSeedRole_body_card]
  unfold inputWeight MixedKernel.analyticActivity
  congr 1
  have hh := MixedKernel.CoordinateTransport.activity_equiv (rolePartition (inputSeedRole seed)).symm
    (inputRate primaryPool bodyPool seed) (inputReference primary body seed) seed.kernel
  have hr : (fun slot => inputReference primary body seed (rolePartition (inputSeedRole seed) slot))=
      Sum.elim (fun _ : PrimaryRoles (inputSeedRole seed) => primary)
        (fun _ : BodyRoles (inputSeedRole seed) => body) := by
    have href (slot) : inputReference primary body seed slot=
        if inputSeedRole seed slot then primary else body := by
      cases slot using Fin.addCases <;> simp [inputReference,inputSeedRole]
    funext slot
    rcases slot with slot|slot
    · simp [href,rolePartition,slot.property]
    · simp [href,rolePartition,slot.property]
  have ht : (fun slot => inputRate primaryPool bodyPool seed (rolePartition (inputSeedRole seed) slot))=
      Sum.elim (fun _ : PrimaryRoles (inputSeedRole seed) => (Real.sqrt primaryPool)⁻¹)
        (fun _ : BodyRoles (inputSeedRole seed) => (Real.sqrt bodyPool)⁻¹) := by
    have hrate (slot) : inputRate primaryPool bodyPool seed slot=
        if inputSeedRole seed slot then (Real.sqrt primaryPool)⁻¹ else (Real.sqrt bodyPool)⁻¹ := by
      cases slot using Fin.addCases <;> simp [inputRate,inputSeedRole]
    funext slot
    rcases slot with slot|slot
    · simp [hrate,rolePartition,slot.property]
    · simp [hrate,rolePartition,slot.property]
  simp only [Equiv.symm_symm,hr,ht] at hh
  change MixedKernel.activity _ _ (publicRoleKernel seed)=_ at hh
  exact (activity_instance_eq _ _ _ _ _ _ _).trans
    (hh.trans (activity_instance_eq _ _ _ _ _ _ _))

theorem publicRoleSeed_pendingPolynomial (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (seed : InputSeed (Fin (Parameters.modulus n))) :
    pendingPhysicalPolynomial C n beta charts (initialPendingInput (publicRoleSeed seed))=
      pendingPhysicalPolynomial C n beta charts (initialPendingInput seed) := by
  change pendingPhysicalPolynomial C n beta charts (initialPendingInput (mixedFiniteSeed
    (fun word => seed.kernel (word ∘ (rolePartition (inputSeedRole seed)).symm))))=_
  rw [← publicIndependent_mixed_seed,
    inputSeedRole_reference,inputSeedRole_forms]
  rfl

theorem publicRoleSeed_quotient_image_eventually (C : ℝ) (hC : 1≤C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n)≤beta n ∧
      beta n≤2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n →
    ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    (∀ mark attached first second,publicChartRaw C n mark (charts mark) attached first second=
      conditionalJointOutput C n mark attached first second) →
    ∀ seed : InputSeed (Fin (Parameters.modulus n)),
    Hoeffding.Canonical (inputReference (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) seed) Finset.univ seed.kernel →
    ∀ cutoff,
    actualLeadingOutput C n (beta n) (independentGlobalQuotient C n (beta n) operator charts (publicRoleSeed seed) cutoff)=
      actualLeadingOutput C n (beta n) (independentGlobalQuotient C n (beta n) operator charts seed cutoff) := by
  filter_upwards [independentGlobalQuotient_image_eventually C hC beta hbeta]
    with n h operator hop charts hcharts seed hs cutoff
  have hc := mixedFiniteSeed_canonical (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
    (publicRoleKernel seed) (publicRoleKernel_canonical _ _ seed hs)
  rw [h operator hop charts hcharts (publicRoleSeed seed) hc cutoff,h operator hop charts hcharts seed hs cutoff,
    publicRoleSeed_pendingPolynomial,publicRoleSeed_primaryOrder,publicRoleSeed_bodyOrder]

end
end AFT.V7Calibration
