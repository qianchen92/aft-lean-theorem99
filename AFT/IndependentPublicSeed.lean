import AFT.IndependentPublicForms
import AFT.IndependentPublicResponse
import AFT.IndependentGlobalImage

/-! # Actual public placement semantics of every joint mixed input seed -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance independentPublicSeedFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance independentPublicSeedSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
local instance independentPublicSeedSubtypeDecEq {α : Type*} {p : α → Prop} : DecidableEq (Subtype p) := Classical.decEq _
attribute [local instance] actualModulusNeZero

def inputSeedRole {Color : Type*} (seed : InputSeed Color) : Fin (seed.primaryOrder+seed.bodyOrder) → Bool :=
  Fin.addCases (fun _ => true) (fun _ => false)

theorem inputSeedRole_primary_card {Color : Type*} (seed : InputSeed Color) :
    Fintype.card (PrimaryRoles (inputSeedRole seed))=seed.primaryOrder := by
  let equiv : Fin seed.primaryOrder ≃ PrimaryRoles (inputSeedRole seed) := Equiv.ofBijective
    (fun index => ⟨Fin.castAdd seed.bodyOrder index,by simp [inputSeedRole]⟩) (by
      constructor
      · intro first second he
        apply Fin.ext
        exact congrArg (fun x => x.val.val) he
      · intro index
        rcases index with ⟨index,hi⟩
        revert hi
        refine Fin.addCases ?_ ?_ index
        · intro first _
          exact ⟨first,rfl⟩
        · intro second hh
          simp [inputSeedRole] at hh)
  simpa only [Fintype.card_fin] using (Fintype.card_congr equiv).symm

theorem inputSeedRole_body_card {Color : Type*} (seed : InputSeed Color) :
    Fintype.card (BodyRoles (inputSeedRole seed))=seed.bodyOrder := by
  let equiv : Fin seed.bodyOrder ≃ BodyRoles (inputSeedRole seed) := Equiv.ofBijective
    (fun index => ⟨Fin.natAdd seed.primaryOrder index,by simp [inputSeedRole]⟩) (by
      constructor
      · intro first second he
        apply Fin.ext
        have hh := congrArg (fun x => x.val.val) he
        change seed.primaryOrder+first.val=seed.primaryOrder+second.val at hh
        omega
      · intro index
        rcases index with ⟨index,hi⟩
        revert hi
        refine Fin.addCases ?_ ?_ index
        · intro first hh
          simp [inputSeedRole] at hh
        · intro second _
          exact ⟨second,rfl⟩)
  simpa only [Fintype.card_fin] using (Fintype.card_congr equiv).symm

theorem inputSeedRole_reference (C : ℝ) (n : ℕ) (beta : ℝ) (seed : InputSeed (Fin (Parameters.modulus n))) :
    publicRoleReference C n beta (inputSeedRole seed)=inputReference (actualPrimaryLaw C n beta) (actualBodyLaw C n beta) seed := by
  funext slot
  refine Fin.addCases ?_ ?_ slot <;> intro index <;> simp [publicRoleReference,inputSeedRole,inputReference]

theorem inputSeedRole_forms (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (seed : InputSeed (Fin (Parameters.modulus n))) :
    publicIndependentForms C n beta charts (inputSeedRole seed)=
      pendingPhysicalForms C n beta charts (initialPendingInput seed) := by
  funext slot
  refine Fin.addCases ?_ ?_ slot <;> intro index <;>
    simp [publicIndependentForms,inputSeedRole,pendingPhysicalForms,initialPendingInput]

theorem independentPublic_seed_polynomial_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    ∀ seed : InputSeed (Fin (Parameters.modulus n)),
    Hoeffding.Canonical (inputReference (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) seed)
      Finset.univ seed.kernel →
    (∑ input,MvPolynomial.C (seed.kernel input)*publicInputIndependentPolynomial C n (beta n) charts (inputSeedRole seed) input)=
      pendingPhysicalPolynomial C n (beta n) charts (initialPendingInput seed) := by
  filter_upwards [publicIndependent_joint_canonical_eventually C hC beta hbeta] with n hi charts seed hs
  have hc : Hoeffding.Canonical (publicRoleReference C n (beta n) (inputSeedRole seed)) Finset.univ seed.kernel := by
    rw [inputSeedRole_reference]; exact hs
  rw [hi charts (seed.primaryOrder+seed.bodyOrder) (inputSeedRole seed) seed.kernel hc,
    inputSeedRole_reference,inputSeedRole_forms]
  rfl

/-- Every real public source-disjoint placement realizes the same literal
joint numerator. The untouched positive blocks remain explicit. -/
theorem independentPublic_numerator_image_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n →
    ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    (∀ mark attached first second,publicChartRaw C n mark (charts mark) attached first second=
      conditionalJointOutput C n mark attached first second) →
    ∀ seed : InputSeed (Fin (Parameters.modulus n)),
    Hoeffding.Canonical (inputReference (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) seed)
      Finset.univ seed.kernel →
    ∀ queue : Window (queueCutoff n),∀ placement : Equiv.Perm (blockIndex n),
    ∀ primary : ActualPublicPrimaryChoice n placement (PrimaryRoles (inputSeedRole seed)),
    ∀ body : ActualPublicBodyChoice n placement (BodyRoles (inputSeedRole seed)),
    independentRootResponseLinear n (fun roots =>
      actualConditionalControlPolynomialLinear C n (beta n) charts (seed.primaryOrder+seed.bodyOrder) (inputSeedRole seed)
        (actualPublicSelected n placement primary body) (actualPublicTaggedPlacement n placement (inputSeedRole seed) primary body)
        roots (queue,placement) seed.kernel)=
      actualLeadingOutput C n (beta n) (independentNumeratorTable C n (beta n) operator charts seed)*
        ∏ index : {index : blockIndex n // index ∉ actualPublicSelected n placement primary body},
          blockPhysicalPolynomial C n (beta n) index (actualQueueShifts n (queue,placement) index) := by
  filter_upwards [actual_independent_public_response_eventually C hC beta hbeta,
    independentPublic_seed_polynomial_eventually C hC beta hbeta,
    independentNumeratorTable_image_eventually C hC beta hbeta]
    with n hp hs hi operator hop charts hc seed hseed queue placement primary body
  rw [hp charts (seed.primaryOrder+seed.bodyOrder) (inputSeedRole seed) queue placement primary body seed.kernel,
    hs charts seed hseed,hi operator hop charts hc seed hseed]

end
end AFT.V7Calibration
