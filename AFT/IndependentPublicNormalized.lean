import AFT.IndependentPublicDenominator
import AFT.IndependentUpperImage

/-! # Actual public response equals the joint literal quotient times its background -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance independentPublicNormalizedFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance independentPublicNormalizedSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
local instance independentPublicNormalizedSubtypeDecEq {α : Type*} {p : α → Prop} : DecidableEq (Subtype p) := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- At each actual public record, all selected coordinates are queue-free.
Thus the same literal joint quotient multiplies the true whole background,
before any averaging over the common queue or the public placement. -/
theorem independentPublic_quotient_response_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
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
    ∀ cutoff : ℕ,∀ queue : Window (queueCutoff n),∀ placement : Equiv.Perm (blockIndex n),
    ∀ primary : ActualPublicPrimaryChoice n placement (PrimaryRoles (inputSeedRole seed)),
    ∀ body : ActualPublicBodyChoice n placement (BodyRoles (inputSeedRole seed)),
    truncate (fun _ => 1) cutoff (independentRootResponseLinear n (fun roots =>
      actualConditionalControlPolynomialLinear C n (beta n) charts (seed.primaryOrder+seed.bodyOrder) (inputSeedRole seed)
        (actualPublicSelected n placement primary body) (actualPublicTaggedPlacement n placement (inputSeedRole seed) primary body)
        roots (queue,placement) seed.kernel))=
    truncate (fun _ => 1) cutoff
      (actualLeadingOutput C n (beta n) (independentGlobalQuotient C n (beta n) operator charts seed cutoff)*
        ∏ index,blockPhysicalPolynomial C n (beta n) index (actualQueueShifts n (queue,placement) index)) := by
  filter_upwards [independentPublic_numerator_image_eventually C hC beta hbeta,
    independentNumeratorTable_image_eventually C hC beta hbeta,
    independentGlobalQuotient_image_eventually C hC beta hbeta,
    actualPublicSelected_polynomial_eventually C hC beta hbeta,
    independentPairedPositiveMass_probability_eventually C hC beta hbeta]
    with n hpublic hnumerator hquotient hselected hmass operator hop charts hc seed hs cutoff queue placement primary body
  rw [hpublic operator hop charts hc seed hs queue placement primary body,
    hnumerator operator hop charts hc seed hs,hquotient operator hop charts hc seed hs cutoff]
  let paired := centeredGeneratingLinear (actualReferenceLaw C n (beta n)).weight (independentPairedPositiveMass C n (beta n) charts)
  let single := centeredGeneratingLinear (actualReferenceLaw C n (beta n)).weight (independentBodyPositiveMass C n (beta n))
  let complement := ∏ index : {index : blockIndex n // index ∉ actualPublicSelected n placement primary body},
    blockPhysicalPolynomial C n (beta n) index (actualQueueShifts n (queue,placement) index)
  have hsel := hselected charts hc (PrimaryRoles (inputSeedRole seed)) (BodyRoles (inputSeedRole seed))
    queue placement primary body
  rw [inputSeedRole_primary_card,inputSeedRole_body_card] at hsel
  have hall : (∏ index,blockPhysicalPolynomial C n (beta n) index (actualQueueShifts n (queue,placement) index))=
      paired^seed.primaryOrder*single^seed.bodyOrder*complement := by
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun index => index ∈ actualPublicSelected n placement primary body)
      (fun index => blockPhysicalPolynomial C n (beta n) index (actualQueueShifts n (queue,placement) index))]
    apply congrArg₂ (· * ·)
    · convert hsel using 1
      apply Finset.prod_congr (by ext index; simp)
      intro index _
      rfl
    · rfl
  rw [hall]
  apply (quotient_eq_iff_truncate (fun _ : Fin (Parameters.modulus n) => 1) cutoff _ _).mp
  let quotient := quotientMap (fun _ : Fin (Parameters.modulus n) => 1) cutoff
  have hpair : quotient paired*quotient (finiteCorrection (paired-1) cutoff)=1 :=
    quotient_reciprocal paired cutoff (by dsimp only [paired]; rw [centeredGeneratingLinear_constant]; exact (hmass charts).2)
  have hsingle : quotient single*quotient (finiteCorrection (single-1) cutoff)=1 :=
    quotient_reciprocal single cutoff (by dsimp only [single]; rw [centeredGeneratingLinear_constant,independentBodyPositiveMass_mass])
  change quotient (_*complement)=quotient (_*(paired^seed.primaryOrder*single^seed.bodyOrder*complement))
  simp only [map_mul,map_pow]
  calc
    _ = quotient (pendingPhysicalPolynomial C n (beta n) charts (initialPendingInput seed))*quotient complement*
        (quotient paired*quotient (finiteCorrection (paired-1) cutoff))^seed.primaryOrder*
        (quotient single*quotient (finiteCorrection (single-1) cutoff))^seed.bodyOrder := by rw [hpair,hsingle]; simp
    _ = _ := by ring

/-- The finite literal operator is identified with the actual independent
response for a whole mixed monomial, including every old correlation. -/
theorem independentPublic_upper_response_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n →
    ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    (∀ mark attached first second,publicChartRaw C n mark (charts mark) attached first second=
      conditionalJointOutput C n mark attached first second) →
    ∀ cutoff : ℕ,∀ powers : InputSeed (Fin (Parameters.modulus n)) →₀ ℕ,
    weightedOrder (fun seed => seed.primaryOrder+seed.bodyOrder) powers ≤ cutoff →
    (∀ seed ∈ powers.support,Hoeffding.Canonical
      (inputReference (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) seed) Finset.univ seed.kernel) →
    ∀ queue : Window (queueCutoff n),∀ placement : Equiv.Perm (blockIndex n),
    ∀ primary : ActualPublicPrimaryChoice n placement (PrimaryRoles (inputSeedRole (mixedMonomialSeed powers))),
    ∀ body : ActualPublicBodyChoice n placement (BodyRoles (inputSeedRole (mixedMonomialSeed powers))),
    truncate (fun _ => 1) cutoff (independentRootResponseLinear n (fun roots =>
      actualConditionalControlPolynomialLinear C n (beta n) charts
        ((mixedMonomialSeed powers).primaryOrder+(mixedMonomialSeed powers).bodyOrder) (inputSeedRole (mixedMonomialSeed powers))
        (actualPublicSelected n placement primary body)
        (actualPublicTaggedPlacement n placement (inputSeedRole (mixedMonomialSeed powers)) primary body)
        roots (queue,placement) (mixedMonomialSeed powers).kernel))=
    truncate (fun _ => 1) cutoff
      (actualLeadingOutput C n (beta n)
        ((1+independentUpperLinear C n (beta n) operator charts cutoff cutoff) (MvPolynomial.monomial powers 1))*
        ∏ index,blockPhysicalPolynomial C n (beta n) index (actualQueueShifts n (queue,placement) index)) := by
  filter_upwards [independentPublic_quotient_response_eventually C hC beta hbeta]
    with n hi operator hop charts hc cutoff powers ho hs queue placement primary body
  rw [hi operator hop charts hc (mixedMonomialSeed powers) (mixedMonomialSeed_canonical _ _ powers hs)
    cutoff queue placement primary body]
  have he := independentUpperLinear_monomial_image C n (beta n) operator charts cutoff cutoff powers ho hs
  let background := ∏ index,blockPhysicalPolynomial C n (beta n) index (actualQueueShifts n (queue,placement) index)
  have hh := congrArg (fun value => value*quotientMap (fun _ : Fin (Parameters.modulus n) => 1) cutoff background)
    ((quotient_eq_iff_truncate (fun _ : Fin (Parameters.modulus n) => 1) cutoff _ _).mpr he)
  simp only [← map_mul] at hh
  exact ((quotient_eq_iff_truncate (fun _ : Fin (Parameters.modulus n) => 1) cutoff _ _).mp hh).symm

end
end AFT.V7Calibration

