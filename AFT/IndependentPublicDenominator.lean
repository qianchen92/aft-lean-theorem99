import AFT.IndependentPublicSeed

/-! # The actual selected public background equals the local positive denominators -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance independentPublicDenominatorFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance independentPublicDenominatorSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
local instance independentPublicDenominatorSubtypeDecEq {α : Type*} {p : α → Prop} : DecidableEq (Subtype p) := Classical.decEq _
attribute [local instance] actualModulusNeZero

theorem actualPublicSelected_polynomial_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    (∀ mark attached first second,publicChartRaw C n mark (charts mark) attached first second=
      conditionalJointOutput C n mark attached first second) →
    ∀ (Primary Body : Type) [Fintype Primary] [Fintype Body],
    ∀ queue : Window (queueCutoff n),∀ placement : Equiv.Perm (blockIndex n),
    ∀ primary : ActualPublicPrimaryChoice n placement Primary,
    ∀ body : ActualPublicBodyChoice n placement Body,
    (∏ index : actualPublicSelected n placement primary body,
      blockPhysicalPolynomial C n (beta n) index.val (actualQueueShifts n (queue,placement) index.val))=
      (centeredGeneratingLinear (actualReferenceLaw C n (beta n)).weight
        (independentPairedPositiveMass C n (beta n) charts))^Fintype.card Primary*
      (centeredGeneratingLinear (actualReferenceLaw C n (beta n)).weight
        (independentBodyPositiveMass C n (beta n)))^Fintype.card Body := by
  filter_upwards [independentPairedPositiveMass_polynomial_eventually C hC beta hbeta,
    independentBodyPositiveMass_polynomial_eventually C hC beta hbeta] with n hp hb charts hc Primary Body _ _ queue placement primary body
  rw [← (actualPublicSourceEquiv n placement primary body).prod_comp]
  simp only [actualPublicSourceEquiv_val,actualPublicSource_queue_zero,Fintype.prod_sum_type]
  rw [← Finset.prod_mul_distrib]
  have hpair (index : Primary) :
      blockPhysicalPolynomial C n (beta n) (actualPublicSourceEmbedding n placement primary body (.inl (.inl index))) 0*
        blockPhysicalPolynomial C n (beta n) (actualPublicSourceEmbedding n placement primary body (.inl (.inr index))) 0=
      centeredGeneratingLinear (actualReferenceLaw C n (beta n)).weight
        (independentPairedPositiveMass C n (beta n) charts) := by
    obtain ⟨leg,hl⟩ := actualPublicSource_attached n placement primary body index
    obtain ⟨free,hf⟩ := actualPublicSource_compensator n placement primary body index
    rw [hl,hf]
    exact (hp charts hc leg free).symm
  have hbody (index : Body) :
      blockPhysicalPolynomial C n (beta n) (actualPublicSourceEmbedding n placement primary body (.inr index)) 0=
      centeredGeneratingLinear (actualReferenceLaw C n (beta n)).weight
        (independentBodyPositiveMass C n (beta n)) := by
    obtain ⟨free,hf⟩ := actualPublicSource_body n placement primary body index
    rw [hf]
    exact (hb free).symm
  simp only [hpair,hbody,Finset.prod_const,Finset.card_univ]

end
end AFT.V7Calibration
