import CurrentAFT.RootUnselectedBlockChannel
import CurrentAFT.LocalRaisingFirst

/-! # The real unselected channel in one-root, no-control grouped coordinates -/
namespace CurrentAFT.RootUnselectedGrouped
open AFT ActualBlockFock CycleRootExpansion RootTaggedFamilies RootUnselectedChannels
  RootLegCoefficientFamily RootLegCoefficientLinear GradedInverse LocalRaisingFirst
  ControlCoordinates GradedControlAlgebra BackgroundFamilies
open Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

abbrev Input (security : ℕ) := (Fin 1 → Root security) × Unit

def inputEquiv (security : ℕ) : Input security ≃ Root security where
  toFun sample := sample.1 0
  invFun root := (fun _ => root, ())
  left_inv := by
    rintro ⟨roots, control⟩
    apply Prod.ext
    · funext index
      rw [Fin.eq_zero index]
    · exact Subsingleton.elim _ _
  right_inv _ := rfl

def reference (security : ℕ) : FiniteDist (Input security) :=
  (FiniteDist.independent (fun _ : Fin 1 => rootReference security)).prod (FiniteDist.uniform Unit)

def extractLinear (security : ℕ) : (Input security → ℝ) →ₗ[ℝ] (Root security → ℝ) where
  toFun score root := score ((inputEquiv security).symm root)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem extract_energy (security : ℕ) (score : Input security → ℝ) :
    (rootReference security).l2Sq (extractLinear security score) = (reference security).l2Sq score := by
  unfold reference FiniteDist.l2Sq FiniteDist.expectation
  rw [← (inputEquiv security).symm.sum_comp]
  simp only [inputEquiv, Equiv.coe_fn_symm_mk, FiniteDist.prod_weight, FiniteDist.independent,
    Fin.prod_univ_one, FiniteDist.uniform_weight, Fintype.card_unit, Nat.cast_one, inv_one, mul_one,
    extractLinear, LinearMap.coe_mk, AddHom.coe_mk]

def channel (security order : ℕ) (horder : 1 ≤ order) (queue : ℤ) (block : BlockIndex security) :
    (Input security → ℝ) →ₗ[ℝ] ActualFamily security order :=
  (RootUnselectedBlockChannel.channel security order horder queue block).comp (extractLinear security)

theorem channel_norm_eventually (order : ℕ) (horder : 1 ≤ order) :
    ∀ᶠ security : ℕ in atTop, ∀ queue : ℤ, ∀ block : BlockIndex security, ∀ score : Input security → ℝ,
      LocalRaisingBounds.coefficientNorm security order (channel security order horder queue block score) ≤
        RootUnselectedBlockChannel.channelConstant / (Parameters.base security : ℝ) ^ 94 *
          Real.sqrt ((reference security).l2Sq score) := by
  filter_upwards [RootUnselectedBlockChannel.channel_norm_eventually order horder] with security h queue block score
  have hh := h queue block (extractLinear security score)
  rw [extract_energy] at hh
  exact hh

theorem rootFamily_degree (security order : ℕ) (horder : 1 ≤ order)
    (role : UniformBodyProfiles.BodyRole) (queue : ℤ) (input : Root security → ℝ) :
    VanishesBelow (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) order 1
      (rootFamilyLinear security order horder role queue input) := by
  intro arity hsmall
  rw [rootFamilyLinear_apply]
  unfold primaryFamily
  rw [Pi.single_eq_of_ne]
  intro hequal
  have h := congrArg (fun item : TruncatedArity order => item.val.1.val + item.val.2.val) hequal
  change arity.val.1.val + arity.val.2.val = 1 + 0 at h
  omega

theorem raw_channel_degree (security order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (block : BlockIndex security) (input : Root security → ℝ) :
    VanishesBelow (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) order 1
      (RootUnselectedBlockChannel.channel security order horder queue block input) := by
  have hsingle (role : UniformBodyProfiles.BodyRole) (shift : ℤ) :
      VanishesBelow (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) order 1
        (singletonChannel security order horder role shift input) :=
    vanishesBelow_mul _ _ order 1 0 _ _ (rootFamily_degree security order horder role shift input)
      (vanishesBelow_zero _ _ _ _)
  rcases block with leg | singleton
  · change VanishesBelow _ _ _ _ (legNumeratorLinear security order horder input * _)
    apply vanishesBelow_mul _ _ order 1 0
    · apply vanishesBelow_add
      · exact rootFamily_degree security order horder .attachment 0 input
      · rw [rootHigherLinear_apply]
        intro arity hsmall
        exact rootHigherFamily_vanishesBelow security order input arity (by omega)
    · exact vanishesBelow_zero _ _ _ _
  · rcases singleton with center | point
    · exact hsingle .free 0
    · exact hsingle .queue queue

theorem channel_degree (security order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (block : BlockIndex security) (score : Input security → ℝ) :
    VanishesBelow (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) order 1
      (channel security order horder queue block score) :=
  raw_channel_degree security order horder queue block (extractLinear security score)

theorem channel_primaryOnly (security order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (block : BlockIndex security) (score : Input security → ℝ) :
    PrimaryOnlyFamily.PrimaryOnly (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) order
      (channel security order horder queue block score) :=
  RootUnselectedBlockChannel.channel_primaryOnly security order horder queue block (extractLinear security score)

theorem channel_physical (security order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (block : BlockIndex security) (score : Input security → ℝ) :
    BackgroundEvaluation.evaluation security order (channel security order horder queue block score) *
      TruncatedOutput.quotientMap order (RootUnselectedBlockChannel.positivePolynomial security queue block) =
        TruncatedOutput.quotientMap order
          (RootUnselectedBlockChannel.numeratorPolynomial security queue (extractLinear security score) block) :=
  RootUnselectedBlockChannel.channel_physical security order horder queue block (extractLinear security score)

end
end CurrentAFT.RootUnselectedGrouped
