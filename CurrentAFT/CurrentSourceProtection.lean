import CurrentAFT.GaussianProductProtection
import CurrentAFT.ProtectedCycle
import CurrentAFT.InwardAnchor

/-! # The current complete Gaussian source and its one protection budget

The body block includes its public closure edge. Every leg contributes two
inputs and the shared queue contributes one input, independently of `q`.
-/
namespace CurrentAFT.CurrentSourceProtection
open AFT GaussianSource GaussianWindowProtection GaussianProductProtection
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.bodySize Parameters.legCount

def sourceCount (security : ℕ) : ℕ := Parameters.bodySize security + (Parameters.legCount security * 2 + 1)
def width (security : ℕ) : ℝ := Parameters.sourceWidth security

theorem width_pos (security : ℕ) : 0 < width security := by
  unfold width Parameters.sourceWidth
  exact_mod_cast Parameters.base_pos security

def cutoff (security : ℕ) (index : Fin (sourceCount security)) : ℕ :=
  if index.val < Parameters.bodySize security then DiffuseProfiles.edgeCutoff security
  else Parameters.sourceCutoff security - 1

def bodyPosition (security : ℕ) (index : Fin (Parameters.bodySize security)) : Fin (sourceCount security) :=
  index.castAdd (Parameters.legCount security * 2 + 1)

def auxPosition (security : ℕ) (index : Fin (Parameters.legCount security * 2 + 1)) : Fin (sourceCount security) :=
  Fin.natAdd (Parameters.bodySize security) index

theorem cutoff_body (security : ℕ) (index : Fin (Parameters.bodySize security)) :
    cutoff security (bodyPosition security index) = DiffuseProfiles.edgeCutoff security := by
  exact if_pos index.isLt

theorem cutoff_aux (security : ℕ) (index : Fin (Parameters.legCount security * 2 + 1)) :
    cutoff security (auxPosition security index) = Parameters.sourceCutoff security - 1 := by
  exact if_neg (Nat.not_lt.mpr (Nat.le_add_right _ _))

def budget (security : ℕ) : ℝ :=
  (Parameters.bodySize security : ℝ) *
      clippingProbability (width security) (DiffuseProfiles.edgeCutoff security + 1 : ℕ) (width_pos security) +
    (Parameters.legCount security * 2 + 1 : ℕ) *
      clippingProbability (width security) (Parameters.sourceCutoff security - 1 + 1 : ℕ) (width_pos security)

theorem budget_eq_sum (security : ℕ) :
    budget security = ∑ index : Fin (sourceCount security),
      clippingProbability (width security) (cutoff security index + 1 : ℕ) (width_pos security) := by
  symm
  unfold sourceCount
  rw [Fin.sum_univ_add]
  have hb (index : Fin (Parameters.bodySize security)) :
      cutoff security (index.castAdd (Parameters.legCount security * 2 + 1)) =
        DiffuseProfiles.edgeCutoff security := cutoff_body security index
  have ha (index : Fin (Parameters.legCount security * 2 + 1)) :
      cutoff security (Fin.natAdd (Parameters.bodySize security) index) =
        Parameters.sourceCutoff security - 1 := cutoff_aux security index
  simp only [hb, ha,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rfl

theorem budget_nonneg (security : ℕ) : 0 ≤ budget security := by
  rw [budget_eq_sum]
  apply Finset.sum_nonneg
  intro index _
  exact tsum_nonneg (fun point => by
    split_ifs
    · exact ENNReal.toReal_nonneg
    · rfl)

def protectedSourceLaw (security : ℕ) : FiniteDist (GaussianProductProtection.ProtectedWord (cutoff security)) :=
  GaussianProductProtection.protectedLaw (width security) (cutoff security)

/-- The unbounded joint source is literally the product integer Gaussian. -/
theorem fullMass_actual (security : ℕ) (word : Fin (sourceCount security) → ℤ) :
    GaussianProductProtection.fullMass (width security) (sourceCount security) word =
      (GaussianSource.latticeGaussian (sourceCount security) (width security) (width_pos security) word).toReal := by
  rw [latticeGaussian, independentCoordinates_apply, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro index _
  exact integerMass_actual (width security) (width_pos security) _

theorem joint_source_tv (security : ℕ) :
    (∑' word, |GaussianProductProtection.fullMass (width security) (sourceCount security) word -
      GaussianProductProtection.protectedMass (width security) (cutoff security) word|) / 2 ≤ budget security := by
  rw [budget_eq_sum]
  exact GaussianProductProtection.joint_tv (width security) (width_pos security) (cutoff security)

/-- One comparison for the whole public experiment, uniformly over every
same source-independent core and complete conditional public-map channel. -/
theorem channel_tv {Output : Type*} [Fintype Output] (security : ℕ)
    (channel : (Fin (sourceCount security) → ℤ) → FiniteDist Output) :
    FiniteDist.TVBound
      (FiniteDist.countableMix (GaussianProductProtection.fullMass (width security) (sourceCount security))
        (GaussianProductProtection.fullMass_nonneg (width security) (width_pos security) (sourceCount security))
        (GaussianProductProtection.fullMass_summable (width security) (width_pos security) (sourceCount security))
        (GaussianProductProtection.fullMass_sum (width security) (width_pos security) (sourceCount security)) channel)
      ((protectedSourceLaw security).mix (fun word => channel (GaussianProductProtection.sourceEmbedding (cutoff security) word)))
      (budget security) := by
  rw [budget_eq_sum]
  exact GaussianProductProtection.joint_channel_tv (width security) (width_pos security) (cutoff security) channel

def protectedBody (security : ℕ) (word : GaussianProductProtection.ProtectedWord (cutoff security))
    (index : Fin (Parameters.bodySize security)) : Window (DiffuseProfiles.edgeCutoff security) :=
  ⟨(word (bodyPosition security index)).val, by
    have h := (word (bodyPosition security index)).property
    simpa only [cutoff_body] using h⟩

def protectedAux (security : ℕ) (word : GaussianProductProtection.ProtectedWord (cutoff security))
    (index : Fin (Parameters.legCount security * 2 + 1)) : Window (Parameters.sourceCutoff security - 1) :=
  ⟨(word (auxPosition security index)).val, by
    have h := (word (auxPosition security index)).property
    simpa only [cutoff_aux] using h⟩

theorem sourceCutoff_pos (security : ℕ) : 0 < Parameters.sourceCutoff security :=
  pow_pos (Parameters.base_pos security) _

theorem protectedAux_bound (security : ℕ) (word : GaussianProductProtection.ProtectedWord (cutoff security))
    (index : Fin (Parameters.legCount security * 2 + 1)) :
    |(protectedAux security word index : ℤ)| < Parameters.sourceCutoff security := by
  have h := Finset.mem_Icc.mp (protectedAux security word index).property
  have hp := sourceCutoff_pos security
  exact lt_of_le_of_lt (abs_le.mpr h) (by omega)

theorem protectedCycle_bound (security : ℕ) (word : GaussianProductProtection.ProtectedWord (cutoff security))
    (permutation : Equiv.Perm (Fin (Parameters.bodySize security))) (vertex : Fin (Parameters.bodySize security)) :
    |PublicCharge.cycleDifference (fun index => (protectedBody security word (permutation.symm index) : ℤ)) vertex| <
      Parameters.sourceCutoff security := by
  have hh := ProtectedCycle.protected_integer_difference_bound (Parameters.bodySize security)
    (DiffuseProfiles.edgeCutoff security) (fun index => protectedBody security word (permutation.symm index)) vertex
  have hp := sourceCutoff_pos security
  have hcut : 2 * (DiffuseProfiles.edgeCutoff security : ℤ) < Parameters.sourceCutoff security := by
    unfold DiffuseProfiles.edgeCutoff
    omega
  exact hh.trans_lt hcut

/-- A body root and any one same-source leg/queue input fit inside the
actual safe-center margin, including arbitrary body permutations. -/
theorem protected_load_bound (security : ℕ) (word : GaussianProductProtection.ProtectedWord (cutoff security))
    (permutation : Equiv.Perm (Fin (Parameters.bodySize security))) (vertex : Fin (Parameters.bodySize security))
    (index : Fin (Parameters.legCount security * 2 + 1)) :
    |PublicCharge.cycleDifference (fun point => (protectedBody security word (permutation.symm point) : ℤ)) vertex +
      (protectedAux security word index : ℤ)| < Parameters.safeMargin security := by
  have hb := protectedCycle_bound security word permutation vertex
  have ha := protectedAux_bound security word index
  have hp := sourceCutoff_pos security
  have htriangle := abs_add_le
    (PublicCharge.cycleDifference (fun point => (protectedBody security word (permutation.symm point) : ℤ)) vertex)
    (protectedAux security word index : ℤ)
  unfold Parameters.safeMargin
  push_cast
  omega

/-- Safe centers stay canonical on the protected support; their integer
carry is exactly zero rather than merely bounded in probability. -/
theorem safe_center_carry_zero (security : ℕ) (color : Fin (Parameters.modulus security))
    (hsafe : InwardAnchor.SafeColor security color) (increment : ℤ)
    (hbound : |increment| ≤ Parameters.safeMargin security) :
    ((color.val : ℤ) + increment) / Parameters.modulus security = 0 ∧
      ((color.val : ℤ) + increment) % Parameters.modulus security = (color.val : ℤ) + increment := by
  have hinc := abs_le.mp hbound
  have hnonneg : 0 ≤ (color.val : ℤ) + increment := by unfold InwardAnchor.SafeColor at hsafe; omega
  have hlt : (color.val : ℤ) + increment < Parameters.modulus security := by unfold InwardAnchor.SafeColor at hsafe; omega
  exact ⟨Int.ediv_eq_zero_of_lt hnonneg hlt, Int.emod_eq_of_lt hnonneg hlt⟩

end
end CurrentAFT.CurrentSourceProtection
