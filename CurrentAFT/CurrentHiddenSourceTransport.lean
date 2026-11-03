import CurrentAFT.CurrentSourceLayout

/-! # Gaussian replacement with the finite public closure retained

Only the dimension-many hidden Gaussian coordinates are unbounded here.
The public closing edge is already drawn from its finite clipped law.
The protected product is exactly the complete-source protected law under
the proved source numbering.
-/
namespace CurrentAFT.CurrentHiddenSourceTransport

open AFT GaussianSource CurrentSourceProtection CurrentSourceLayout GaussianProductProtection
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.bodySize Parameters.dimension Parameters.legCount
  sourceCount cutoff sourceNumbering

abbrev HiddenWord (security : ℕ) := ProtectedWord (hiddenCutoff security)
abbrev Closure (security : ℕ) := Window (DiffuseProfiles.edgeCutoff security)

def hiddenLaw (security : ℕ) : FiniteDist (HiddenWord security) :=
  GaussianProductProtection.protectedLaw (width security) (hiddenCutoff security)

def closureLaw (security : ℕ) : FiniteDist (Closure security) :=
  windowGaussian (width security) (DiffuseProfiles.edgeCutoff security)

def joinProtected (security : ℕ) (pair : HiddenWord security × Closure security) :
    ProtectedWord (cutoff security) := fun index =>
  ⟨(splitWord security).symm
    (sourceEmbedding (hiddenCutoff security) pair.1, pair.2.val) index, by
    obtain ⟨hidden | point, rfl⟩ := (sourceNumbering security).surjective index
    · simpa only [splitWord, Equiv.coe_fn_symm_mk, Equiv.symm_apply_apply, Sum.elim_inl]
        using (pair.1 hidden).property
    · cases point
      simpa only [splitWord, Equiv.coe_fn_symm_mk, Equiv.symm_apply_apply, Sum.elim_inr, cutoff_closure]
        using pair.2.property⟩

def splitProtected (security : ℕ) : ProtectedWord (cutoff security) ≃
    HiddenWord security × Closure security where
  toFun word := (hiddenProtectedWord security word, protectedClosure security word)
  invFun := joinProtected security
  left_inv word := by
    apply (sourceEmbedding (cutoff security)).injective
    exact (splitWord security).symm_apply_apply (sourceEmbedding (cutoff security) word)
  right_inv pair := by
    apply Prod.ext
    · apply (sourceEmbedding (hiddenCutoff security)).injective
      funext index
      change (splitWord security).symm
        (sourceEmbedding (hiddenCutoff security) pair.1, pair.2.val)
          (sourceNumbering security (.inl index)) = _
      simp only [splitWord, Equiv.coe_fn_symm_mk, Equiv.symm_apply_apply, Sum.elim_inl]
    · apply Subtype.ext
      change (splitWord security).symm
        (sourceEmbedding (hiddenCutoff security) pair.1, pair.2.val)
          (sourceNumbering security (.inr ())) = _
      simp only [splitWord, Equiv.coe_fn_symm_mk, Equiv.symm_apply_apply, Sum.elim_inr]

theorem protected_law_split (security : ℕ) :
    (protectedSourceLaw security).map (splitProtected security) =
      (hiddenLaw security).prod (closureLaw security) := by
  apply FiniteDist.ext
  intro pair
  rw [FiniteDist.map_equiv_weight, protectedLaw_weight_split]
  have hpair := (splitProtected security).apply_symm_apply pair
  have hh := congrArg Prod.fst hpair
  have hc := congrArg Prod.snd hpair
  change hiddenProtectedWord security ((splitProtected security).symm pair) = pair.1 at hh
  change protectedClosure security ((splitProtected security).symm pair) = pair.2 at hc
  rw [hh, hc]
  rfl

theorem protected_law_join (security : ℕ) :
    ((hiddenLaw security).prod (closureLaw security)).map (joinProtected security) =
      protectedSourceLaw security := by
  rw [← protected_law_split, FiniteDist.map_map]
  change (protectedSourceLaw security).map
    (fun word => (splitProtected security).symm (splitProtected security word)) = _
  simp only [Equiv.symm_apply_apply]
  apply FiniteDist.ext
  intro word
  rw [FiniteDist.map_weight, Finset.sum_eq_single word]
  · rw [if_pos rfl]
  · intro other _ hother
    exact if_neg hother
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

def hiddenBudget (security : ℕ) : ℝ :=
  ∑ index : Fin (Parameters.dimension security),
    clippingProbability (width security) (hiddenCutoff security index + 1 : ℕ) (width_pos security)

theorem budget_split (security : ℕ) :
    budget security = hiddenBudget security +
      clippingProbability (width security) (DiffuseProfiles.edgeCutoff security + 1 : ℕ) (width_pos security) := by
  rw [budget_eq_sum, ← Equiv.sum_comp (sourceNumbering security)]
  simp only [Fintype.sum_sum_type, Fintype.sum_unique]
  change _ + clippingProbability _ (cutoff security (sourceNumbering security (.inr ())) + 1 : ℕ) _ = _
  rw [cutoff_closure]
  unfold hiddenBudget hiddenCutoff
  rfl

theorem hiddenBudget_le (security : ℕ) : hiddenBudget security ≤ budget security := by
  rw [budget_split]
  have hnonneg : 0 ≤ clippingProbability (width security)
      (DiffuseProfiles.edgeCutoff security + 1 : ℕ) (width_pos security) :=
    tsum_nonneg (fun point => by split_ifs; exact ENNReal.toReal_nonneg; rfl)
  linarith

def hiddenGaussianOutput {Output : Type*} [Fintype Output] (security : ℕ)
    (channel : (Fin (Parameters.dimension security) → ℤ) → FiniteDist Output) : FiniteDist Output :=
  FiniteDist.countableMix (fullMass (width security) (Parameters.dimension security))
    (fullMass_nonneg (width security) (width_pos security) (Parameters.dimension security))
    (fullMass_summable (width security) (width_pos security) (Parameters.dimension security))
    (fullMass_sum (width security) (width_pos security) (Parameters.dimension security)) channel

/-- The closure and all core/chart randomness are public, finite and
independent of the dimension-many unbounded hidden inputs. The complete
source error is paid once, with no queue multiplicity factor. -/
theorem public_hidden_channel_tv {Public Output : Type*} [Fintype Public] [Fintype Output]
    (security : ℕ) (publicLaw : FiniteDist Public)
    (physical : Public → Closure security → (Fin (Parameters.dimension security) → ℤ) → FiniteDist Output) :
    FiniteDist.TVBound
      ((publicLaw.prod (closureLaw security)).mix (fun draw =>
        hiddenGaussianOutput security (physical draw.1 draw.2)))
      ((publicLaw.prod (closureLaw security)).mix (fun draw => (hiddenLaw security).mix
        (fun word => physical draw.1 draw.2 (sourceEmbedding (hiddenCutoff security) word))))
      (budget security) := by
  apply FiniteDist.TVBound.mix_right
  intro draw
  exact (GaussianProductProtection.joint_channel_tv (width security) (width_pos security)
    (hiddenCutoff security) (physical draw.1 draw.2)).mono (hiddenBudget_le security)

end
end CurrentAFT.CurrentHiddenSourceTransport
