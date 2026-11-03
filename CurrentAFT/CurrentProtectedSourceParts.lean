import CurrentAFT.CurrentAffineProtectedCarry
import AFT.FiniteRetype

/-! # Exact protected body, first-leg, second-leg and shared-queue product

This is a reindexing of the actual clipped latent scalars. It retains the
entire closed-cycle latent word, both inputs at every leg, and one queue.
-/
namespace CurrentAFT.CurrentProtectedSourceParts

open AFT GaussianSource CurrentSourceProtection CurrentSourceLayout
  CurrentAffineProtectedCarry GaussianProductProtection ActualCycleMeanMGF
  AffineFlagCalibration DiffuseProfiles
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

abbrev Parts (security : ℕ) := (BodyIndex security → Edge security) ×
  ((Fin (Parameters.legCount security) → Scalar security) ×
    ((Fin (Parameters.legCount security) → Scalar security) × Scalar security))

abbrev PartIndex (security : ℕ) := BodyIndex security ⊕
  ((Fin (Parameters.legCount security) ⊕ Fin (Parameters.legCount security)) ⊕ Unit)

def partsNumbering (security : ℕ) : PartIndex security ≃ Fin (sourceCount security) :=
  (Equiv.sumCongr (Equiv.refl _) (auxNumbering security)).trans finSumFinEquiv

theorem partsNumbering_body (security : ℕ) (body : BodyIndex security) :
    partsNumbering security (.inl body) = bodyPosition security body := rfl

theorem partsNumbering_aux (security : ℕ)
    (index : (Fin (Parameters.legCount security) ⊕ Fin (Parameters.legCount security)) ⊕ Unit) :
    partsNumbering security (.inr index) = auxPosition security (auxNumbering security index) := rfl

theorem auxNumbering_queue (security : ℕ) :
    auxNumbering security (.inr ()) = Fin.last (Parameters.legCount security * 2) := by
  apply Fin.ext
  simp [auxNumbering, CurrentAffineGeometry.unitToFinOne]

def partValue (security : ℕ) (parts : Parts security) : PartIndex security → ℤ
  | .inl body => (parts.1 body).val
  | .inr (.inl (.inl leg)) => (parts.2.1 leg).val
  | .inr (.inl (.inr leg)) => (parts.2.2.1 leg).val
  | .inr (.inr _) => parts.2.2.2.val

def joinParts (security : ℕ) (parts : Parts security) : ProtectedWord (cutoff security) :=
  fun index => ⟨partValue security parts ((partsNumbering security).symm index), by
    obtain ⟨body | ((first | second) | point), rfl⟩ := (partsNumbering security).surjective index
    · simp only [Equiv.symm_apply_apply, partValue]
      simpa only [partsNumbering_body, cutoff_body] using (parts.1 body).property
    · simp only [Equiv.symm_apply_apply, partValue]
      simpa only [partsNumbering_aux, cutoff_aux] using (parts.2.1 first).property
    · simp only [Equiv.symm_apply_apply, partValue]
      simpa only [partsNumbering_aux, cutoff_aux] using (parts.2.2.1 second).property
    · simp only [Equiv.symm_apply_apply, partValue]
      simpa only [partsNumbering_aux, cutoff_aux] using parts.2.2.2.property⟩

def splitParts (security : ℕ) : ProtectedWord (cutoff security) ≃ Parts security where
  toFun word := (protectedBody security word,
    (protectedFirst security word, (protectedSecond security word,
      protectedAux security word (Fin.last (Parameters.legCount security * 2)))))
  invFun := joinParts security
  left_inv word := by
    apply (sourceEmbedding (cutoff security)).injective
    funext index
    obtain ⟨body | ((first | second) | point), rfl⟩ := (partsNumbering security).surjective index
    · simp only [sourceEmbedding, Function.Embedding.coeFn_mk, joinParts,
        Equiv.symm_apply_apply, partValue]
      rw [partsNumbering_body]
      rfl
    · simp only [sourceEmbedding, Function.Embedding.coeFn_mk, joinParts,
        Equiv.symm_apply_apply, partValue]
      rw [partsNumbering_aux]
      rfl
    · simp only [sourceEmbedding, Function.Embedding.coeFn_mk, joinParts,
        Equiv.symm_apply_apply, partValue]
      rw [partsNumbering_aux]
      rfl
    · cases point
      simp only [sourceEmbedding, Function.Embedding.coeFn_mk, joinParts,
        Equiv.symm_apply_apply, partValue]
      rw [partsNumbering_aux, auxNumbering_queue]
      rfl
  right_inv parts := by
    apply Prod.ext
    · funext index
      apply Subtype.ext
      change partValue security parts ((partsNumbering security).symm (bodyPosition security index)) = _
      rw [← partsNumbering_body, Equiv.symm_apply_apply]
      rfl
    · apply Prod.ext
      · funext index
        apply Subtype.ext
        change partValue security parts ((partsNumbering security).symm
          (auxPosition security (auxNumbering security (.inl (.inl index))))) = _
        rw [← partsNumbering_aux, Equiv.symm_apply_apply]
        rfl
      · apply Prod.ext
        · funext index
          apply Subtype.ext
          change partValue security parts ((partsNumbering security).symm
            (auxPosition security (auxNumbering security (.inl (.inr index))))) = _
          rw [← partsNumbering_aux, Equiv.symm_apply_apply]
          rfl
        · apply Subtype.ext
          change partValue security parts ((partsNumbering security).symm
            (auxPosition security (Fin.last (Parameters.legCount security * 2)))) = _
          rw [← auxNumbering_queue, ← partsNumbering_aux, Equiv.symm_apply_apply]
          rfl

def legInputLaw (security : ℕ) : FiniteDist (Fin (Parameters.legCount security) → Scalar security) :=
  FiniteDist.independent (fun _ => scalarLaw security)

def partsLaw (security : ℕ) : FiniteDist (Parts security) :=
  (FiniteDist.retype (ActualFockBound.latentLaw security)).prod
    ((legInputLaw security).prod ((legInputLaw security).prod (scalarLaw security)))

theorem protected_weight_parts (security : ℕ) (word : ProtectedWord (cutoff security)) :
    (protectedSourceLaw security).weight word = (partsLaw security).weight (splitParts security word) := by
  change (GaussianProductProtection.protectedLaw (width security) (cutoff security)).weight word = _
  rw [← protectedMass_on_word (width security) (width_pos security) (cutoff security)]
  unfold protectedMass
  rw [← Equiv.prod_comp (partsNumbering security)]
  simp only [Fintype.prod_sum_type, Fintype.prod_unique]
  simp_rw [partsNumbering_body, partsNumbering_aux, cutoff_body, cutoff_aux]
  rw [auxNumbering_queue]
  change (∏ body, GaussianWindowProtection.protectedMass (width security) (edgeCutoff security)
    (protectedBody security word body).val) *
      (((∏ leg, GaussianWindowProtection.protectedMass (width security) (Parameters.sourceCutoff security - 1)
        (protectedFirst security word leg).val) *
        ∏ leg, GaussianWindowProtection.protectedMass (width security) (Parameters.sourceCutoff security - 1)
          (protectedSecond security word leg).val) *
        GaussianWindowProtection.protectedMass (width security) (Parameters.sourceCutoff security - 1)
          (protectedAux security word (Fin.last (Parameters.legCount security * 2))).val) = _
  have hedge (value : Edge security) :
      GaussianWindowProtection.protectedMass (width security) (edgeCutoff security) value.val =
        (edgeLaw security).weight value := by
    rw [GaussianWindowProtection.protectedMass_window _ _ (width_pos security), dif_pos value.property]
    rfl
  have hscalar (value : Scalar security) :
      GaussianWindowProtection.protectedMass (width security) (Parameters.sourceCutoff security - 1) value.val =
        (scalarLaw security).weight value := by
    rw [GaussianWindowProtection.protectedMass_window _ _ (width_pos security), dif_pos value.property]
    rfl
  simp_rw [hedge, hscalar]
  change _ = (∏ body, (edgeLaw security).weight (protectedBody security word body)) *
    ((∏ leg, (scalarLaw security).weight (protectedFirst security word leg)) *
      ((∏ leg, (scalarLaw security).weight (protectedSecond security word leg)) *
        (scalarLaw security).weight (protectedAux security word (Fin.last (Parameters.legCount security * 2)))))
  ring

/-- The protected-source law is exactly the four genuine independent
source products used by the completed physical block experiment. -/
theorem protected_source_parts (security : ℕ) :
    (protectedSourceLaw security).map (splitParts security) = partsLaw security := by
  apply FiniteDist.ext
  intro parts
  rw [FiniteDist.map_equiv_weight, protected_weight_parts, Equiv.apply_symm_apply]

end
end CurrentAFT.CurrentProtectedSourceParts
