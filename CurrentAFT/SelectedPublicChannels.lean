import CurrentAFT.TensorPublicProjection

/-! # The actual selected controls controls before the signed physical response -/
namespace CurrentAFT.SelectedPublicChannels
open AFT DiffuseProfiles ProposalPrimary PositivePublicChannels JointTaggedPhysicalFock
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance finDecEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance groupDecEq (security : ℕ) : DecidableEq (Group security) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.dimension Parameters.legCount
  primaryLaw centerLaw

def primaryScore (security : ℕ) : (Group security → ℝ) →ₗ[ℝ] (Group security → ℝ) where
  toFun score controls := PhysicalSynthesis.pairedChannel security
    (reducePrimary (ActualControls.bodyReference security) score) (SafeControlGroups.unwrap security controls)
  map_add' first second := by funext controls; simp only [map_add, Pi.add_apply]
  map_smul' scalar score := by funext controls; simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

def ordinaryScore (security : ℕ) : (Group security → ℝ) →ₗ[ℝ] (Group security → ℝ) where
  toFun score controls := reduceBody (primaryLaw security) score controls.2
  map_add' first second := by funext controls; simp only [map_add, Pi.add_apply]
  map_smul' scalar score := by funext controls; simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

def roleScore (security r s : ℕ) : (Fin r ⊕ Fin s) →
    (Group security → ℝ) →ₗ[ℝ] (Group security → ℝ)
  | .inl _ => primaryScore security
  | .inr _ => ordinaryScore security

def roleLaw (security r s : ℕ) (compensatorRoot attachmentRoot : Fin r → ℤ) (bodyRoot : Fin s → ℤ) :
    (index : Fin r ⊕ Fin s) → Group security → FiniteDist (roleSlots r s index → FirstHistogram.Palette security)
  | .inl index, controls => quadGiven security (compensatorRoot index) (attachmentRoot index)
      (SafeControlGroups.unwrap security controls)
  | .inr index, controls => bodyGiven security (bodyRoot index) controls.2

theorem role_channel_public_sum (security r s : ℕ)
    (compensatorRoot attachmentRoot : Fin r → ℤ) (bodyRoot : Fin s → ℤ)
    (index : Fin r ⊕ Fin s) (score : Group security → ℝ)
    (word : roleSlots r s index → FirstHistogram.Palette security) :
    roleChannel security r s compensatorRoot attachmentRoot bodyRoot index score word =
      (SafeControlGroups.reference security).expectation (fun controls => roleScore security r s index score controls *
        (roleLaw security r s compensatorRoot attachmentRoot bodyRoot index controls).weight word) := by
  cases index with
  | inl index =>
    change TaggedPhysicalFock.averagedPairedChannel security (compensatorRoot index) (attachmentRoot index)
      (reducePrimary (ActualControls.bodyReference security) score) word = _
    rw [paired_channel_public_sum]
    exact (SafeControlGroups.reference_expectation security _).symm
  | inr index =>
    change OrdinaryPhysicalFock.bodyChannel security (bodyRoot index) (reduceBody (primaryLaw security) score) word = _
    rw [body_channel_public_sum]
    exact (SafeControlGroups.reference_body_expectation security _).symm

def scoreChannel (security r s : ℕ) (index : Fin (r + s)) :
    (Group security → ℝ) →ₗ[ℝ] (Group security → ℝ) :=
  roleScore security r s (finSumFinEquiv.symm index)

def publicLaw (security r s : ℕ) (compensatorRoot attachmentRoot : Fin r → ℤ) (bodyRoot : Fin s → ℤ)
    (index : Fin (r + s)) (controls : Group security) :
    FiniteDist (physicalSlots r s index → FirstHistogram.Palette security) :=
  roleLaw security r s compensatorRoot attachmentRoot bodyRoot (finSumFinEquiv.symm index) controls

def selectedScore (security r s : ℕ)
    (kernel : ControlCoordinates.DensityKernel (Primary := FirstHistogram.Palette security)
      (Body := ActualControls.SafePalette security) r s) (controls : Fin (r + s) → Group security) : ℝ :=
  ∑ input, finiteKernel kernel input * ∏ index,
    scoreChannel security r s index (Pi.single (input index) 1) (controls index)

/-- The common safe alphabet contributes only independent unused coordinates.
After integrating them the score is precisely the original paired kernel,
with no second application of paired synthesis. -/
theorem selectedScore_eq_pairedKernel (security r s : ℕ)
    (kernel : ControlCoordinates.DensityKernel (Primary := FirstHistogram.Palette security)
      (Body := ActualControls.SafePalette security) r s) (controls : Fin (r + s) → Group security) :
    selectedScore security r s kernel controls = PhysicalSynthesis.pairedKernel security r s kernel
      (fun index => SafeControlGroups.unwrap security (controls (finSumFinEquiv (.inl index))))
      (fun index => (controls (finSumFinEquiv (.inr index))).2) := by
  have hreindex := TensorPublicProjection.sum_reindex
    (finSumFinEquiv : Fin r ⊕ Fin s ≃ Fin (r + s)) (unpairedKernel kernel)
    (fun index point => roleScore security r s index (Pi.single point 1) (controls (finSumFinEquiv index)))
  have hfirst : selectedScore security r s kernel controls =
      ∑ input : (Fin r ⊕ Fin s) → Group security, unpairedKernel kernel input *
        ∏ index, roleScore security r s index (Pi.single (input index) 1) (controls (finSumFinEquiv index)) := by
    simpa only [selectedScore, finiteKernel, scoreChannel, Equiv.apply_symm_apply] using hreindex
  rw [hfirst]
  apply Eq.trans ?_ (TensorPublicProjection.paired_projection (primaryLaw security)
    (ActualControls.bodyReference security) r s (PhysicalSynthesis.pairedChannel security) kernel
    (fun index => SafeControlGroups.unwrap security (controls (finSumFinEquiv (.inl index))))
    (fun index => (controls (finSumFinEquiv (.inr index))).2))
  apply Finset.sum_congr rfl
  intro input _
  rw [Fintype.prod_sum_type]
  simp only [unpairedKernel, roleScore, primaryScore, ordinaryScore, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [TensorPublicProjection.single_one_canonical]
  exact (mul_assoc (G := ℝ) _ _ _).symm

/-- All selected positive kernels are integrated against the one actual
reference product law. The coefficient kernel remains arbitrary and joint. -/
theorem jointMass_public_sum (security r s : ℕ)
    (compensatorRoot attachmentRoot : Fin r → ℤ) (bodyRoot : Fin s → ℤ)
    (kernel : ControlCoordinates.DensityKernel (Primary := FirstHistogram.Palette security)
      (Body := ActualControls.SafePalette security) r s)
    (word : Sigma (physicalSlots r s) → FirstHistogram.Palette security) :
    jointMass security r s compensatorRoot attachmentRoot bodyRoot kernel word =
      (FiniteDist.independent (fun _ : Fin (r + s) => SafeControlGroups.reference security)).expectation
        (fun controls => selectedScore security r s kernel controls * ∏ index,
          (publicLaw security r s compensatorRoot attachmentRoot bodyRoot index (controls index)).weight
            (fun slot => word ⟨index, slot⟩)) := by
  unfold jointMass JointPhysicalChannel.mass
  change (∑ input, finiteKernel kernel input * ∏ index,
    roleChannel security r s compensatorRoot attachmentRoot bodyRoot (finSumFinEquiv.symm index)
      (Pi.single (input index) 1) (fun slot => word ⟨index, slot⟩)) = _
  simp_rw [role_channel_public_sum]
  exact weighted_tensor_sum (fun _ => SafeControlGroups.reference security)
    (scoreChannel security r s)
    (fun index controls => (publicLaw security r s compensatorRoot attachmentRoot bodyRoot index controls).weight
      (fun slot => word ⟨index, slot⟩)) (finiteKernel kernel)

end
end CurrentAFT.SelectedPublicChannels
