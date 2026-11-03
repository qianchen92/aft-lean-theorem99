import CurrentAFT.BackgroundEndpointLaw
import CurrentAFT.ActualBlockMean
import CurrentAFT.CycleRootPolynomial

/-! Actual root-dependent background block polynomials and their exact constant coordinates. -/

namespace CurrentAFT.RootBackgroundPolynomial

open AFT AFT.RepresentedPolynomial DiffuseProfiles ProposalPrimary ActualControls
  LocalReferenceEnergy ActualBlockFock ActualBlockMean BackgroundPolynomialEvaluation
  CycleRootExpansion CycleRootPolynomial ConditionalHistogramMean ActualCycleMeanMGF
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
  CycleRootExpansion.rootLaw CycleRootExpansion.rootReference

local instance blockIndexDecidableEq (security : ℕ) : DecidableEq (BlockIndex security) := Classical.decEq _

theorem profileForm_constantCoeff {Color : Type*} [Fintype Color] (profile : Color → ℝ) :
    MvPolynomial.constantCoeff (profileForm profile) = 0 := by
  rw [profileForm_apply, map_sum]
  simp only [map_mul, MvPolynomial.constantCoeff_X, mul_zero, Finset.sum_const_zero]

theorem centeredFactor_constantCoeff {Color : Type*} [Fintype Color] (reference : Color → ℝ) (color : Color) :
    MvPolynomial.constantCoeff (centeredFactor reference color) = 1 := by
  rw [centeredFactor, map_sub, map_add, map_one, MvPolynomial.constantCoeff_X, profileForm_constantCoeff]
  ring

def blockGenerating {Slot : Type*} [Fintype Slot] (security : ℕ)
    (law : FiniteDist (Slot → ActualControls.Palette security)) : MvPolynomial (ActualControls.Palette security) ℝ :=
  finiteGenerating law (fun output => ∏ slot, centeredFactor (FringeCertificate.uniformProfile security) (output slot))

theorem blockGenerating_constantCoeff {Slot : Type*} [Fintype Slot] (security : ℕ)
    (law : FiniteDist (Slot → ActualControls.Palette security)) :
    MvPolynomial.constantCoeff (blockGenerating security law) = 1 := by
  unfold blockGenerating finiteGenerating
  simp only [map_sum, map_mul, map_prod, MvPolynomial.constantCoeff_C,
    centeredFactor_constantCoeff, Finset.prod_const_one, mul_one]
  exact law.sum_one

def localPolynomialInt (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (queue : ℤ) (vertex : Vertex security) (root : ℤ) : MvPolynomial (ActualControls.Palette security) ℝ :=
  match layout.symm vertex with
  | .inl _ => blockGenerating security (singletonLaw ((centerLaw security).map (shiftEquiv security root)))
  | .inr (.inl _) => blockGenerating security (singletonLaw ((safeLaw security).map (shiftEquiv security (root + queue))))
  | .inr (.inr _) => blockGenerating security (primaryLawAt security root)

theorem localPolynomialInt_constantCoeff (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (queue : ℤ) (vertex : Vertex security) (root : ℤ) :
    MvPolynomial.constantCoeff (localPolynomialInt security layout queue vertex root) = 1 := by
  unfold localPolynomialInt
  split <;> exact blockGenerating_constantCoeff security _

def localPolynomial (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (queue : ℤ) (vertex : Vertex security) (root : Root security) : MvPolynomial (ActualControls.Palette security) ℝ :=
  localPolynomialInt security layout queue vertex (root.val : ℤ)

theorem localPolynomial_constantCoeff (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (queue : ℤ) (vertex : Vertex security) (root : Root security) :
    MvPolynomial.constantCoeff (localPolynomial security layout queue vertex root) = 1 :=
  localPolynomialInt_constantCoeff security layout queue vertex root.val

theorem shiftEquiv_eq_of_cast (security : ℕ) (first second : ℤ)
    (hequal : (first : Root security) = (second : Root security)) :
    shiftEquiv security first = shiftEquiv security second := by
  unfold shiftEquiv
  rw [hequal]

theorem primaryLawAt_eq_of_cast (security : ℕ) (first second : ℤ)
    (hequal : (first : Root security) = (second : Root security)) :
    primaryLawAt security first = primaryLawAt security second := by
  have hatt (scalar : LocalReferenceEnergy.Scalar security) :
      attachmentAt security first scalar = attachmentAt security second scalar := by
    unfold attachmentAt
    rw [shiftEquiv_eq_of_cast security (first + scalar.val) (second + scalar.val)
      (by simp only [Int.cast_add, hequal])]
  unfold primaryLawAt
  congr 1
  funext scalar
  simp only [PositiveFirstCoefficient.positiveTripleLaw, hatt]

theorem localPolynomialInt_eq_of_cast (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (queue : ℤ) (vertex : Vertex security) (first second : ℤ)
    (hequal : (first : Root security) = (second : Root security)) :
    localPolynomialInt security layout queue vertex first = localPolynomialInt security layout queue vertex second := by
  unfold localPolynomialInt
  split
  · rw [shiftEquiv_eq_of_cast security first second hequal]
  · rw [shiftEquiv_eq_of_cast security (first + queue) (second + queue)
      (by simp only [Int.cast_add, hequal])]
  · rw [primaryLawAt_eq_of_cast security first second hequal]

theorem localPolynomial_cast (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (queue : ℤ) (vertex : Vertex security) (root : ℤ) :
    localPolynomial security layout queue vertex (root : Root security) =
      localPolynomialInt security layout queue vertex root := by
  apply localPolynomialInt_eq_of_cast
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]

theorem rooted_product (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security) :
    (∏ vertex : Vertex security, localPolynomialInt security layout queue vertex
      (rootAt security permutation latent vertex)) =
      ∏ index, blockGenerating security (rootedLaw security layout queue permutation latent index) := by
  rw [← Equiv.prod_comp layout (fun vertex => localPolynomialInt security layout queue vertex
    (rootAt security permutation latent vertex))]
  simp only [Fintype.prod_sum_type, localPolynomialInt, Equiv.symm_apply_apply,
    rootedLaw, blockLawAt, attachmentRoots, centerRoots, queueRoots]
  ac_rfl

theorem finiteGenerating_blocks {Index Color Variable : Type*} [Fintype Index] [Fintype Color]
    (Slots : Index → Type*) [∀ index, Fintype (Slots index)]
    (laws : (index : Index) → FiniteDist (Slots index → Color)) (factor : Color → MvPolynomial Variable ℝ) :
    finiteGenerating (BlockProducts.blockLaw Slots laws) (fun word => ∏ slot : Sigma Slots, factor (word slot)) =
      ∏ index, finiteGenerating (laws index) (fun word => ∏ slot, factor (word slot)) := by
  have hequiv := (Equiv.piCurry (fun index (_ : Slots index) => Color)).sum_comp
    (fun word => ∏ index, MvPolynomial.C ((laws index).weight (word index)) * ∏ slot, factor (word index slot))
  unfold finiteGenerating BlockProducts.blockLaw BlockProducts.blockMass
  simp only [map_prod, Fintype.prod_sigma]
  calc
    _ = ∑ word : Sigma Slots → Color,
        ∏ index, (MvPolynomial.C ((laws index).weight (fun slot => word ⟨index, slot⟩)) *
          ∏ slot, factor (word ⟨index, slot⟩)) := by
      simp only [Finset.prod_mul_distrib]
    _ = ∑ word : (index : Index) → Slots index → Color,
        ∏ index, (MvPolynomial.C ((laws index).weight (word index)) * ∏ slot, factor (word index slot)) := hequiv
    _ = _ := (Fintype.prod_sum (fun index (word : Slots index → Color) =>
      MvPolynomial.C ((laws index).weight word) * ∏ slot, factor (word slot))).symm

theorem rootedLaw_generating (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security) :
    finiteGenerating (BlockProducts.blockLaw (Slots security) (rootedLaw security layout queue permutation latent))
      (fun word => ∏ slot : Sigma (Slots security),
        centeredFactor (FringeCertificate.uniformProfile security) (word slot)) =
      ∏ vertex : Vertex security, localPolynomial security layout queue vertex
        ((rootAt security permutation latent vertex : ℤ) : Root security) := by
  rw [finiteGenerating_blocks]
  simp_rw [localPolynomial_cast]
  exact (rooted_product security layout queue permutation latent).symm

def rootedResidues (security : ℕ) (permutation : Equiv.Perm (BodyIndex security))
    (latent : BodyIndex security → Edge security) : Vertex security → Root security :=
  fun vertex => (rootAt security permutation latent vertex : Root security)

theorem rootLaw_latent (security : ℕ) :
    rootLaw security = (FiniteDist.uniform (Equiv.Perm (BodyIndex security))).mix (fun permutation =>
      (FiniteDist.independent (fun _ : BodyIndex security => edgeLaw security)).map (rootedResidues security permutation)) := by
  unfold rootLaw ProtectedCycle.relabeledCycleLaw ProtectedCycle.cycleLaw
  simp only [FiniteDist.map_map]
  congr 1
  funext permutation
  congr 1
  funext latent vertex
  simp only [rootedResidues, rootAt, PublicCharge.cycleDifference, Int.cast_sub]

def cycleBackgroundLaw (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ) :
    FiniteDist (Sigma (Slots security) → ActualControls.Palette security) :=
  (FiniteDist.uniform (Equiv.Perm (BodyIndex security))).mix (fun permutation =>
    (FiniteDist.independent (fun _ : BodyIndex security => edgeLaw security)).mix (fun latent =>
      BlockProducts.blockLaw (Slots security) (rootedLaw security layout queue permutation latent)))

theorem cycleBackgroundLaw_generating (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ) :
    finiteGenerating (cycleBackgroundLaw security layout queue)
      (fun word => ∏ slot : Sigma (Slots security),
        centeredFactor (FringeCertificate.uniformProfile security) (word slot)) =
      expectationLinear (rootLaw security) (fun roots =>
        ∏ vertex, localPolynomial security layout queue vertex (roots vertex)) := by
  unfold cycleBackgroundLaw
  rw [finiteGenerating_mix]
  simp_rw [finiteGenerating_mix, rootedLaw_generating]
  have hexpect (law : FiniteDist (Vertex security → Root security))
      (test : (Vertex security → Root security) → MvPolynomial (ActualControls.Palette security) ℝ) :
      expectationLinear law test = finiteGenerating law test := by
    simp only [expectationLinear, LinearMap.coe_mk, AddHom.coe_mk, finiteGenerating, MvPolynomial.smul_eq_C_mul]
  rw [hexpect, rootLaw_latent, finiteGenerating_mix]
  apply Finset.sum_congr rfl
  intro permutation _
  congr 1
  rw [BackgroundEndpointLaw.finiteGenerating_map]
  simp only [finiteGenerating, MvPolynomial.smul_eq_C_mul, Function.comp_apply, rootedResidues]

theorem actual_defect_hasOrder (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ) :
    HasOrder (fun _ : ActualControls.Palette security => 1) 2
      (polynomialDefect security (localPolynomial security layout queue)) :=
  polynomialDefect_hasOrder security _ (localPolynomial_constantCoeff security layout queue)

theorem actual_defect_truncated_sources (security order : ℕ)
    (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ) :
    truncate (fun _ : ActualControls.Palette security => 1) order
        (polynomialDefect security (localPolynomial security layout queue)) =
      ∑ selected ∈ (Finset.univ : Finset (Finset (Vertex security))).filter
          (fun selected => 2 ≤ selected.card ∧ selected.card ≤ order),
        truncate (fun _ : ActualControls.Palette security => 1) order
          (polynomialComponent security selected (localPolynomial security layout queue)) :=
  polynomialDefect_truncated_sources security order _ (localPolynomial_constantCoeff security layout queue)

end

end CurrentAFT.RootBackgroundPolynomial
