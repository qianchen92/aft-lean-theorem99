import AFT.PublicRoleSeed
import AFT.PairedKernelReindex
import AFT.TwoPoolReindex
import AFT.PairedTableLinear

/-! # The same paired statistic in actual public-role coordinates -/
namespace AFT.V7Calibration
open RepresentedPolynomial CanonicalMoments
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
local instance roleStatFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance roleStatSumDecEq {First Second : Type*} : DecidableEq (First ⊕ Second) := Classical.decEq _
local instance roleStatSubtypeDecEq {First : Type*} {predicate : First → Prop} : DecidableEq (Subtype predicate) := Classical.decEq _
variable {Primary Body Color : Type*} [Fintype Primary] [Fintype Body] [Fintype Color]
  [DecidableEq Primary] [DecidableEq Body]

private def seedPrimaryEquiv (seed : InputSeed Color) : Fin seed.primaryOrder ≃ PrimaryRoles (inputSeedRole seed) :=
  Equiv.ofBijective (fun index => ⟨Fin.castAdd seed.bodyOrder index,by simp [inputSeedRole]⟩) (by
    constructor
    · intro first second he
      apply Fin.ext
      exact congrArg (fun x => x.val.val) he
    · intro index
      rcases index with ⟨index,hi⟩
      revert hi
      refine Fin.addCases ?_ ?_ index
      · intro first _; exact ⟨first,rfl⟩
      · intro second hh; simp [inputSeedRole] at hh)

private def seedBodyEquiv (seed : InputSeed Color) : Fin seed.bodyOrder ≃ BodyRoles (inputSeedRole seed) :=
  Equiv.ofBijective (fun index => ⟨Fin.natAdd seed.primaryOrder index,by simp [inputSeedRole]⟩) (by
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
      · intro first hh; simp [inputSeedRole] at hh
      · intro second _; exact ⟨second,rfl⟩)

def mixedSeedPrimaryEquiv (kernel : (Primary ⊕ Body → Color) → ℝ) :
    Primary ≃ PrimaryRoles (inputSeedRole (mixedFiniteSeed kernel)) :=
  (Fintype.equivFin Primary).trans (seedPrimaryEquiv (mixedFiniteSeed kernel))

def mixedSeedBodyEquiv (kernel : (Primary ⊕ Body → Color) → ℝ) :
    Body ≃ BodyRoles (inputSeedRole (mixedFiniteSeed kernel)) :=
  (Fintype.equivFin Body).trans (seedBodyEquiv (mixedFiniteSeed kernel))

omit [Fintype Color] [DecidableEq Primary] [DecidableEq Body] in
theorem mixedSeedRole_partition (kernel : (Primary ⊕ Body → Color) → ℝ) (slot : Primary ⊕ Body) :
    (rolePartition (inputSeedRole (mixedFiniteSeed kernel)))
      (Equiv.sumCongr (mixedSeedPrimaryEquiv kernel) (mixedSeedBodyEquiv kernel) slot)=mixedFiniteEquiv slot := by
  cases slot <;> rfl

omit [Fintype Color] [DecidableEq Primary] [DecidableEq Body] in
theorem publicRoleKernel_mixedSeed (kernel : (Primary ⊕ Body → Color) → ℝ) :
    publicRoleKernel (mixedFiniteSeed kernel)=
      fun word => kernel (word ∘ Equiv.sumCongr (mixedSeedPrimaryEquiv kernel) (mixedSeedBodyEquiv kernel)) := by
  funext word
  change kernel ((word ∘ (rolePartition (inputSeedRole (mixedFiniteSeed kernel))).symm) ∘ mixedFiniteEquiv)=_
  apply congrArg kernel
  funext slot
  change word ((rolePartition _).symm (mixedFiniteEquiv slot))=_
  rw [← mixedSeedRole_partition kernel slot,Equiv.symm_apply_apply]
  rfl

omit [DecidableEq Primary] [DecidableEq Body] in
/-- A joint paired score commutes with a change of the names of its primary
and body coordinates. All compensation terms remain in the same kernel. -/
theorem pairedPublicKernel_sum_reindex {P' B' : Type*} [Fintype P'] [Fintype B']
    [DecidableEq P'] [DecidableEq B']
    (primary body : FiniteDist Color) (anchor : Color → Color → ℝ) (activation : ℝ)
    (p : Primary ≃ P') (b : Body ≃ B') (kernel : (Primary ⊕ Body → Color) → ℝ) :
    pairedPublicKernel primary body anchor activation (Sum.elim (fun _ : P' => true) (fun _ : B' => false))
      (fun word => kernel (word ∘ Equiv.sumCongr p b))=
    fun word => pairedPublicKernel primary body anchor activation
      (Sum.elim (fun _ : Primary => true) (fun _ : Body => false)) kernel (word ∘ Equiv.sumCongr p b) := by
  funext word
  have hh := MixedKernel.matrixApply_reindex (Equiv.sumCongr p b)
    (fun slot => publicInputMatrix primary body anchor activation
      (Sum.elim (fun _ : Primary => true) (fun _ : Body => false) slot)) kernel word
  have he : (fun slot => publicInputMatrix primary body anchor activation
      (Sum.elim (fun _ : Primary => true) (fun _ : Body => false) ((Equiv.sumCongr p b).symm slot)))=
      fun slot => publicInputMatrix primary body anchor activation
        (Sum.elim (fun _ : P' => true) (fun _ : B' => false) slot) := by
    funext slot; cases slot <;> rfl
  rw [he] at hh
  exact hh

omit [DecidableEq Primary] [DecidableEq Body] in
/-- Repacking a literal mixed seed leaves its complete paired U-statistic
unchanged, including the exact without-replacement denominators. -/
theorem mixedSeed_paired_statistic (primary body : FiniteDist Color) (anchor : Color → Color → ℝ)
    (activation : ℝ) (kernel : (Primary ⊕ Body → Color) → ℝ)
    {PP BP : Type*} [Fintype PP] [Fintype BP] (word : PP ⊕ BP → Color × Color) :
    twoPoolStatistic (pairedPublicKernel primary body anchor activation
      (Sum.elim (fun _ : PrimaryRoles (inputSeedRole (mixedFiniteSeed kernel)) => true)
        (fun _ : BodyRoles (inputSeedRole (mixedFiniteSeed kernel)) => false))
      (publicRoleKernel (mixedFiniteSeed kernel))) word=
    twoPoolStatistic (pairedPublicKernel primary body anchor activation
      (Sum.elim (fun _ : Primary => true) (fun _ : Body => false)) kernel) word := by
  rw [publicRoleKernel_mixedSeed,pairedPublicKernel_sum_reindex]
  have h := twoPoolStatistic_reindex (mixedSeedPrimaryEquiv kernel) (mixedSeedBodyEquiv kernel)
    (Equiv.refl PP) (Equiv.refl BP)
    (pairedPublicKernel primary body anchor activation
      (Sum.elim (fun _ : Primary => true) (fun _ : Body => false)) kernel) word
  simpa only [Equiv.sumCongr_refl,Equiv.coe_refl,Function.comp_id] using h

theorem mixedMonomial_paired_statistic_any (primary body : FiniteDist Color) (anchor : Color → Color → ℝ)
    (activation : ℝ) (powers : InputSeed Color →₀ ℕ)
    {PP BP : Type*} [Fintype PP] [Fintype BP] (word : PP ⊕ BP → Color × Color) :
    twoPoolStatistic (pairedPublicKernel primary body anchor activation
      (Sum.elim (fun _ : PrimaryRoles (inputSeedRole (mixedMonomialSeed powers)) => true)
        (fun _ : BodyRoles (inputSeedRole (mixedMonomialSeed powers)) => false))
      (publicRoleKernel (mixedMonomialSeed powers))) word=
      twoPoolStatistic (twoPoolPairedKernel primary body anchor activation (monomialOccurrences powers)) word := by
  letI : DecidableEq (ControlPrimarySlot (monomialOccurrences powers)) := Classical.decEq _
  letI : DecidableEq (ControlBodySlot (monomialOccurrences powers)) := Classical.decEq _
  simpa only [mixedMonomialSeed,mixedProductSeed,twoPoolPairedKernel] using
    mixedSeed_paired_statistic primary body anchor activation (twoPoolControlKernel (monomialOccurrences powers)) word

theorem mixedMonomial_paired_statistic (primary body : FiniteDist Color) (anchor : Color → Color → ℝ)
    (activation : ℝ) (primaryPool bodyPool : ℕ) (powers : InputSeed Color →₀ ℕ)
    (word : Fin primaryPool ⊕ Fin bodyPool → Color × Color) :
    twoPoolStatistic (pairedPublicKernel primary body anchor activation
      (Sum.elim (fun _ : PrimaryRoles (inputSeedRole (mixedMonomialSeed powers)) => true)
        (fun _ : BodyRoles (inputSeedRole (mixedMonomialSeed powers)) => false))
      (publicRoleKernel (mixedMonomialSeed powers))) word=
      monomialPairedStatistic primary body anchor activation primaryPool bodyPool powers word :=
  by
    letI : DecidableEq (ControlPrimarySlot (monomialOccurrences powers)) := Classical.decEq _
    letI : DecidableEq (ControlBodySlot (monomialOccurrences powers)) := Classical.decEq _
    simpa only [mixedMonomialSeed,mixedProductSeed,monomialPairedStatistic,twoPoolPairedKernel] using
      mixedSeed_paired_statistic primary body anchor activation (twoPoolControlKernel (monomialOccurrences powers)) word

end
end AFT.V7Calibration
