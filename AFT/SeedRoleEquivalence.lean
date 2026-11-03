import AFT.OrderedControlReindex
import AFT.WholeBoundarySeed

/-! # Role-preserving equivalence of complete joint input seeds -/
namespace AFT.RepresentedPolynomial
open V7Calibration CanonicalMoments
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
local instance seedRoleFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance seedRoleSumDecEq {First Second : Type*} : DecidableEq (First ⊕ Second) := Classical.decEq _
local instance seedRoleSubtypeDecEq {First : Type*} {predicate : First → Prop} : DecidableEq (Subtype predicate) := Classical.decEq _
variable {Color : Type*}

/-- Reindex the full joint kernel while retaining each coordinate's primary/body role. -/
structure SeedRoleEquiv (first second : InputSeed Color) where
  coordinates : Fin (first.primaryOrder+first.bodyOrder) ≃ Fin (second.primaryOrder+second.bodyOrder)
  role : ∀ slot,inputSeedRole second (coordinates slot)=inputSeedRole first slot
  kernel : ∀ word,first.kernel (word ∘ coordinates)=second.kernel word

namespace SeedRoleEquiv
variable {first second third : InputSeed Color}

 def refl (seed : InputSeed Color) : SeedRoleEquiv seed seed :=
  ⟨Equiv.refl _,fun _ => rfl,fun _ => rfl⟩

 def trans (one : SeedRoleEquiv first second) (two : SeedRoleEquiv second third) : SeedRoleEquiv first third :=
  ⟨one.coordinates.trans two.coordinates,
    fun slot => (two.role _).trans (one.role slot),
    fun word => (one.kernel (word ∘ two.coordinates)).trans (two.kernel word)⟩

 def symm (equiv : SeedRoleEquiv first second) : SeedRoleEquiv second first :=
  ⟨equiv.coordinates.symm,fun slot => by simpa using (equiv.role (equiv.coordinates.symm slot)).symm,
    fun word => by
      have hh := equiv.kernel (word ∘ equiv.coordinates.symm)
      simpa only [Function.comp_assoc,Equiv.symm_comp_self,Function.comp_id] using hh.symm⟩

 def primary (equiv : SeedRoleEquiv first second) :
    PrimaryRoles (inputSeedRole first)≃PrimaryRoles (inputSeedRole second) :=
  Equiv.subtypeEquiv equiv.coordinates (fun slot => by rw [equiv.role])

 def body (equiv : SeedRoleEquiv first second) :
    BodyRoles (inputSeedRole first)≃BodyRoles (inputSeedRole second) :=
  Equiv.subtypeEquiv equiv.coordinates (fun slot => by rw [equiv.role])

 theorem primaryOrder_eq (equiv : SeedRoleEquiv first second) : first.primaryOrder=second.primaryOrder := by
  simpa only [inputSeedRole_primary_card] using Fintype.card_congr equiv.primary

 theorem bodyOrder_eq (equiv : SeedRoleEquiv first second) : first.bodyOrder=second.bodyOrder := by
  simpa only [inputSeedRole_body_card] using Fintype.card_congr equiv.body

 theorem reference [Fintype Color] (equiv : SeedRoleEquiv first second)
    (primary body : FiniteDist Color) (slot : Fin (first.primaryOrder+first.bodyOrder)) :
    inputReference primary body second (equiv.coordinates slot)=inputReference primary body first slot := by
  have hr (seed : InputSeed Color) (index : Fin (seed.primaryOrder+seed.bodyOrder)) :
      inputReference primary body seed index=if inputSeedRole seed index then primary else body := by
    cases index using Fin.addCases <;> simp [inputReference,inputSeedRole]
  simp only [hr,equiv.role]

 theorem primary_mem [Fintype Color] (equiv : SeedRoleEquiv first second)
    (slot : Fin (first.primaryOrder+first.bodyOrder)) :
    equiv.coordinates slot∈primaryCoordinates second ↔ slot∈primaryCoordinates first := by
  have hm (seed : InputSeed Color) (index : Fin (seed.primaryOrder+seed.bodyOrder)) :
      index∈primaryCoordinates seed ↔ inputSeedRole seed index=true := by
    cases index using Fin.addCases with
    | left index => simp [primaryCoordinates,inputSeedRole,List.mem_ofFn]
    | right index =>
      simp only [primaryCoordinates,List.mem_ofFn,inputSeedRole,Fin.addCases_right,Bool.false_eq_true,iff_false]
      rintro ⟨j,hj⟩
      have hh := congrArg Fin.val hj
      simp only [Fin.val_castAdd,Fin.val_natAdd] at hh
      omega
  rw [hm,hm,equiv.role]

 theorem partition (equiv : SeedRoleEquiv first second)
    (slot : PrimaryRoles (inputSeedRole first)⊕BodyRoles (inputSeedRole first)) :
    rolePartition (inputSeedRole second) (Equiv.sumCongr equiv.primary equiv.body slot)=
      equiv.coordinates (rolePartition (inputSeedRole first) slot) := by
  cases slot <;> rfl

 theorem publicKernel (equiv : SeedRoleEquiv first second) :
    (fun word => publicRoleKernel first (word ∘ Equiv.sumCongr equiv.primary equiv.body))=
      publicRoleKernel second := by
  funext word
  unfold publicRoleKernel
  rw [← equiv.kernel (word ∘ (rolePartition (inputSeedRole second)).symm)]
  congr 1
  funext slot
  change word (Equiv.sumCongr equiv.primary equiv.body ((rolePartition (inputSeedRole first)).symm slot))=
    word ((rolePartition (inputSeedRole second)).symm (equiv.coordinates slot))
  apply congrArg word
  apply (rolePartition (inputSeedRole second)).injective
  rw [equiv.partition,Equiv.apply_symm_apply,Equiv.apply_symm_apply]

 theorem pairedStatistic [Fintype Color] (equiv : SeedRoleEquiv first second)
    (primary body : FiniteDist Color) (anchor : Color → Color → ℝ) (activation : ℝ)
    {PP BP : Type*} [Fintype PP] [Fintype BP] (word : PP⊕BP → Color×Color) :
    twoPoolStatistic (pairedPublicKernel primary body anchor activation
      (Sum.elim (fun _ : PrimaryRoles (inputSeedRole first) => true)
        (fun _ : BodyRoles (inputSeedRole first) => false)) (publicRoleKernel first)) word=
    twoPoolStatistic (pairedPublicKernel primary body anchor activation
      (Sum.elim (fun _ : PrimaryRoles (inputSeedRole second) => true)
        (fun _ : BodyRoles (inputSeedRole second) => false)) (publicRoleKernel second)) word := by
  have hp := pairedPublicKernel_sum_reindex primary body anchor activation equiv.primary equiv.body (publicRoleKernel first)
  rw [equiv.publicKernel] at hp
  have hh := twoPoolStatistic_reindex equiv.primary equiv.body (Equiv.refl PP) (Equiv.refl BP)
    (pairedPublicKernel primary body anchor activation
      (Sum.elim (fun _ : PrimaryRoles (inputSeedRole first) => true)
        (fun _ : BodyRoles (inputSeedRole first) => false)) (publicRoleKernel first)) word
  rw [hp]
  simpa only [Equiv.sumCongr_refl,Equiv.coe_refl,Function.comp_id] using hh.symm

end SeedRoleEquiv
end
end AFT.RepresentedPolynomial
