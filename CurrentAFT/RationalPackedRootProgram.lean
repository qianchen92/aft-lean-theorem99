import CurrentAFT.RationalRootGroupProgram
import CurrentAFT.RationalFamilyWordProduct
import CurrentAFT.CurrentGroupSourcePadding

/-! # A native base-q program for the whole joint root/control summand

The metadata contain only small role and root-slot arrays. Gaussian,
proposal, inverse and cycle entries are all computed by the existing
rational programs; the source array is enumerated as one joint word.
-/
namespace CurrentAFT.RationalPackedRootProgram
open AFT RationalRootGroupProgram RationalFamilyProductProgram
open scoped BigOperators
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

structure Metadata (primaryDegree bodyDegree keptCount tagCount : ℕ) where
  roles : Fin ((primaryDegree + bodyDegree) + keptCount) → LocalRole
  taggedSlots : Fin tagCount → Fin ((primaryDegree + bodyDegree) + keptCount) × Fin 2

def sourceWord (security groups : ℕ) (index : Fin ((CurrentRectangleIndex.colors security)^(groups*3))) :
    Fin groups → Fin 3 → ℕ :=
  fun group slot => (WeightCoordinates.tupleDecode (CurrentRectangleIndex.colors security)
    (CurrentRectangleIndex.colors_pos security) (groups*3) index.val (finProdFinEquiv (group, slot))).val

def validGroup (security : ℕ) (role : LocalRole) (word : Fin 3 → ℕ) : Prop :=
  match role with
  | .primary => True
  | .ordinary => RationalBackgroundProfiles.Safe security (word 1) ∧ word 2 = 0
  | .leg | .center | .queue => word 1 = 0 ∧ word 2 = 0

instance validGroupDecidable (security : ℕ) (role : LocalRole) (word : Fin 3 → ℕ) : Decidable (validGroup security role word) := by
  cases role <;> unfold validGroup <;> infer_instance

def Valid {r s kept tags : ℕ} (security : ℕ) (metadata : Metadata r s kept tags)
    (word : Fin ((r+s)+kept) → Fin 3 → ℕ) : Prop := ∀ group, validGroup security (metadata.roles group) (word group)

instance validDecidable {r s kept tags : ℕ} (security : ℕ) (metadata : Metadata r s kept tags)
    (word : Fin ((r+s)+kept) → Fin 3 → ℕ) : Decidable (Valid security metadata word) := by
  unfold Valid
  infer_instance

def primaryGroup (r s kept : ℕ) (index : Fin r) : Fin ((r+s)+kept) := ⟨index.val, by omega⟩

def ordinaryGroup (r s kept : ℕ) (index : Fin s) : Fin ((r+s)+kept) := ⟨r + index.val, by omega⟩

def rootActive (role : LocalRole) (slot : Fin 2) : Prop := role = .primary ∨ slot.val = 0

instance rootActiveDecidable (role : LocalRole) (slot : Fin 2) : Decidable (rootActive role slot) := by
  unfold rootActive
  infer_instance

def untagged {r s kept tags : ℕ} (security bits : ℕ) (metadata : Metadata r s kept tags)
    (word : Fin ((r+s)+kept) → Fin 3 → ℕ) : ℚ :=
  ∏ group, ∏ slot : Fin 2,
    if rootActive (metadata.roles group) slot ∧ ¬∃ tag, metadata.taggedSlots tag = (group, slot) then
      RootSignedMassProgram.referenceEntry security bits (word group slot.castSucc) else 1

def control {r s kept tags : ℕ} (security bits : ℕ) (_metadata : Metadata r s kept tags)
    (sourcePrimary : Fin r → ℕ) (sourceBody : Fin s → ℕ) (word : Fin ((r+s)+kept) → Fin 3 → ℕ) : ℚ :=
  WeightedPointKernelProgram.current security bits r s sourcePrimary sourceBody
    (fun index => word (primaryGroup r s kept index) 2) (fun index => word (ordinaryGroup r s kept index) 1)

def signed {r s kept tags : ℕ} (security bits : ℕ) (metadata : Metadata r s kept tags)
    (word : Fin ((r+s)+kept) → Fin 3 → ℕ) : ℚ :=
  RootSignedMassProgram.weightedEntry security bits tags
    (fun tag => word (metadata.taggedSlots tag).1 (metadata.taggedSlots tag).2.castSucc)

def localProduct {r s kept tags : ℕ} (security bits order : ℕ) (queue : ℤ) (metadata : Metadata r s kept tags)
    (word : Fin ((r+s)+kept) → Fin 3 → ℕ) : Table ℚ ℕ ℕ order :=
  RationalFamilyWordProduct.current order ((r+s)+kept)
    (fun group => localTable security bits order queue (metadata.roles group) (word group))

def summand {r s kept tags : ℕ} (security bits order : ℕ) (queue : ℤ) (metadata : Metadata r s kept tags)
    (sourcePrimary : Fin r → ℕ) (sourceBody : Fin s → ℕ) (word : Fin ((r+s)+kept) → Fin 3 → ℕ) : Table ℚ ℕ ℕ order :=
  fun arity colors centers => if Valid security metadata word then
    control security bits metadata sourcePrimary sourceBody word * untagged security bits metadata word * signed security bits metadata word *
      localProduct security bits order queue metadata word arity colors centers else 0

def current {r s kept tags : ℕ} (security bits order : ℕ) (queue : ℤ) (metadata : Metadata r s kept tags)
    (sourcePrimary : Fin r → ℕ) (sourceBody : Fin s → ℕ) : Table ℚ ℕ ℕ order :=
  fun arity colors centers => ∑ index : Fin ((CurrentRectangleIndex.colors security)^(((r+s)+kept)*3)),
    summand security bits order queue metadata sourcePrimary sourceBody
      (sourceWord security ((r+s)+kept) index) arity colors centers

theorem source_count {r s kept tags : ℕ} (security : ℕ) (_metadata : Metadata r s kept tags)
    (hkept : kept ≤ tags) :
    (CurrentRectangleIndex.colors security)^(((r+s)+kept)*3) ≤
      (CurrentRectangleIndex.colors security)^((r+s+tags)*3) := by
  exact Nat.pow_le_pow_right (CurrentRectangleIndex.colors_pos security)
    (Nat.mul_le_mul_right 3 (Nat.add_le_add_left hkept _))

end CurrentAFT.RationalPackedRootProgram
