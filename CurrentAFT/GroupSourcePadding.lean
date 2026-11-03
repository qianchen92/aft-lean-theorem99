import CurrentAFT.CalibrationRectanglePadding
import CurrentAFT.WeightCoordinateDecode

/-! Native base-q padding of bounded grouped sources. A primary has two
roots and one control; an ordinary group has one root and a safe control;
a retained group has one root. Padding is checked explicitly. -/
namespace CurrentAFT.GroupSourcePadding
open scoped BigOperators
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

inductive Kind where
  | primary
  | ordinary
  | kept
  deriving DecidableEq

def Input (q : ℕ) (safe : Fin q → Prop) : Kind → Type
  | .primary => (Fin 2 → Fin q) × Fin q
  | .ordinary => (Fin 1 → Fin q) × {color : Fin q // safe color}
  | .kept => (Fin 1 → Fin q) × Unit

instance inputFintype (q : ℕ) (safe : Fin q → Prop) [DecidablePred safe] (kind : Kind) : Fintype (Input q safe kind) := by
  cases kind <;> unfold Input <;> infer_instance

def encode (q : ℕ) (hq : 0 < q) (safe : Fin q → Prop) : (kind : Kind) → Input q safe kind → (Fin 3 → Fin q)
  | .primary, input => ![input.1 0, input.1 1, input.2]
  | .ordinary, input => ![input.1 0, input.2.val, ⟨0, hq⟩]
  | .kept, input => ![input.1 0, ⟨0, hq⟩, ⟨0, hq⟩]

def Valid (q : ℕ) (safe : Fin q → Prop) : Kind → (Fin 3 → Fin q) → Prop
  | .primary, _ => True
  | .ordinary, word => safe (word 1) ∧ (word 2).val = 0
  | .kept, word => (word 1).val = 0 ∧ (word 2).val = 0

instance validDecidable (q : ℕ) (safe : Fin q → Prop) [DecidablePred safe] (kind : Kind) (word : Fin 3 → Fin q) :
    Decidable (Valid q safe kind word) := by
  cases kind <;> unfold Valid <;> infer_instance

def recover (q : ℕ) (safe : Fin q → Prop) : (kind : Kind) → (word : Fin 3 → Fin q) → Valid q safe kind word → Input q safe kind
  | .primary, word, _ => (![word 0, word 1], word 2)
  | .ordinary, word, h => (fun _ => word 0, ⟨word 1, h.1⟩)
  | .kept, word, _ => (fun _ => word 0, ())

theorem encode_valid (q : ℕ) (hq : 0 < q) (safe : Fin q → Prop) (kind : Kind) (input : Input q safe kind) :
    Valid q safe kind (encode q hq safe kind input) := by
  cases kind with
  | primary => trivial
  | ordinary => exact ⟨input.2.property, rfl⟩
  | kept => exact ⟨rfl, rfl⟩

theorem recover_encode (q : ℕ) (hq : 0 < q) (safe : Fin q → Prop) (kind : Kind) (input : Input q safe kind) :
    recover q safe kind (encode q hq safe kind input) (encode_valid q hq safe kind input) = input := by
  cases kind with
  | primary =>
    apply Prod.ext
    · funext slot
      fin_cases slot <;> rfl
    · rfl
  | ordinary =>
    apply Prod.ext
    · funext slot
      fin_cases slot
      rfl
    · rfl
  | kept =>
    apply Prod.ext
    · funext slot
      fin_cases slot
      rfl
    · exact Subsingleton.elim _ _

theorem encode_recover (q : ℕ) (hq : 0 < q) (safe : Fin q → Prop) (kind : Kind)
    (word : Fin 3 → Fin q) (h : Valid q safe kind word) :
    encode q hq safe kind (recover q safe kind word h) = word := by
  funext slot
  cases kind with
  | primary => fin_cases slot <;> rfl
  | ordinary =>
    fin_cases slot
    · rfl
    · rfl
    · apply Fin.ext; exact h.2.symm
  | kept =>
    fin_cases slot
    · rfl
    · apply Fin.ext; exact h.1.symm
    · apply Fin.ext; exact h.2.symm

theorem encode_injective (q : ℕ) (hq : 0 < q) (safe : Fin q → Prop) (kind : Kind) :
    Function.Injective (encode q hq safe kind) := by
  intro first second h
  have hh := congrArg (fun word : {word // Valid q safe kind word} => recover q safe kind word.val word.property)
    (show (⟨encode q hq safe kind first, encode_valid q hq safe kind first⟩ : {word // Valid q safe kind word}) =
      ⟨encode q hq safe kind second, encode_valid q hq safe kind second⟩ from Subtype.ext h)
  simpa only [recover_encode] using hh

section Grouped
variable {Group : Type*} [Fintype Group] (q : ℕ) (hq : 0 < q) (safe : Fin q → Prop) [DecidablePred safe]
  (kind : Group → Kind)

abbrev Source := (group : Group) → Input q safe (kind group)
abbrev Word := Group → Fin 3 → Fin q

instance sourceFintype [DecidableEq Group] : Fintype (Source q safe kind) :=
  Pi.instFintype

def sourceEncode (source : Source q safe kind) : Word (Group := Group) q :=
  fun group => encode q hq safe (kind group) (source group)

def sourceDecode (word : Word (Group := Group) q) : Option (Source q safe kind) :=
  if h : ∀ group, Valid q safe (kind group) (word group) then
    some (fun group => recover q safe (kind group) (word group) (h group)) else none

theorem sourceDecode_encode (source : Source q safe kind) :
    sourceDecode q safe kind (sourceEncode q hq safe kind source) = some source := by
  unfold sourceDecode sourceEncode
  rw [dif_pos (fun group => encode_valid q hq safe (kind group) (source group))]
  congr 1
  funext group
  exact recover_encode q hq safe (kind group) (source group)

omit [Fintype Group] [DecidablePred safe] in
theorem sourceEncode_injective : Function.Injective (sourceEncode q hq safe kind) := by
  intro first second h
  funext group
  exact encode_injective q hq safe (kind group) (congrFun h group)

theorem sourceDecode_eq_some (word : Word (Group := Group) q) (source : Source q safe kind) :
    sourceDecode q safe kind word = some source ↔ word = sourceEncode q hq safe kind source := by
  constructor
  · intro h
    unfold sourceDecode at h
    split at h
    · rename_i hv
      have he := Option.some.inj h
      subst source
      funext group
      exact (encode_recover q hq safe (kind group) (word group) (hv group)).symm
    · cases h
  · rintro rfl
    exact sourceDecode_encode q hq safe kind source

end Grouped

def flatten {Group : Type*} (count q : ℕ) (ordering : Fin count ≃ Group) :
    (Group → Fin 3 → Fin q) ≃ (Fin (count*3) → Fin q) where
  toFun word index := word (ordering (finProdFinEquiv.symm index).1) (finProdFinEquiv.symm index).2
  invFun word group slot := word (finProdFinEquiv (ordering.symm group, slot))
  left_inv word := by funext group slot; simp
  right_inv word := by
    funext index
    dsimp only
    rw [Equiv.symm_apply_apply]
    exact congrArg word (finProdFinEquiv.apply_symm_apply index)

def tupleEquiv (q count : ℕ) (hq : 0 < q) : (Fin count → Fin q) ≃ Fin (q^count) where
  toFun word := ⟨WeightCoordinates.tupleCode q count (fun index => (word index).val),
    WeightCoordinates.tupleCode_lt q count hq _ (fun index => (word index).isLt)⟩
  invFun index := WeightCoordinates.tupleDecode q hq count index.val
  left_inv word := WeightCoordinates.tupleDecode_code q count hq word
  right_inv index := by apply Fin.ext; exact WeightCoordinates.tupleCode_decode q count hq index.val index.isLt

section Indexed
variable {Group : Type*} [Fintype Group] [DecidableEq Group] (q : ℕ) (hq : 0 < q) (safe : Fin q → Prop) [DecidablePred safe]
  (kind : Group → Kind) (count : ℕ) (ordering : Fin count ≃ Group)

def indexEquiv : Word (Group := Group) q ≃ Fin (q^(count*3)) :=
  (flatten count q ordering).trans (tupleEquiv q (count*3) hq)

def indexEncode : Source q safe kind ↪ Fin (q^(count*3)) where
  toFun source := indexEquiv q hq count ordering (sourceEncode q hq safe kind source)
  inj' := (indexEquiv q hq count ordering).injective.comp (sourceEncode_injective q hq safe kind)

def indexDecode (index : Fin (q^(count*3))) : Option (Source q safe kind) :=
  sourceDecode q safe kind ((indexEquiv q hq count ordering).symm index)

omit [DecidableEq Group] in
theorem indexDecode_eq_some (index : Fin (q^(count*3))) (source : Source q safe kind) :
    indexDecode q hq safe kind count ordering index = some source ↔
      index = indexEncode q hq safe kind count ordering source := by
  rw [indexDecode, sourceDecode_eq_some q hq safe kind]
  exact (indexEquiv q hq count ordering).symm_apply_eq

theorem sum_index {Scalar : Type*} [AddCommMonoid Scalar] (summand : Source q safe kind → Scalar) :
    (∑ index : Fin (q^(count*3)), (indexDecode q hq safe kind count ordering index).elim 0 summand) =
      ∑ source, summand source :=
  CalibrationRectanglePadding.sum_extend (indexEncode q hq safe kind count ordering)
    (indexDecode q hq safe kind count ordering) (indexDecode_eq_some q hq safe kind count ordering) summand

end Indexed
end CurrentAFT.GroupSourcePadding
