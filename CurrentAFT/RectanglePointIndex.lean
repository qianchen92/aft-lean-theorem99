import CurrentAFT.CalibrationPointCoordinates
import CurrentAFT.CalibrationRectanglePadding
import CurrentAFT.WeightCoordinateDecode

/-! # Explicit finite coordinates of safe joint points in rectangular arrays

Enumeration is by integer counters, and the inverse searches this bounded
list. The list has at most `(D+1)^2 q^D` entries; no finite-choice enumeration
or subset of an exponentially larger latent space is used.
-/
namespace CurrentAFT.RectanglePointIndex
open AFT GradedControlAlgebra WeightCoordinates
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

abbrev Point (base order : ℕ) (safe : Fin base → Prop) :=
  CalibrationPointCoordinates.PointIndex (Fin base) {color : Fin base // safe color} order
abbrev Rectangle (base order : ℕ) := Fin ((order+1)^2) × Fin (base^order)

def encode (base order : ℕ) (hb : 0 < base) (safe : Fin base → Prop)
    (point : Point base order safe) : Rectangle base order :=
  (arityIndex order point.1.val.1 point.1.val.2,
    wordIndex base order point.1.val.1.val point.1.val.2.val hb point.1.property
      point.2.1 (fun index => (point.2.2 index).val))

def words (base count : ℕ) (hb : 0 < base) : List (Fin count → Fin base) :=
  List.ofFn (fun index : Fin (base^count) => tupleDecode base hb count index.val)

def arities (order : ℕ) : List (TruncatedArity order) :=
  (List.finRange (order+1)).flatMap (fun first =>
    (List.finRange (order+1)).filterMap (fun second =>
      if h : first.val + second.val ≤ order then some ⟨(first, second), h⟩ else none))

def atArity (base order : ℕ) (hb : 0 < base) (safe : Fin base → Prop) [DecidablePred safe]
    (arity : TruncatedArity order) : List (Point base order safe) :=
  (words base arity.val.1.val hb).flatMap (fun primary =>
    (words base arity.val.2.val hb).filterMap (fun body =>
      if h : ∀ index, safe (body index) then
        some ⟨arity, primary, fun index => ⟨body index, h index⟩⟩ else none))

def points (base order : ℕ) (hb : 0 < base) (safe : Fin base → Prop) [DecidablePred safe] :
    List (Point base order safe) :=
  (arities order).flatMap (atArity base order hb safe)

def decode (base order : ℕ) (hb : 0 < base) (safe : Fin base → Prop) [DecidablePred safe]
    (index : Rectangle base order) : Option (Point base order safe) :=
  (points base order hb safe).find? (fun point => decide (encode base order hb safe point = index))

theorem encode_injective (base order : ℕ) (hb : 0 < base) (safe : Fin base → Prop) :
    Function.Injective (encode base order hb safe) := by
  rintro ⟨arity, primary, body⟩ ⟨arity', primary', body'⟩ he
  have ha := arityCode_injective order (congrArg Prod.fst he)
  have haa : arity = arity' := Subtype.ext ha
  subst arity'
  have hw := congrArg (fun index : Rectangle base order => index.2.val) he
  have hh : (primary, fun i => (body i).val) = (primary', fun i => (body' i).val) :=
    jointCode_injective base arity.val.1.val arity.val.2.val hb hw
  have hp := congrArg Prod.fst hh
  have hb' := congrArg Prod.snd hh
  have hb'' : body = body' := by
    funext index
    exact Subtype.ext (congrFun hb' index)
  cases hp
  cases hb''
  rfl

theorem mem_words (base count : ℕ) (hb : 0 < base) (word : Fin count → Fin base) :
    word ∈ words base count hb := by
  apply List.mem_ofFn.mpr
  exact ⟨⟨tupleCode base count (fun i => (word i).val), tupleCode_lt base count hb _ (fun i => (word i).isLt)⟩,
    tupleDecode_code base count hb word⟩

theorem mem_arities (order : ℕ) (arity : TruncatedArity order) : arity ∈ arities order := by
  apply List.mem_flatMap.mpr
  refine ⟨arity.val.1, List.mem_finRange _, ?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨arity.val.2, List.mem_finRange _, ?_⟩
  simp only [dif_pos arity.property]

theorem mem_atArity (base order : ℕ) (hb : 0 < base) (safe : Fin base → Prop) [DecidablePred safe]
    (point : Point base order safe) : point ∈ atArity base order hb safe point.1 := by
  apply List.mem_flatMap.mpr
  refine ⟨point.2.1, mem_words base _ hb _, ?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨fun i => (point.2.2 i).val, mem_words base _ hb _, ?_⟩
  rw [dif_pos (fun i => (point.2.2 i).property)]

theorem mem_points (base order : ℕ) (hb : 0 < base) (safe : Fin base → Prop) [DecidablePred safe]
    (point : Point base order safe) : point ∈ points base order hb safe :=
  List.mem_flatMap.mpr ⟨point.1, mem_arities order point.1, mem_atArity base order hb safe point⟩

theorem decode_eq_some (base order : ℕ) (hb : 0 < base) (safe : Fin base → Prop) [DecidablePred safe]
    (index : Rectangle base order) (point : Point base order safe) :
    decode base order hb safe index = some point ↔ index = encode base order hb safe point := by
  constructor
  · intro h
    have hh := List.find?_some h
    exact (of_decide_eq_true hh).symm
  · intro h
    subst index
    have hs : (decode base order hb safe (encode base order hb safe point)).isSome := by
      apply List.find?_isSome.mpr
      exact ⟨point, mem_points base order hb safe point, by simp⟩
    cases hd : decode base order hb safe (encode base order hb safe point) with
    | none => simp only [hd, Option.isSome_none, Bool.false_eq_true] at hs
    | some found =>
      have hh := List.find?_some hd
      have he := encode_injective base order hb safe (of_decide_eq_true hh)
      exact congrArg some he

private theorem length_flatMap_le {Source Target : Type*} (list : List Source)
    (value : Source → List Target) (bound : ℕ) (hvalue : ∀ source ∈ list, (value source).length ≤ bound) :
    (list.flatMap value).length ≤ list.length * bound := by
  induction list with
  | nil => simp
  | cons first rest ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have ht := ih (fun point hpoint => hvalue point (List.mem_cons_of_mem _ hpoint))
    have hh := hvalue first List.mem_cons_self
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem words_length (base count : ℕ) (hb : 0 < base) : (words base count hb).length = base^count :=
  List.length_ofFn

theorem arities_length (order : ℕ) : (arities order).length ≤ (order+1)^2 := by
  have h := length_flatMap_le (List.finRange (order+1))
    (fun first : Fin (order+1) => (List.finRange (order+1)).filterMap (fun second =>
      if h : first.val+second.val ≤ order then some (⟨(first, second), h⟩ : TruncatedArity order) else none))
    (order+1) (fun _ _ => (List.length_filterMap_le _ _).trans_eq List.length_finRange)
  simpa only [List.length_finRange, pow_two] using h

theorem atArity_length (base order : ℕ) (hb : 0 < base) (safe : Fin base → Prop) [DecidablePred safe]
    (arity : TruncatedArity order) : (atArity base order hb safe arity).length ≤ base^order := by
  have h := length_flatMap_le (words base arity.val.1.val hb)
    (fun primary => (words base arity.val.2.val hb).filterMap (fun body =>
      if h : ∀ index, safe (body index) then
        some (⟨arity, primary, fun index => ⟨body index, h index⟩⟩ : Point base order safe) else none))
    (base^arity.val.2.val) (fun _ _ => (List.length_filterMap_le _ _).trans_eq (words_length base _ hb))
  simp only [words_length, ← pow_add] at h
  exact h.trans (Nat.pow_le_pow_right hb arity.property)

theorem points_length (base order : ℕ) (hb : 0 < base) (safe : Fin base → Prop) [DecidablePred safe] :
    (points base order hb safe).length ≤ (order+1)^2 * base^order :=
  (length_flatMap_le (arities order) (atArity base order hb safe) (base^order)
    (fun arity _ => atArity_length base order hb safe arity)).trans
      (Nat.mul_le_mul_right _ (arities_length order))

end CurrentAFT.RectanglePointIndex
