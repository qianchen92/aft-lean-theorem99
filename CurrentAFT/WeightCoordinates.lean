import Mathlib

/-! # Fixed rectangular coordinates for the current joint weight tables

Primary digits precede body digits.  These coordinates retain every joint
entry; positivity and runtime are supplied by separate program modules.
-/
namespace CurrentAFT.WeightCoordinates
set_option maxHeartbeats 600000

/-- The first coordinate is the most significant digit. -/
def tupleCode (base : ℕ) : (count : ℕ) → (Fin count → ℕ) → ℕ
  | 0, _ => 0
  | count+1, word => base*tupleCode base count (fun index => word index.castSucc)+word (Fin.last count)

def jointCode (base r s : ℕ) (primary : Fin r → ℕ) (body : Fin s → ℕ) : ℕ :=
  base^s*tupleCode base r primary+tupleCode base s body

def arityCode (order r s : ℕ) : ℕ := r*(order+1)+s

theorem tupleCode_lt (base count : ℕ) (_hb : 0 < base) (word : Fin count → ℕ)
    (hw : ∀ index, word index < base) : tupleCode base count word < base^count := by
  induction count with
  | zero => simp only [tupleCode, pow_zero]; omega
  | succ count ih =>
    have ht := ih (fun index => word index.castSucc) (fun index => hw index.castSucc)
    have hl := hw (Fin.last count)
    simp only [tupleCode, pow_succ]
    nlinarith

theorem jointCode_lt (base r s : ℕ) (hb : 0 < base) (primary : Fin r → ℕ) (body : Fin s → ℕ)
    (hp : ∀ index, primary index < base) (hq : ∀ index, body index < base) :
    jointCode base r s primary body < base^(r+s) := by
  have hp' := tupleCode_lt base r hb primary hp
  have hq' := tupleCode_lt base s hb body hq
  have hpower : 0 < base^s := pow_pos hb s
  unfold jointCode
  rw [pow_add]
  nlinarith

theorem jointCode_lt_capacity (base order r s : ℕ) (hb : 0 < base) (hdegree : r+s ≤ order)
    (primary : Fin r → ℕ) (body : Fin s → ℕ)
    (hp : ∀ index, primary index < base) (hq : ∀ index, body index < base) :
    jointCode base r s primary body < base^order :=
  (jointCode_lt base r s hb primary body hp hq).trans_le
    (Nat.pow_le_pow_right hb hdegree)

theorem arityCode_lt (order r s : ℕ) (hr : r ≤ order) (hs : s ≤ order) :
    arityCode order r s < (order+1)^2 := by
  unfold arityCode
  nlinarith

def wordIndex (base order r s : ℕ) (hb : 0 < base) (hdegree : r+s ≤ order)
    (primary : Fin r → Fin base) (body : Fin s → Fin base) : Fin (base^order) :=
  ⟨jointCode base r s (fun index => (primary index).val) (fun index => (body index).val),
    jointCode_lt_capacity base order r s hb hdegree _ _ (fun index => (primary index).isLt) (fun index => (body index).isLt)⟩

def arityIndex (order : ℕ) (r s : Fin (order+1)) : Fin ((order+1)^2) :=
  ⟨arityCode order r.val s.val, arityCode_lt order r.val s.val (Nat.le_of_lt_succ r.isLt) (Nat.le_of_lt_succ s.isLt)⟩

theorem arityCode_injective (order : ℕ) : Function.Injective
    (fun pair : Fin (order+1) × Fin (order+1) => arityIndex order pair.1 pair.2) := by
  rintro ⟨r, s⟩ ⟨r', s'⟩ he
  have h := congrArg Fin.val he
  change r.val*(order+1)+s.val = r'.val*(order+1)+s'.val at h
  have hmod : s.val = s'.val := by
    have hh := congrArg (fun number => number % (order+1)) h
    simpa only [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt s.isLt, Nat.mod_eq_of_lt s'.isLt] using hh
  have hquot : r.val = r'.val := by nlinarith
  exact Prod.ext (Fin.ext hquot) (Fin.ext hmod)

end CurrentAFT.WeightCoordinates
