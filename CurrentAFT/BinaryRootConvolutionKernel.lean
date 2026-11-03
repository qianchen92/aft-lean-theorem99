import CurrentAFT.BinaryPaletteLookup
import CurrentAFT.BinaryBodyProgram

/-! # A root difference acts on a stored profile through an actual binary residue -/
namespace CurrentAFT.BinaryRootConvolutionKernel
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegerBits.residue signedAdd BinaryBodyProgram.shift BinaryPaletteLookup.current

def key (edgeCutoff scalarCutoff : ℕ) (modulus output : List Bool)
    (left right : Fin (2*edgeCutoff+1)) (scalar : Fin (2*scalarCutoff+1)) : Result :=
  let root := BinaryBodyProgram.shift edgeCutoff scalarCutoff false left right scalar
  let difference := signedAdd false (!root.negative) output root.digits
  let residue := IntegerBits.residue ⟨difference.negative, difference.digits⟩ modulus
  ⟨residue.digits, root.work+difference.work+residue.work+3⟩

theorem key_value (edgeCutoff scalarCutoff : ℕ) (modulus output : List Bool)
    (left right : Fin (2*edgeCutoff+1)) (scalar : Fin (2*scalarCutoff+1)) (hq : 0<value modulus) :
    (value (key edgeCutoff scalarCutoff modulus output left right scalar).digits:ℤ) =
      ((value output:ℤ)-((left.val:ℤ)-right.val))%(value modulus:ℤ) := by
  unfold key
  rw [IntegerBits.residue_value _ _ hq]
  rw [IntegerBits.decode, signedAdd_value, signedValue_not, BinaryBodyProgram.shift_value]
  simp only [Bool.false_eq_true, if_false, add_zero, signedValue, sub_eq_add_neg]

def profile {count : ℕ} (table : Vector RationalBits count) (output : ℕ) : ℚ :=
  if h : output<count then (table.get ⟨output,h⟩).decode else 0

def current {count : ℕ} (edgeCutoff scalarCutoff : ℕ) (modulus output : List Bool)
    (table : Vector RationalBits count)
    (left right : Fin (2*edgeCutoff+1)) (scalar : Fin (2*scalarCutoff+1)) : RationalResult :=
  let index := key edgeCutoff scalarCutoff modulus output left right scalar
  let result := BinaryPaletteLookup.current table index.digits
  ⟨result.data, index.work+result.work+2⟩

theorem current_value {count : ℕ} (edgeCutoff scalarCutoff : ℕ) (modulus output : List Bool)
    (table : Vector RationalBits count)
    (left right : Fin (2*edgeCutoff+1)) (scalar : Fin (2*scalarCutoff+1))
    (hq : 0<count) (hmodulus : value modulus=count) :
    (current edgeCutoff scalarCutoff modulus output table left right scalar).data.decode =
      profile table (((value output:ℤ)-((left.val:ℤ)-right.val))%(count:ℤ)).toNat := by
  let index := key edgeCutoff scalarCutoff modulus output left right scalar
  have hv := key_value edgeCutoff scalarCutoff modulus output left right scalar (hmodulus ▸ hq)
  rw [hmodulus] at hv
  have hlt : value index.digits<count := by
    have hx := Int.emod_lt_of_pos ((value output:ℤ)-((left.val:ℤ)-right.val)) (show (0:ℤ)<count by exact_mod_cast hq)
    rw [← hv] at hx
    exact_mod_cast hx
  have hnat : value index.digits = (((value output:ℤ)-((left.val:ℤ)-right.val))%(count:ℤ)).toNat := by
    simpa only [Int.toNat_natCast] using congrArg Int.toNat hv
  change (BinaryPaletteLookup.current table index.digits).data.decode = _
  rw [← hnat, profile, dif_pos hlt]
  exact BinaryPaletteLookup.current_value table index.digits ⟨value index.digits,hlt⟩ rfl

def keyBits (bound : ℕ) := 5*bound+3
def keyWork (bound : ℕ) := BinaryBodyProgram.shiftWork bound+(100*bound+48)+60*(5*bound+4)^2+10+3

theorem key_bounds (edgeCutoff scalarCutoff : ℕ) (modulus output : List Bool)
    (left right : Fin (2*edgeCutoff+1)) (scalar : Fin (2*scalarCutoff+1)) (bound : ℕ)
    (he : edgeCutoff≤bound) (hs : scalarCutoff≤bound) (hm : modulus.length≤bound) (ho : output.length≤bound) :
    (key edgeCutoff scalarCutoff modulus output left right scalar).digits.length ≤ keyBits bound ∧
      (key edgeCutoff scalarCutoff modulus output left right scalar).work ≤ keyWork bound := by
  let root := BinaryBodyProgram.shift edgeCutoff scalarCutoff false left right scalar
  let difference := signedAdd false (!root.negative) output root.digits
  let residue := IntegerBits.residue ⟨difference.negative,difference.digits⟩ modulus
  have hr := BinaryBodyProgram.shift_bounds edgeCutoff scalarCutoff false left right scalar bound he hs
  change root.digits.length≤4*bound+2 ∧ root.work≤BinaryBodyProgram.shiftWork bound at hr
  have hd : difference.digits.length ≤ 4*bound+3 := (signedAdd_length _ _ _ _).trans (by omega)
  have hl : residue.digits.length ≤ 5*bound+3 := (IntegerBits.residue_length _ _).trans (by dsimp only; omega)
  have wd : difference.work ≤ 100*bound+48 := (signedAdd_work _ _ _ _).trans (by omega)
  have wr : residue.work ≤ 60*(5*bound+4)^2+10 := (IntegerBits.residue_work _ _).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 60 (Nat.pow_le_pow_left (by dsimp only; omega) 2)) 10)
  refine ⟨hl, ?_⟩
  change root.work+difference.work+residue.work+3 ≤ _
  unfold keyWork
  omega

def work (count bound bits : ℕ) := keyWork bound+BinaryPaletteLookup.work count (keyBits bound) bits+2

theorem current_bounds {count : ℕ} (edgeCutoff scalarCutoff : ℕ) (modulus output : List Bool)
    (table : Vector RationalBits count)
    (left right : Fin (2*edgeCutoff+1)) (scalar : Fin (2*scalarCutoff+1)) (bound bits : ℕ)
    (he : edgeCutoff≤bound) (hs : scalarCutoff≤bound) (hm : modulus.length≤bound) (ho : output.length≤bound)
    (ht : ∀ color, HeightBound (table.get color).decode bits) :
    HeightBound (current edgeCutoff scalarCutoff modulus output table left right scalar).data.decode (count*(bits+1)) ∧
      (current edgeCutoff scalarCutoff modulus output table left right scalar).work ≤ work count bound bits := by
  have hk := key_bounds edgeCutoff scalarCutoff modulus output left right scalar bound he hs hm ho
  have hl := BinaryPaletteLookup.current_bounds table (key edgeCutoff scalarCutoff modulus output left right scalar).digits
    (keyBits bound) bits hk.1 ht
  exact ⟨hl.1, Nat.add_le_add_right (Nat.add_le_add hk.2 hl.2) 2⟩

end CurrentAFT.BinaryRootConvolutionKernel
