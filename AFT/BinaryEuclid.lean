import AFT.BinaryDivision
import AFT.BinaryNormalization

/-! A binary implementation of Euclid with an explicit linear-in-bitlength
iteration bound. Each iteration performs two long divisions, which halves
the second nonzero operand. -/
namespace AFT.BinaryArithmetic

def remainder (as bs : List Bool) : Result :=
  let division := divide as bs
  let normal := normalize division.remainder
  ⟨normal.digits,division.work+normal.work⟩

theorem remainder_value (as bs : List Bool) (hb : 0 < value bs) :
    value (remainder as bs).digits=value as%value bs := by
  exact (normalize_value _).trans (divide_value as bs hb).2

theorem remainder_normal (as bs : List Bool) :
    (remainder as bs).digits.length=(value (remainder as bs).digits).size := by
  exact (normalize_length _).trans (congrArg Nat.size (normalize_value _)).symm

theorem remainder_length (as bs : List Bool) (hb : 0 < value bs) :
    (remainder as bs).digits.length ≤ bs.length := by
  change (normalize (divide as bs).remainder).digits.length ≤ _
  rw [normalize_length,(divide_value as bs hb).2]
  exact (Nat.size_le_size (Nat.mod_lt _ hb).le).trans (Nat.size_le.mpr (value_lt bs))

theorem remainder_work (as bs : List Bool) :
    (remainder as bs).work ≤ 30*(as.length+bs.length+1)^2 := by
  have hd := divide_work as bs
  have hl := divide_remainder_length as bs
  simp only [remainder,normalize_work]
  nlinarith

def gcdAux : ℕ → List Bool → List Bool → Result
  | 0,as,_ => ⟨as,2⟩
  | fuel+1,as,bs =>
    match bs with
    | [] => ⟨as,2⟩
    | _::_ =>
      let first := remainder as bs
      match first.digits with
      | [] => ⟨bs,first.work+3⟩
      | _::_ =>
        let second := remainder bs first.digits
        let rest := gcdAux fuel first.digits second.digits
        ⟨rest.digits,first.work+second.work+rest.work+4⟩

theorem second_remainder_half {first second : ℕ} (hs : 0 < second) (hlt : second < first) :
    2*(first%second) < first := by
  by_cases hh : 2*second ≤ first
  · have hm := Nat.mod_lt first hs
    omega
  · rw [Nat.mod_eq_sub_mod hlt.le,Nat.mod_eq_of_lt (by omega : first-second < second)]
    omega

/-- Euclid's two-step invariant; the fuel is logarithmic, never an operand
value used as a unary iteration budget. -/
theorem gcdAux_value (fuel : ℕ) (as bs : List Bool)
    (hbn : bs.length=(value bs).size) (hsmall : value bs < 2^fuel) :
    value (gcdAux fuel as bs).digits=Nat.gcd (value as) (value bs) := by
  induction fuel generalizing as bs with
  | zero =>
    have hb : value bs=0 := by simpa using hsmall
    simp [gcdAux,hb]
  | succ fuel ih =>
    cases bs with
    | nil => simp [gcdAux,value]
    | cons b tail =>
      have hb : 0 < value (b::tail) := by
        by_contra hn
        have hz : value (b::tail)=0 := by omega
        simp [hz] at hbn
      have hfirst := remainder_value as (b::tail) hb
      have hfirstn : (remainder as (b::tail)).digits.length=(value (remainder as (b::tail)).digits).size := by
        exact (normalize_length _).trans (congrArg Nat.size (normalize_value _)).symm
      simp only [gcdAux]
      split <;> rename_i he
      · have hz : value as%value (b::tail)=0 := by rw [he,value] at hfirst;omega
        rw [Nat.gcd_comm,Nat.gcd_rec,hz,Nat.gcd_zero_left]
      · have hf : 0 < value (remainder as (b::tail)).digits := by
          by_contra hn
          have hz : value (remainder as (b::tail)).digits=0 := by omega
          rw [hz,Nat.size_zero,he] at hfirstn
          simp at hfirstn
        have hsecond := remainder_value (b::tail) (remainder as (b::tail)).digits hf
        have hn : (remainder (b::tail) (remainder as (b::tail)).digits).digits.length=
            (value (remainder (b::tail) (remainder as (b::tail)).digits).digits).size := by
          exact (normalize_length _).trans (congrArg Nat.size (normalize_value _)).symm
        have hhalf := second_remainder_half hf (by rw [hfirst];exact Nat.mod_lt _ hb)
        have hbound : value (remainder (b::tail) (remainder as (b::tail)).digits).digits < 2^fuel := by
          rw [hsecond]
          rw [pow_succ] at hsmall
          omega
        have hi := ih (remainder as (b::tail)).digits (remainder (b::tail) (remainder as (b::tail)).digits).digits hn hbound
        rw [hi,hfirst,hsecond,hfirst]
        calc
          _ = Nat.gcd (value (b::tail)%(value as%value (b::tail))) (value as%value (b::tail)) := Nat.gcd_comm ..
          _ = Nat.gcd (value as%value (b::tail)) (value (b::tail)) := (Nat.gcd_rec _ _).symm
          _ = Nat.gcd (value (b::tail)) (value as) := (Nat.gcd_rec _ _).symm
          _ = _ := Nat.gcd_comm ..

theorem gcdAux_resources (fuel : ℕ) (as bs : List Bool)
    (hbn : bs.length=(value bs).size) (bound : ℕ)
    (ha : as.length ≤ bound) (hb : bs.length ≤ bound) :
    (gcdAux fuel as bs).digits.length ≤ bound ∧
      (gcdAux fuel as bs).work ≤ fuel*(300*(bound+1)^2)+2 := by
  induction fuel generalizing as bs with
  | zero => simpa only [gcdAux,Nat.zero_mul,Nat.zero_add,le_refl,and_true] using ha
  | succ fuel ih =>
    cases bs with
    | nil => simp only [gcdAux];constructor;exact ha;omega
    | cons b tail =>
      have hbpos : 0 < value (b::tail) := by
        by_contra hn
        have hz : value (b::tail)=0 := by omega
        simp [hz] at hbn
      have hfl := remainder_length as (b::tail) hbpos
      have hfw := remainder_work as (b::tail)
      have hfw' : (remainder as (b::tail)).work ≤ 120*(bound+1)^2 := by
        have hm : as.length+(b::tail).length+1 ≤ 2*(bound+1) := by omega
        nlinarith [Nat.pow_le_pow_left hm 2]
      simp only [gcdAux]
      split <;> rename_i he
      · constructor;exact hb
        have hone : 1 ≤ (bound+1)^2 := Nat.one_le_pow _ _ (by omega)
        nlinarith
      · have hfpos : 0 < value (remainder as (b::tail)).digits := by
          have hfn := remainder_normal as (b::tail)
          by_contra hn
          have hz : value (remainder as (b::tail)).digits=0 := by omega
          rw [hz,Nat.size_zero,he] at hfn
          simp at hfn
        have hsl := remainder_length (b::tail) (remainder as (b::tail)).digits hfpos
        have hsw := remainder_work (b::tail) (remainder as (b::tail)).digits
        have hsw' : (remainder (b::tail) (remainder as (b::tail)).digits).work ≤ 120*(bound+1)^2 := by
          have hm : (b::tail).length+(remainder as (b::tail)).digits.length+1 ≤ 2*(bound+1) := by omega
          nlinarith [Nat.pow_le_pow_left hm 2]
        have hr := ih (remainder as (b::tail)).digits
          (remainder (b::tail) (remainder as (b::tail)).digits).digits
          (remainder_normal _ _) (hfl.trans hb) (hsl.trans (hfl.trans hb))
        constructor
        · exact hr.1
        · have hone : 1 ≤ (bound+1)^2 := Nat.one_le_pow _ _ (by omega)
          nlinarith [hr.2]

/-- This code uses the input-list length as its logarithmic fuel bound. -/
def gcd (as bs : List Bool) : Result :=
  let na := normalize as
  let nb := normalize bs
  let result := gcdAux (bs.length+1) na.digits nb.digits
  ⟨result.digits,na.work+nb.work+result.work+bs.length+1⟩

theorem gcd_value (as bs : List Bool) : value (gcd as bs).digits=Nat.gcd (value as) (value bs) := by
  have hn : (normalize bs).digits.length=(value (normalize bs).digits).size := by
    rw [normalize_length,normalize_value]
  have hv : value (normalize bs).digits < 2^(bs.length+1) := by
    rw [normalize_value]
    exact (value_lt bs).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  simpa only [gcd,normalize_value] using gcdAux_value (bs.length+1) (normalize as).digits (normalize bs).digits hn hv

theorem gcd_resources (as bs : List Bool) :
    (gcd as bs).digits.length ≤ max as.length bs.length ∧
      (gcd as bs).work ≤ 1000*(as.length+bs.length+1)^3 := by
  have hn : (normalize bs).digits.length=(value (normalize bs).digits).size := by
    rw [normalize_length,normalize_value]
  have hr := gcdAux_resources (bs.length+1) (normalize as).digits (normalize bs).digits hn
    (as.length+bs.length) ((normalize_length_le as).trans (by omega)) ((normalize_length_le bs).trans (by omega))
  have hl := gcdAux_resources (bs.length+1) (normalize as).digits (normalize bs).digits hn
    (max as.length bs.length) ((normalize_length_le as).trans (Nat.le_max_left ..))
    ((normalize_length_le bs).trans (Nat.le_max_right ..))
  constructor
  · exact hl.1
  · simp only [gcd,normalize_work]
    have hh := hr.2
    have hone : 1 ≤ as.length+bs.length+1 := by omega
    nlinarith [Nat.mul_le_mul_right (300*(as.length+bs.length+1)^2) (show bs.length+1 ≤ as.length+bs.length+1 by omega)]

end AFT.BinaryArithmetic
