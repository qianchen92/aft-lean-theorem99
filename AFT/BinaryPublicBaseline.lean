import AFT.BinaryBoundaryHalf
import AFT.ActualPublicOffsetProgram

/-! Public baseline formation retaining all signed source digits. -/
namespace AFT.BinaryArithmetic
open AFT.V7Calibration

def binaryBaselineStart (modulus width color : ℕ) (coin : Bool) : SignedResult :=
  let twiceColor := doubleCounter color
  let last := differenceCounter modulus 1
  let lower := lessCounter twiceColor.count last.count
  let upper := lessCounter last.count twiceColor.count
  let twiceWidth := doubleCounter width
  let positive := canonicalCounter width
  let negative := canonicalCounter twiceWidth.count
  let shifted := signedAdd true false negative.digits [true]
  let pickLower := lower.value || (!upper.value && coin)
  ⟨if pickLower then shifted.negative else false,
    if pickLower then shifted.digits else positive.digits,
    twiceColor.work+last.work+lower.work+upper.work+twiceWidth.work+
      positive.work+negative.work+shifted.work+10⟩

theorem binaryBaselineStart_value (modulus width color : ℕ) (coin : Bool) :
    signedValue (binaryBaselineStart modulus width color coin).negative
      (binaryBaselineStart modulus width color coin).digits=
      publicAnchorStartProgram modulus width color coin+(color : ℤ)-((modulus : ℤ)-1) := by
  have hn : signedValue (signedAdd true false (canonicalCounter (2*width)).digits [true]).negative
      (signedAdd true false (canonicalCounter (2*width)).digits [true]).digits=1-2*(width : ℤ) := by
    rw [signedAdd_value]
    simp [signedValue,canonicalCounter_value,value]
    ring
  have hp : signedValue false (canonicalCounter width).digits=(width : ℤ) := by
    simp [signedValue,canonicalCounter_value]
  by_cases hlow : 2*color < modulus-1
  · have hl : (lessCounter (2*color) (modulus-1)).value=true := (lessCounter_value _ _).mpr hlow
    simp only [binaryBaselineStart,doubleCounter_value,differenceCounter_value,hl,Bool.true_or,
      ↓reduceIte,hn,publicAnchorStartProgram,if_pos hlow]
    omega
  · have hl : (lessCounter (2*color) (modulus-1)).value=false := by
      apply Bool.eq_false_iff.mpr
      exact fun h => hlow ((lessCounter_value _ _).mp h)
    by_cases hupp : modulus-1 < 2*color
    · have hu : (lessCounter (modulus-1) (2*color)).value=true := (lessCounter_value _ _).mpr hupp
      simp [binaryBaselineStart,doubleCounter_value,differenceCounter_value,hl,hu,hp,
        publicAnchorStartProgram,hlow,hupp]
      ring
    · have hu : (lessCounter (modulus-1) (2*color)).value=false := by
        apply Bool.eq_false_iff.mpr
        exact fun h => hupp ((lessCounter_value _ _).mp h)
      cases coin <;> simp [binaryBaselineStart,doubleCounter_value,differenceCounter_value,hl,hu,
        hp,hn,publicAnchorStartProgram,hlow,hupp] <;> omega

def binaryPublicBaseline (modulus width color : ℕ) (coin : Bool)
    (rootSign legSign queueSign : Bool) (root leg queue : List Bool) : SignedResult :=
  let start := binaryBaselineStart modulus width color coin
  let first := signedAdd rootSign legSign root leg
  let body := signedAdd first.negative queueSign first.digits queue
  let result := signedAdd start.negative body.negative start.digits body.digits
  ⟨result.negative,result.digits,start.work+first.work+body.work+result.work+4⟩

theorem binaryPublicBaseline_value (modulus width color : ℕ) (coin : Bool)
    (rootSign legSign queueSign : Bool) (root leg queue : List Bool) :
    signedValue (binaryPublicBaseline modulus width color coin rootSign legSign queueSign root leg queue).negative
      (binaryPublicBaseline modulus width color coin rootSign legSign queueSign root leg queue).digits=
      publicAnchorStartProgram modulus width color coin+(color : ℤ)-((modulus : ℤ)-1)+
        (signedValue rootSign root+signedValue legSign leg+signedValue queueSign queue) := by
  simp only [binaryPublicBaseline,signedAdd_value,binaryBaselineStart_value]

def binaryBaselineStartWork (modulus width color : ℕ) : ℕ :=
  1000*(modulus+width+color+2)^2

theorem binaryBaselineStart_length (modulus width color : ℕ) (coin : Bool) :
    (binaryBaselineStart modulus width color coin).digits.length ≤ 2*width+2 := by
  have h := signedAdd_length true false (canonicalCounter (2*width)).digits [true]
  have hsize (count : ℕ) : count.size ≤ count := Nat.size_le.mpr (Nat.lt_two_pow_self (n:=count))
  simp only [canonicalCounter_length,List.length_cons,List.length_nil] at h
  have hp := hsize width
  have hn := hsize (2*width)
  have hneg : (signedAdd true false (canonicalCounter (2*width)).digits [true]).digits.length ≤ 2*width+2 := by omega
  have hpos : (canonicalCounter width).digits.length ≤ 2*width+2 := by rw [canonicalCounter_length];omega
  unfold binaryBaselineStart
  simp only [doubleCounter_value]
  split_ifs
  · exact hneg
  · exact hpos

theorem binaryBaselineStart_work (modulus width color : ℕ) (coin : Bool) :
    (binaryBaselineStart modulus width color coin).work ≤ binaryBaselineStartWork modulus width color := by
  have hl := differenceCounter_work modulus 1
  have hlower := lessCounter_work (2*color) (modulus-1)
  have hupper := lessCounter_work (modulus-1) (2*color)
  have hp := canonicalCounter_work width
  have hn := canonicalCounter_work (2*width)
  have hs := signedAdd_work true false (canonicalCounter (2*width)).digits [true]
  have hsize := Nat.size_le.mpr (Nat.lt_two_pow_self (n:=2*width))
  simp only [canonicalCounter_length,List.length_cons,List.length_nil] at hs
  have hmax : max (2*width).size 1 ≤ 2*width+1 := by omega
  have hs' := hs.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 20 hmax) 8)
  unfold binaryBaselineStart binaryBaselineStartWork
  simp only [doubleCounter_value,doubleCounter_work,differenceCounter_value]
  have hsub := Nat.sub_le modulus 1
  nlinarith

def binaryPublicBaselineWork (modulus width color rootBits legBits queueBits : ℕ) : ℕ :=
  binaryBaselineStartWork modulus width color+200*(width+rootBits+legBits+queueBits+3)+100

theorem binaryPublicBaseline_length (modulus width color : ℕ) (coin : Bool)
    (rootSign legSign queueSign : Bool) (root leg queue : List Bool) :
    (binaryPublicBaseline modulus width color coin rootSign legSign queueSign root leg queue).digits.length ≤
      2*width+root.length+leg.length+queue.length+5 := by
  have hs := binaryBaselineStart_length modulus width color coin
  have h1 := signedAdd_length rootSign legSign root leg
  have h2 := signedAdd_length (signedAdd rootSign legSign root leg).negative queueSign
    (signedAdd rootSign legSign root leg).digits queue
  have h3 := signedAdd_length (binaryBaselineStart modulus width color coin).negative
    (signedAdd (signedAdd rootSign legSign root leg).negative queueSign (signedAdd rootSign legSign root leg).digits queue).negative
    (binaryBaselineStart modulus width color coin).digits
    (signedAdd (signedAdd rootSign legSign root leg).negative queueSign (signedAdd rootSign legSign root leg).digits queue).digits
  unfold binaryPublicBaseline
  dsimp only
  omega

theorem binaryPublicBaseline_work (modulus width color : ℕ) (coin : Bool)
    (rootSign legSign queueSign : Bool) (root leg queue : List Bool) :
    (binaryPublicBaseline modulus width color coin rootSign legSign queueSign root leg queue).work ≤
      binaryPublicBaselineWork modulus width color root.length leg.length queue.length := by
  have hs := binaryBaselineStart_work modulus width color coin
  have hsl := binaryBaselineStart_length modulus width color coin
  have h1 := signedAdd_work rootSign legSign root leg
  have hl1 := signedAdd_length rootSign legSign root leg
  have h2 := signedAdd_work (signedAdd rootSign legSign root leg).negative queueSign
    (signedAdd rootSign legSign root leg).digits queue
  have hl2 := signedAdd_length (signedAdd rootSign legSign root leg).negative queueSign
    (signedAdd rootSign legSign root leg).digits queue
  have h3 := signedAdd_work (binaryBaselineStart modulus width color coin).negative
    (signedAdd (signedAdd rootSign legSign root leg).negative queueSign (signedAdd rootSign legSign root leg).digits queue).negative
    (binaryBaselineStart modulus width color coin).digits
    (signedAdd (signedAdd rootSign legSign root leg).negative queueSign (signedAdd rootSign legSign root leg).digits queue).digits
  unfold binaryPublicBaseline binaryPublicBaselineWork
  dsimp only
  omega

end AFT.BinaryArithmetic
