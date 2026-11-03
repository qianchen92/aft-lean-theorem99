import AFT.BinaryPathInverse

/-! The actual integer rounding-coordinate inverse uses bitwise charge
summation, exact binary long division, signed products and path inversion. -/
namespace AFT.BinaryArithmetic
open RationalRejectionProgram

private def shiftedLoadEntry {size : ℕ} (charge : IntegerBits) (injection load : Vector IntegerBits size)
    (index : Fin size) : CountedValue IntegerBits :=
  let original := readVector IntegerBits.zero load index
  let direction := readVector IntegerBits.zero injection index
  let multiple := IntegerBits.multiply charge direction.value
  let result := IntegerBits.subtract original.value multiple.value
  ⟨result.value,original.work+direction.work+multiple.work+result.work+4⟩

def binaryShiftedLoad {size : ℕ} (charge : IntegerBits) (injection load : Vector IntegerBits size) :
    CountedValue (Vector IntegerBits size) := storeData size (shiftedLoadEntry charge injection load)

theorem binaryShiftedLoad_value {size : ℕ} (charge : IntegerBits) (injection load : Vector IntegerBits size)
    (index : Fin size) :
    ((binaryShiftedLoad charge injection load).value.get index).decode=
      (load.get index).decode-charge.decode*(injection.get index).decode := by
  simp only [binaryShiftedLoad,storeData_get,shiftedLoadEntry,IntegerBits.subtract_value,
    IntegerBits.multiply_value,readVector_value]

theorem binaryShiftedLoad_length {size chargeBits bits : ℕ} (charge : IntegerBits)
    (injection load : Vector IntegerBits size) (hc : charge.digits.length ≤ chargeBits)
    (hi : ∀ index,(injection.get index).digits.length ≤ bits)
    (hl : ∀ index,(load.get index).digits.length ≤ bits) (index : Fin size) :
    ((binaryShiftedLoad charge injection load).value.get index).digits.length ≤ 2*chargeBits+bits+1 := by
  have hm := IntegerBits.multiply_length charge (injection.get index)
  have hs := IntegerBits.subtract_length (load.get index) (IntegerBits.multiply charge (injection.get index)).value
  have hid := hi index
  have hld := hl index
  simp only [binaryShiftedLoad,storeData_get,shiftedLoadEntry,readVector_value]
  omega

def binaryShiftedLoadWork (size chargeBits bits : ℕ) : ℕ :=
  size*(6*size+20*(chargeBits+bits+1)^2+20*(2*chargeBits+bits)+27)+2

theorem binaryShiftedLoad_work {size chargeBits bits : ℕ} (charge : IntegerBits)
    (injection load : Vector IntegerBits size) (hc : charge.digits.length ≤ chargeBits)
    (hi : ∀ index,(injection.get index).digits.length ≤ bits)
    (hl : ∀ index,(load.get index).digits.length ≤ bits) :
    (binaryShiftedLoad charge injection load).work ≤ binaryShiftedLoadWork size chargeBits bits := by
  apply storeData_work
  intro index
  have hr := readVector_work IntegerBits.zero load index
  have hd := readVector_work IntegerBits.zero injection index
  have hil : (readVector IntegerBits.zero injection index).value.digits.length ≤ bits := by rw [readVector_value];exact hi index
  have hll : (readVector IntegerBits.zero load index).value.digits.length ≤ bits := by rw [readVector_value];exact hl index
  have hml := IntegerBits.multiply_length charge (readVector IntegerBits.zero injection index).value
  have wm := IntegerBits.multiply_work charge (readVector IntegerBits.zero injection index).value
  have ws := IntegerBits.subtract_work (readVector IntegerBits.zero load index).value
    (IntegerBits.multiply charge (readVector IntegerBits.zero injection index).value).value
  have wmm : (IntegerBits.multiply charge (readVector IntegerBits.zero injection index).value).work ≤
      20*(chargeBits+bits+1)^2+2 :=
    wm.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left (by omega) 2)) 2)
  have hmax : max (readVector IntegerBits.zero load index).value.digits.length
      (IntegerBits.multiply charge (readVector IntegerBits.zero injection index).value).value.digits.length ≤ 2*chargeBits+bits := by omega
  change (readVector IntegerBits.zero load index).work+(readVector IntegerBits.zero injection index).work+
    (IntegerBits.multiply charge (readVector IntegerBits.zero injection index).value).work+
    (IntegerBits.subtract (readVector IntegerBits.zero load index).value
      (IntegerBits.multiply charge (readVector IntegerBits.zero injection index).value).value).work+4 ≤ _
  omega

structure BinaryCoordinateResult (count : ℕ) where
  edges : Vector IntegerBits count
  charge : IntegerBits
  work : ℕ

def binaryRoundingInverse (count : ℕ) (modulus : List Bool)
    (injection load : Vector IntegerBits (count+1)) : BinaryCoordinateResult count :=
  let total := IntegerBits.sumFin (count+1) (readVector IntegerBits.zero load)
  let charge := IntegerBits.exactQuotient total.value modulus
  let shifted := binaryShiftedLoad charge.value injection load
  let edges := binaryPathInverse count shifted.value
  ⟨edges.value,charge.value,total.work+charge.work+shifted.work+edges.work+4⟩

theorem binaryRoundingInverse_value (count : ℕ) (modulus : List Bool)
    (injection load : Vector IntegerBits (count+1)) (hq : 0 < value modulus)
    (hdiv : (value modulus : ℤ) ∣ ∑ index,(load.get index).decode) :
    (binaryRoundingInverse count modulus injection load).charge.decode=
      (roundingInverseProgram count (value modulus) (injection.map IntegerBits.decode) (load.map IntegerBits.decode)).value.2 ∧
    ∀ index,((binaryRoundingInverse count modulus injection load).edges.get index).decode=
      ((roundingInverseProgram count (value modulus) (injection.map IntegerBits.decode) (load.map IntegerBits.decode)).value.1.get index) := by
  have htotal : (IntegerBits.sumFin (count+1) (readVector IntegerBits.zero load)).value.decode=
      ∑ index,(load.get index).decode := by rw [IntegerBits.sumFin_value];simp only [readVector_value]
  have hc := IntegerBits.exactQuotient_value (IntegerBits.sumFin (count+1) (readVector IntegerBits.zero load)).value
    modulus hq (by rw [htotal];exact hdiv)
  rw [htotal] at hc
  refine ⟨?_,?_⟩
  · simpa only [binaryRoundingInverse,roundingInverseProgram,Vector.get_map] using hc
  · intro index
    simp only [binaryRoundingInverse,binaryPathInverse_value,roundingInverseProgram,Vector.get_map]
    congr 3
    apply Vector.ext
    intro slot hs
    change ((binaryShiftedLoad _ injection load).value.map IntegerBits.decode).get ⟨slot,hs⟩=
      (Vector.ofFn (fun index : Fin (count+1) => (load.get index).decode-
        ((∑ point : Fin (count+1),(load.get point).decode)/(value modulus : ℤ))*(injection.get index).decode)).get ⟨slot,hs⟩
    simp only [Vector.get_map,Vector.get_ofFn,binaryShiftedLoad_value,hc]

def binaryRoundingInverseWork (count modulusBits bits : ℕ) : ℕ :=
  (count+1)*(3*(count+1)+3+20*(count+1+bits)+11)+2+
    (20*(count+1+bits+modulusBits+1)^2+2)+
    binaryShiftedLoadWork (count+1) (count+1+bits) bits+
    binaryPathInverseWork count (2*(count+1+bits)+bits+1)+4

theorem binaryRoundingInverse_work (count bits : ℕ) (modulus : List Bool)
    (injection load : Vector IntegerBits (count+1))
    (hi : ∀ index,(injection.get index).digits.length ≤ bits)
    (hl : ∀ index,(load.get index).digits.length ≤ bits) :
    (binaryRoundingInverse count modulus injection load).work ≤ binaryRoundingInverseWork count modulus.length bits := by
  let total := IntegerBits.sumFin (count+1) (readVector IntegerBits.zero load)
  let charge := IntegerBits.exactQuotient total.value modulus
  let shifted := binaryShiftedLoad charge.value injection load
  have hread (index : Fin (count+1)) : (readVector IntegerBits.zero load index).value.digits.length ≤ bits := by rw [readVector_value];exact hl index
  have ht := IntegerBits.sumFin_length (count+1) bits _ hread
  have hc : charge.value.digits.length ≤ count+1+bits := by rw [IntegerBits.exactQuotient_length];exact ht
  have hs := binaryShiftedLoad_length charge.value injection load hc hi hl
  have wt := IntegerBits.sumFin_work (count+1) bits (3*(count+1)+3) _ hread (readVector_work _ _)
  have wc := IntegerBits.exactQuotient_work total.value modulus
  have wcm : charge.work ≤ 20*(count+1+bits+modulus.length+1)^2+2 :=
    wc.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left (by
      change total.value.digits.length ≤ count+1+bits at ht
      omega) 2)) 2)
  have ws := binaryShiftedLoad_work charge.value injection load hc hi hl
  have we := binaryPathInverse_work count _ shifted.value hs
  change total.work+charge.work+shifted.work+(binaryPathInverse count shifted.value).work+4 ≤ _
  change total.work ≤ _ at wt
  change charge.work ≤ _ at wcm
  change shifted.work ≤ _ at ws
  unfold binaryRoundingInverseWork
  omega

end AFT.BinaryArithmetic
