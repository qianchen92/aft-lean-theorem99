import AFT.BinaryAffineAssembly

/-! Literal natural-coefficient resource polynomials for the full binary
matrix-and-offset algorithm, parameterized by dimensions and operand lengths. -/
namespace AFT.BinaryArithmetic
open Polynomial

 noncomputable def binaryShiftedLoadPolynomial (size chargeBits bits : Polynomial ℕ) : Polynomial ℕ :=
   size*(6*size+20*(chargeBits+bits+1)^2+20*(2*chargeBits+bits)+27)+2

 theorem binaryShiftedLoadPolynomial_eval (size chargeBits bits : Polynomial ℕ) (n : ℕ) :
     (binaryShiftedLoadPolynomial size chargeBits bits).eval n=
       binaryShiftedLoadWork (size.eval n) (chargeBits.eval n) (bits.eval n) := by
   simp only [binaryShiftedLoadPolynomial,binaryShiftedLoadWork,eval_add,eval_mul,eval_pow,eval_ofNat,eval_one]

 noncomputable def binaryPathInversePolynomial (count bits : Polynomial ℕ) : Polynomial ℕ :=
   count*(100*(count+bits+3)^2)+2

 theorem binaryPathInversePolynomial_eval (count bits : Polynomial ℕ) (n : ℕ) :
     (binaryPathInversePolynomial count bits).eval n=binaryPathInverseWork (count.eval n) (bits.eval n) := by
   simp only [binaryPathInversePolynomial,binaryPathInverseWork,eval_add,eval_mul,eval_pow,eval_ofNat]

 noncomputable def binaryRoundingInversePolynomial (count modulusBits bits : Polynomial ℕ) : Polynomial ℕ :=
   (count+1)*(3*(count+1)+3+20*(count+1+bits)+11)+2+
     (20*(count+1+bits+modulusBits+1)^2+2)+
     binaryShiftedLoadPolynomial (count+1) (count+1+bits) bits+
     binaryPathInversePolynomial count (2*(count+1+bits)+bits+1)+4

 theorem binaryRoundingInversePolynomial_eval (count modulusBits bits : Polynomial ℕ) (n : ℕ) :
     (binaryRoundingInversePolynomial count modulusBits bits).eval n=
       binaryRoundingInverseWork (count.eval n) (modulusBits.eval n) (bits.eval n) := by
   simp only [binaryRoundingInversePolynomial,binaryRoundingInverseWork,eval_add,eval_mul,eval_pow,eval_ofNat,eval_one,
     binaryShiftedLoadPolynomial_eval,binaryPathInversePolynomial_eval]

 noncomputable def binaryPaddedEntryPolynomial (count bits : Polynomial ℕ) : Polynomial ℕ :=
   6*(count+1)+(count+1)*(9*(count+1)+20*(2*bits+1)^2+20*(count+1+3*bits)+27)+20*(count+1+3*bits)+21

 theorem binaryPaddedEntryPolynomial_eval (count bits : Polynomial ℕ) (n : ℕ) :
     (binaryPaddedEntryPolynomial count bits).eval n=binaryPaddedEntryWork (count.eval n) (bits.eval n) := by
   simp only [binaryPaddedEntryPolynomial,binaryPaddedEntryWork,eval_add,eval_mul,eval_pow,eval_ofNat,eval_one]

 noncomputable def binaryAffineAssemblyPolynomial (count modulusBits bits : Polynomial ℕ) : Polynomial ℕ :=
   (count+1)*((count+1)*(9*(count+1)+15)+2+binaryRoundingInversePolynomial count modulusBits bits+4)+2+
     ((count+1)*(binaryPaddedEntryPolynomial count bits+2)+2)+
     binaryRoundingInversePolynomial count modulusBits (count+3*bits+2)+3

 theorem binaryAffineAssemblyPolynomial_eval (count modulusBits bits : Polynomial ℕ) (n : ℕ) :
     (binaryAffineAssemblyPolynomial count modulusBits bits).eval n=
       binaryAffineAssemblyWork (count.eval n) (modulusBits.eval n) (bits.eval n) := by
   simp only [binaryAffineAssemblyPolynomial,binaryAffineAssemblyWork,eval_add,eval_mul,eval_ofNat,eval_one,
     binaryRoundingInversePolynomial_eval,binaryPaddedEntryPolynomial_eval]

 theorem binaryShiftedLoadWork_mono {s t a b c d : ℕ} (hs : s≤t) (hab : a≤b) (hcd : c≤d) :
     binaryShiftedLoadWork s a c≤binaryShiftedLoadWork t b d := by
   unfold binaryShiftedLoadWork
   gcongr

 theorem binaryPathInverseWork_mono {s t a b : ℕ} (hs : s≤t) (hab : a≤b) :
     binaryPathInverseWork s a≤binaryPathInverseWork t b := by
   unfold binaryPathInverseWork
   gcongr

 theorem binaryRoundingInverseWork_mono {s t a b c d : ℕ} (hs : s≤t) (hab : a≤b) (hcd : c≤d) :
     binaryRoundingInverseWork s a c≤binaryRoundingInverseWork t b d := by
   unfold binaryRoundingInverseWork binaryShiftedLoadWork binaryPathInverseWork
   gcongr

 theorem binaryPaddedEntryWork_mono {s t a b : ℕ} (hs : s≤t) (hab : a≤b) :
     binaryPaddedEntryWork s a≤binaryPaddedEntryWork t b := by
   unfold binaryPaddedEntryWork
   gcongr

 theorem binaryAffineAssemblyWork_mono {s t a b c d : ℕ} (hs : s≤t) (hab : a≤b) (hcd : c≤d) :
     binaryAffineAssemblyWork s a c≤binaryAffineAssemblyWork t b d := by
   unfold binaryAffineAssemblyWork binaryRoundingInverseWork binaryShiftedLoadWork binaryPathInverseWork binaryPaddedEntryWork
   gcongr

 theorem binaryAffineAssembly_polynomial_work (n count : ℕ) (modulus : List Bool)
     (injection : Vector IntegerBits (count+1))
     (matrix : Vector (Vector IntegerBits (count+1)) (count+1))
     (initial padding : Vector IntegerBits (count+1))
     (permutation : Vector (Fin (count+1)) (count+1)) (countBound modulusBound bitsBound : Polynomial ℕ)
     (hn : count≤countBound.eval n) (hq : modulus.length≤ modulusBound.eval n)
     (hinjection : ∀ row,(injection.get row).digits.length≤bitsBound.eval n)
     (hm : ∀ column row,((matrix.get column).get row).digits.length≤bitsBound.eval n)
     (hi : ∀ row,(initial.get row).digits.length≤bitsBound.eval n)
     (hp : ∀ column,(padding.get column).digits.length≤bitsBound.eval n) :
     (binaryAffineAssembly count modulus injection matrix initial padding permutation).work≤
       (binaryAffineAssemblyPolynomial countBound modulusBound bitsBound).eval n := by
   rw [binaryAffineAssemblyPolynomial_eval]
   exact (binaryAffineAssembly_work count _ modulus injection matrix initial padding permutation hinjection hm hi hp).trans
     (binaryAffineAssemblyWork_mono hn hq le_rfl)

end AFT.BinaryArithmetic
