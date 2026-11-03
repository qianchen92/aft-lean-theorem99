import AFT.BinaryProtectedFeature

/-! Polynomial bit and unary-control costs of actual protected features.
All address values are polynomially bounded in the actual chart instance. -/
namespace AFT.BinaryArithmetic

 def modularDifferenceWork (address cutoff modulus : ℕ) : ℕ :=
   500*(cutoff+modulus+2)^2+2*modulus+2*address+6+
     500*(address+2*modulus+2)^2

 theorem modularDifference_work (address cutoff modulus : ℕ) (hm : 0 < modulus) :
     (modularDifference address cutoff modulus).work ≤ modularDifferenceWork address cutoff modulus := by
   have hfirst := divideCounter_work cutoff modulus hm
   have hoff := differenceCounter_work modulus (divideCounter cutoff modulus).remainder
   have hvalue : (differenceCounter modulus (divideCounter cutoff modulus).remainder).count≤ modulus := by
     rw [differenceCounter_value];omega
   have hshift := addCounter_work address (differenceCounter modulus (divideCounter cutoff modulus).remainder).count
   have hfinal := divideCounter_work (addCounter address (differenceCounter modulus (divideCounter cutoff modulus).remainder).count).count modulus hm
   have hb : (addCounter address (differenceCounter modulus (divideCounter cutoff modulus).remainder).count).count+modulus+2≤ address+2*modulus+2 := by
     rw [addCounter_value];omega
   have hfinal' := hfinal.trans (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left hb 2))
   dsimp only [modularDifference,modularDifferenceWork]
   omega

 def protectedFeatureWork (cutoff modulus input chart : ℕ) : ℕ :=
   3*cutoff+1+500*(input+(2*cutoff+1)+2)^2+
   (modulus*(2*modulus+3)+1)+500*(chart+modulus*modulus+2)^2+
   500*(modulus*modulus+modulus+2)^2+
   modularDifferenceWork input cutoff modulus+modularDifferenceWork (2*cutoff+1) cutoff modulus+
   (modulus*modulus*(2*modulus+3)+1)+(modulus*(2*modulus+3)+1)+
   (2*chart+1)+(2*(chart+modulus*modulus*modulus)+1)+
   500*(chart+modulus*modulus*modulus+modulus*modulus+modulus+2)^2+13

 theorem protectedFeatureAddress_work (cutoff modulus input chart : ℕ) (hm : 0 < modulus) :
     (protectedFeatureAddress cutoff modulus input chart).work ≤ protectedFeatureWork cutoff modulus input chart := by
   let width := (doubleCounter cutoff).count.succ
   let source := divideCounter input width
   let square := multiplyCounter modulus modulus
   let outer := divideCounter chart square.count
   let inner := divideCounter outer.remainder modulus
   let first := modularDifference source.quotient cutoff modulus
   let second := modularDifference source.remainder cutoff modulus
   let firstProduct := multiplyCounter inner.quotient first.count
   let secondProduct := multiplyCounter inner.remainder second.count
   let prefixSum := addCounter outer.quotient firstProduct.count
   let total := addCounter prefixSum.count secondProduct.count
   have hwidth : width=2*cutoff+1 := by simp [width,doubleCounter_value]
   have hwidthpos : 0< width := by omega
   have hsquare : square.count=modulus*modulus := multiplyCounter_value _ _
   have hsquarepos : 0< square.count := by rw [hsquare];exact Nat.mul_pos hm hm
   have hsourceq : source.quotient≤ input := by
     dsimp only [source];rw [(divideCounter_value _ _ hwidthpos).1];exact Nat.div_le_self _ _
   have hsourcer : source.remainder≤2*cutoff+1 := by
     dsimp only [source];rw [(divideCounter_value _ _ hwidthpos).2,←hwidth];exact Nat.le_of_lt (Nat.mod_lt _ hwidthpos)
   have houterq : outer.quotient≤ chart := by
     dsimp only [outer];rw [(divideCounter_value _ _ hsquarepos).1];exact Nat.div_le_self _ _
   have houterr : outer.remainder≤ modulus*modulus := by
     dsimp only [outer];rw [(divideCounter_value _ _ hsquarepos).2,←hsquare];exact Nat.le_of_lt (Nat.mod_lt _ hsquarepos)
   have hinnerq : inner.quotient≤ modulus*modulus := by
     dsimp only [inner];rw [(divideCounter_value _ _ hm).1];exact (Nat.div_le_self _ _).trans houterr
   have hinnerr : inner.remainder≤ modulus := by
     dsimp only [inner];rw [(divideCounter_value _ _ hm).2];exact Nat.le_of_lt (Nat.mod_lt _ hm)
   have hfirst : first.count≤ modulus := (modularDifference_lt _ _ _ hm).le
   have hsecond : second.count≤ modulus := (modularDifference_lt _ _ _ hm).le
   have hfp : firstProduct.count≤ modulus*modulus*modulus := by
     dsimp only [firstProduct];rw [multiplyCounter_value];exact Nat.mul_le_mul hinnerq hfirst
   have hsp : secondProduct.count≤ modulus*modulus := by
     dsimp only [secondProduct];rw [multiplyCounter_value];exact Nat.mul_le_mul hinnerr hsecond
   have hprefix : prefixSum.count≤ chart+modulus*modulus*modulus := by
     dsimp only [prefixSum];rw [addCounter_value];omega
   have htotal : total.count≤ chart+modulus*modulus*modulus+modulus*modulus := by
     dsimp only [total];rw [addCounter_value];omega
   have hsourcework : source.work≤500*(input+(2*cutoff+1)+2)^2 := by
     dsimp only [source];simpa only [hwidth] using divideCounter_work input width hwidthpos
   have houterwork : outer.work≤500*(chart+modulus*modulus+2)^2 := by
     dsimp only [outer];simpa only [hsquare] using divideCounter_work chart square.count hsquarepos
   have hinnerwork : inner.work≤500*(modulus*modulus+modulus+2)^2 := by
     apply (divideCounter_work outer.remainder modulus hm).trans
     gcongr
   have hfirstwork : first.work≤ modularDifferenceWork input cutoff modulus := by
     apply (modularDifference_work source.quotient cutoff modulus hm).trans
     unfold modularDifferenceWork;gcongr
   have hsecondwork : second.work≤ modularDifferenceWork (2*cutoff+1) cutoff modulus := by
     apply (modularDifference_work source.remainder cutoff modulus hm).trans
     unfold modularDifferenceWork;gcongr
   have hfpwork : firstProduct.work≤ modulus*modulus*(2*modulus+3)+1 := by
     dsimp only [firstProduct];rw [multiplyCounter_work];gcongr
   have hspwork : secondProduct.work≤ modulus*(2*modulus+3)+1 := by
     dsimp only [secondProduct];rw [multiplyCounter_work];gcongr
   have hpwork : prefixSum.work≤2*chart+1 := by
     dsimp only [prefixSum];rw [addCounter_work];omega
   have htwork : total.work≤2*(chart+modulus*modulus*modulus)+1 := by
     dsimp only [total];rw [addCounter_work];omega
   have hresult := (divideCounter_work total.count modulus hm).trans
     (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (show total.count+modulus+2≤ chart+modulus*modulus*modulus+modulus*modulus+modulus+2 by omega) 2))
   change (doubleCounter cutoff).work+source.work+square.work+outer.work+inner.work+first.work+second.work+
     firstProduct.work+secondProduct.work+prefixSum.work+total.work+(divideCounter total.count modulus).work+13≤_
   have hsquarework : square.work=modulus*(2*modulus+3)+1 := multiplyCounter_work _ _
   rw [doubleCounter_work,hsquarework]
   unfold protectedFeatureWork
   omega

end AFT.BinaryArithmetic
