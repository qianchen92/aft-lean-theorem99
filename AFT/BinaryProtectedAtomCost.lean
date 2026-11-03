import AFT.BinaryProtectedParameters

/-! The actual rational atom coefficient, with binary work and height. -/
namespace AFT.BinaryArithmetic
open AFT.RationalNumerics

 def protectedAtomHeight (cutoff : ℕ) : ℕ := 100*((2*cutoff+1)*(2*cutoff+1))
 def protectedAtomWork (cutoff : ℕ) : ℕ :=
   3*cutoff+1+(2*cutoff+1)*(2*(2*cutoff+1)+3)+1+
     100*(2*((2*cutoff+1)*(2*cutoff+1))+3)+1+
     60*(protectedAtomHeight cutoff+1)^2+2*RationalBits.primitiveWorkBound (protectedAtomHeight cutoff)+7

 theorem protectedAtom_height (cutoff : ℕ) : HeightBound (protectedAtom cutoff).data.decode (protectedAtomHeight cutoff) := by
   rw [protectedAtom_value]
   unfold BoundaryCalibration.finiteProtectedAtom
   have h := (HeightBound.nat_coarse (100*((2*cutoff+1)*(2*cutoff+1)))).inv
   simpa only [protectedAtomHeight,Nat.cast_mul,Nat.cast_ofNat,div_eq_mul_inv,one_mul] using h

 theorem protectedAtom_work (cutoff : ℕ) : (protectedAtom cutoff).work≤protectedAtomWork cutoff := by
   let features := multiplyCounter (doubleCounter cutoff).count.succ (doubleCounter cutoff).count.succ
   let denominator := multiplyCounter 100 features.count
   have hv : denominator.count=protectedAtomHeight cutoff := by
     simp only [denominator,features,multiplyCounter_value,doubleCounter_value,protectedAtomHeight,Nat.succ_eq_add_one]
   have hc := RationalBits.ofCounter_work denominator.count
   have hh : HeightBound (RationalBits.ofCounter denominator.count).data.decode (protectedAtomHeight cutoff) := by
     rw [RationalBits.ofCounter_value,←hv];exact HeightBound.nat_coarse _
   have hq := RationalBits.quotient_work RationalBits.one (RationalBits.ofCounter denominator.count).data
     (protectedAtomHeight cutoff) (by rw [RationalBits.one_value];exact HeightBound.one.mono (Nat.zero_le _)) hh
   dsimp only [protectedAtom]
   change (doubleCounter cutoff).work+features.work+denominator.work+(RationalBits.ofCounter denominator.count).work+
     (RationalBits.quotient RationalBits.one (RationalBits.ofCounter denominator.count).data).work+5≤_
   have hf : features.work=(2*cutoff+1)*(2*(2*cutoff+1)+3)+1 := by
     simp only [features,multiplyCounter_work,doubleCounter_value,Nat.succ_eq_add_one]
   have hd : denominator.work=100*(2*((2*cutoff+1)*(2*cutoff+1))+3)+1 := by
     simp only [denominator,features,multiplyCounter_work,multiplyCounter_value,doubleCounter_value,Nat.succ_eq_add_one]
   rw [doubleCounter_work,hf,hd]
   have hc' : (RationalBits.ofCounter denominator.count).work ≤ 60*(protectedAtomHeight cutoff+1)^2 := by
     calc
       _ ≤ 60*(denominator.count+1)^2 := hc
       _ = _ := by rw [hv]
   unfold protectedAtomWork
   omega

end AFT.BinaryArithmetic
