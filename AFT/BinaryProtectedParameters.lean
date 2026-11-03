import AFT.BinaryProtectedScale
import AFT.BinaryFiniteArithmetic

/-! Explicit loop dimensions, marked address and rational spike coefficient. -/
namespace AFT.BinaryArithmetic
open AFT.BoundaryCalibration AFT.RationalRejectionProgram

 structure ProtectedDimensions where
   charts : ℕ
   features : ℕ
   work : ℕ

 def protectedDimensions (cutoff modulus : ℕ) : ProtectedDimensions :=
   let doubled := doubleCounter cutoff
   let features := multiplyCounter doubled.count.succ doubled.count.succ
   let square := multiplyCounter modulus modulus
   let charts := multiplyCounter modulus square.count
   ⟨charts.count,features.count,doubled.work+features.work+square.work+charts.work+5⟩

 theorem protectedDimensions_values (cutoff modulus : ℕ) :
     (protectedDimensions cutoff modulus).charts=modulus*(modulus*modulus) ∧
       (protectedDimensions cutoff modulus).features=(2*cutoff+1)*(2*cutoff+1) := by
   simp [protectedDimensions,doubleCounter_value,multiplyCounter_value,Nat.succ_eq_add_one]

 def protectedDimensionsWork (cutoff modulus : ℕ) : ℕ :=
   3*cutoff+1+(2*cutoff+1)*(2*(2*cutoff+1)+3)+1+
     modulus*(2*modulus+3)+1+modulus*(2*(modulus*modulus)+3)+1+5

 theorem protectedDimensions_work (cutoff modulus : ℕ) :
     (protectedDimensions cutoff modulus).work=protectedDimensionsWork cutoff modulus := by
   simp only [protectedDimensions,protectedDimensionsWork,doubleCounter_work,doubleCounter_value,
     multiplyCounter_work,multiplyCounter_value,Nat.succ_eq_add_one];ring

 def protectedMarkAddress (cutoff : ℕ) : UnaryCounterResult :=
   let doubled := doubleCounter cutoff
   let product := multiplyCounter doubled.count.succ cutoff
   let total := addCounter cutoff product.count
   ⟨total.count,doubled.work+product.work+total.work+4⟩

 theorem protectedMarkAddress_value (cutoff : ℕ) :
     (protectedMarkAddress cutoff).count=cutoff+(2*cutoff+1)*cutoff := by
   simp only [protectedMarkAddress,addCounter_value,multiplyCounter_value,doubleCounter_value]

 theorem protectedMarkAddress_lt (cutoff : ℕ) :
     (protectedMarkAddress cutoff).count<(2*cutoff+1)*(2*cutoff+1) := by
   rw [protectedMarkAddress_value];nlinarith

 def protectedMark (cutoff : ℕ) : CountedValue (Fin ((2*cutoff+1)*(2*cutoff+1))) :=
   let result := protectedMarkAddress cutoff
   ⟨⟨result.count,protectedMarkAddress_lt cutoff⟩,result.work⟩

 theorem protectedMark_value (cutoff : ℕ) : (protectedMark cutoff).value=finiteProtectedMark cutoff := by
   apply Fin.ext
   simp only [protectedMark,protectedMarkAddress_value]
   change cutoff+(2*cutoff+1)*cutoff=((0 : ℤ)+(cutoff : ℤ)).toNat+
     (2*cutoff+1)*((0 : ℤ)+(cutoff : ℤ)).toNat
   simp


 theorem protectedMark_work (cutoff : ℕ) :
     (protectedMark cutoff).work=3*cutoff+1+(2*cutoff+1)*(2*cutoff+3)+1+2*cutoff+1+4 := by
   simp only [protectedMark,protectedMarkAddress,doubleCounter_work,doubleCounter_value,multiplyCounter_work,addCounter_work,Nat.succ_eq_add_one]
   ring

 def protectedAtom (cutoff : ℕ) : RationalResult :=
   let doubled := doubleCounter cutoff
   let features := multiplyCounter doubled.count.succ doubled.count.succ
   let denominator := multiplyCounter 100 features.count
   let rational := RationalBits.ofCounter denominator.count
   let result := RationalBits.quotient RationalBits.one rational.data
   ⟨result.data,doubled.work+features.work+denominator.work+rational.work+result.work+5⟩

 theorem protectedAtom_value (cutoff : ℕ) : (protectedAtom cutoff).data.decode=finiteProtectedAtom cutoff := by
   simp only [protectedAtom,RationalBits.quotient_value,RationalBits.one_value,RationalBits.ofCounter_value,
     multiplyCounter_value,doubleCounter_value,finiteProtectedAtom,Nat.cast_mul,Nat.cast_ofNat]

end AFT.BinaryArithmetic
