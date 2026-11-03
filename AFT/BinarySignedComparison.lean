import AFT.BinarySignedAddition
import AFT.BinaryChartMetadata

/-! Signed comparisons use subtraction, trimming and a Boolean test only. -/
namespace AFT.BinaryArithmetic
open AFT.RationalRejectionProgram

 def signedLe (firstSign secondSign : Bool) (first second : List Bool) : CountedValue Bool :=
   let difference := signedAdd firstSign (!secondSign) first second
   let trimmed := normalize difference.digits
   ⟨difference.negative || trimmed.digits.isEmpty,difference.work+trimmed.work+4⟩

 theorem signedLe_value (firstSign secondSign : Bool) (first second : List Bool) :
     (signedLe firstSign secondSign first second).value=true ↔
       signedValue firstSign first≤signedValue secondSign second := by
   have hv := signedAdd_value firstSign (!secondSign) first second
   have hn : signedValue (!secondSign) second= -signedValue secondSign second := by cases secondSign <;> simp [signedValue]
   rw [hn] at hv
   have hz : (normalize (signedAdd firstSign (!secondSign) first second).digits).digits.isEmpty=true ↔
       value (signedAdd firstSign (!secondSign) first second).digits=0 := by
     rw [List.isEmpty_iff,normalize_nil_iff]
   simp only [signedLe,Bool.or_eq_true,hz]
   cases hs : (signedAdd firstSign (!secondSign) first second).negative with
   | false =>
     rw [hs] at hv
     change (value (signedAdd firstSign (!secondSign) first second).digits : ℤ)=
       signedValue firstSign first+ -signedValue secondSign second at hv
     simp only [Bool.false_eq_true,false_or]
     omega
   | true =>
     rw [hs] at hv
     change -(value (signedAdd firstSign (!secondSign) first second).digits : ℤ)=
       signedValue firstSign first+ -signedValue secondSign second at hv
     simp only [true_or,true_iff]
     omega


 theorem signedLe_work (firstSign secondSign : Bool) (first second : List Bool) :
     (signedLe firstSign secondSign first second).work≤24*max first.length second.length+18 := by
   have hs := signedAdd_work firstSign (!secondSign) first second
   have hl := signedAdd_length firstSign (!secondSign) first second
   have hn := normalize_work (signedAdd firstSign (!secondSign) first second).digits
   simp only [signedLe]
   omega

end AFT.BinaryArithmetic
