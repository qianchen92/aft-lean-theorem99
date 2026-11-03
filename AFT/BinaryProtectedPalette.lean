import AFT.BinaryProtectedFeature
import AFT.BinarySignedComparison

/-! The protected palette predicate on actual signed digit strings.
Four explicit signed comparisons replace max/min endpoint tests. -/
namespace AFT.BinaryArithmetic
open AFT.BoundaryCalibration AFT.RationalRejectionProgram

 theorem signedValue_not (sign : Bool) (digits : List Bool) :
     signedValue (!sign) digits= -signedValue sign digits := by cases sign <;> simp [signedValue]

 def protectedPalette (cutoff modulus : ℕ) (boundarySign baselineSign : Bool)
     (boundary baseline : List Bool) (input color : ℕ) : CountedValue Bool :=
   let doubled := doubleCounter cutoff
   let source := divideCounter input doubled.count.succ
   let address := canonicalCounter source.remainder
   let shiftRadius := canonicalCounter cutoff
   let modulusBits := canonicalCounter modulus
   let colorBits := canonicalCounter color
   let shiftStart := signedAdd baselineSign false baseline shiftRadius.digits
   let shift := signedAdd shiftStart.negative true shiftStart.digits address.digits
   let lower := signedAdd boundarySign shift.negative boundary shift.digits
   let upperStart := signedAdd false (!boundarySign) modulusBits.digits boundary
   let upper := signedAdd upperStart.negative shift.negative upperStart.digits shift.digits
   let lowerTest := signedLe boundarySign false boundary colorBits.digits
   let shiftedLowerTest := signedLe lower.negative false lower.digits colorBits.digits
   let upperTest := signedLe upperStart.negative false upperStart.digits colorBits.digits
   let shiftedUpperTest := signedLe upper.negative false upper.digits colorBits.digits
   ⟨lowerTest.value && shiftedLowerTest.value && !upperTest.value && !shiftedUpperTest.value,
     doubled.work+source.work+address.work+shiftRadius.work+modulusBits.work+colorBits.work+
     shiftStart.work+shift.work+lower.work+upperStart.work+upper.work+
     lowerTest.work+shiftedLowerTest.work+upperTest.work+shiftedUpperTest.work+20⟩

 theorem protectedPalette_formula (cutoff modulus : ℕ) (boundarySign baselineSign : Bool)
     (boundary baseline : List Bool) (input color : ℕ) :
     (protectedPalette cutoff modulus boundarySign baselineSign boundary baseline input color).value=true ↔
       signedValue boundarySign boundary+max (signedValue baselineSign baseline-
         ((input%(2*cutoff+1) : ℕ)-(cutoff : ℤ))) 0≤(color : ℤ) ∧
       (color : ℤ)<(modulus : ℤ)-signedValue boundarySign boundary+
         min (signedValue baselineSign baseline-((input%(2*cutoff+1) : ℕ)-(cutoff : ℤ))) 0 := by
   let source := divideCounter input (doubleCounter cutoff).count.succ
   let address := canonicalCounter source.remainder
   let shiftRadius := canonicalCounter cutoff
   let modulusBits := canonicalCounter modulus
   let colorBits := canonicalCounter color
   let shiftStart := signedAdd baselineSign false baseline shiftRadius.digits
   let shift := signedAdd shiftStart.negative true shiftStart.digits address.digits
   let lower := signedAdd boundarySign shift.negative boundary shift.digits
   let upperStart := signedAdd false (!boundarySign) modulusBits.digits boundary
   let upper := signedAdd upperStart.negative shift.negative upperStart.digits shift.digits
   have hsource : source.remainder=input%(2*cutoff+1) := by
     dsimp only [source];simpa only [doubleCounter_value] using (divideCounter_value input (doubleCounter cutoff).count.succ (Nat.succ_pos _)).2
   have hstart : signedValue shiftStart.negative shiftStart.digits=signedValue baselineSign baseline+(cutoff : ℤ) := by
     dsimp only [shiftStart];rw [signedAdd_value]
     simp only [shiftRadius,signedValue,Bool.false_eq_true,ite_false,canonicalCounter_value]
   have hshift : signedValue shift.negative shift.digits=signedValue baselineSign baseline-
       ((input%(2*cutoff+1) : ℕ)-(cutoff : ℤ)) := by
     dsimp only [shift];rw [signedAdd_value,hstart]
     simp only [address,signedValue,ite_true,canonicalCounter_value,hsource]
     ring
   have hlower := signedAdd_value boundarySign shift.negative boundary shift.digits
   change signedValue lower.negative lower.digits=_ at hlower
   rw [hshift] at hlower
   have hupperStart : signedValue upperStart.negative upperStart.digits=(modulus : ℤ)-signedValue boundarySign boundary := by
     dsimp only [upperStart];rw [signedAdd_value,signedValue_not]
     simp only [modulusBits,signedValue,Bool.false_eq_true,ite_false,canonicalCounter_value,sub_eq_add_neg]
   have hupper := signedAdd_value upperStart.negative shift.negative upperStart.digits shift.digits
   change signedValue upper.negative upper.digits=_ at hupper
   rw [hupperStart,hshift] at hupper
   have hcolor : signedValue false colorBits.digits=(color : ℤ) := by simp [colorBits,signedValue,canonicalCounter_value]
   change ((signedLe boundarySign false boundary colorBits.digits).value &&
     (signedLe lower.negative false lower.digits colorBits.digits).value &&
     !(signedLe upperStart.negative false upperStart.digits colorBits.digits).value &&
     !(signedLe upper.negative false upper.digits colorBits.digits).value)=true ↔ _
   simp only [Bool.and_eq_true,Bool.not_eq_true',Bool.eq_false_iff,ne_eq,signedLe_value,hcolor,hlower,hupperStart,hupper]
   omega

 theorem protectedPalette_value (cutoff modulus : ℕ) (boundarySign baselineSign : Bool)
     (boundary baseline : List Bool) (input : Fin ((2*cutoff+1)*(2*cutoff+1))) (color : Fin modulus) :
     (protectedPalette cutoff modulus boundarySign baselineSign boundary baseline input.val color.val).value=true ↔
       color∈finiteProtectedPalettes cutoff modulus (signedValue boundarySign boundary) (signedValue baselineSign baseline) input := by
   rw [protectedPalette_formula]
   simp only [finiteProtectedPalettes,TrimmedSlice.paletteSlice,Finset.mem_filter,Finset.mem_univ,true_and,
     TrimmedSlice.slice,Finset.mem_Ico,finiteInputEquiv,Equiv.trans_apply,Equiv.prodCongr_apply,
     finProdFinEquiv_symm_apply,FiniteConvolutionProgram.windowIndexEquiv,Equiv.coe_fn_mk,Prod.map_apply]
   rfl

end AFT.BinaryArithmetic
