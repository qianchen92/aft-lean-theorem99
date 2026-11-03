import AFT.BinaryProtectedPalette

/-! Bit costs of the actual palette predicate, including signed endpoints. -/
namespace AFT.BinaryArithmetic

 def protectedPaletteWork (cutoff modulus input color boundaryBits baselineBits : ℕ) : ℕ :=
   3*cutoff+1+500*(input+(2*cutoff+1)+2)^2+
     50*(2*cutoff+2)^2+50*(cutoff+1)^2+50*(modulus+1)^2+50*(color+1)^2+
     200*(boundaryBits+baselineBits+3*cutoff+modulus+color+10)+200

 theorem protectedPalette_work (cutoff modulus : ℕ) (boundarySign baselineSign : Bool)
     (boundary baseline : List Bool) (input color : ℕ) :
     (protectedPalette cutoff modulus boundarySign baselineSign boundary baseline input color).work≤
       protectedPaletteWork cutoff modulus input color boundary.length baseline.length := by
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
   let L := boundary.length+baseline.length+3*cutoff+modulus+color+10
   have hsize (n : ℕ) : n.size≤ n := Nat.size_le.mpr (Nat.lt_two_pow_self (n:=n))
   have hsource : source.remainder≤2*cutoff+1 := by
     dsimp only [source];rw [(divideCounter_value _ _ (Nat.succ_pos _)).2]
     simpa only [doubleCounter_value] using (Nat.mod_lt input (Nat.succ_pos (doubleCounter cutoff).count)).le
   have ha : address.digits.length≤2*cutoff+1 := by
     dsimp only [address];rw [canonicalCounter_length];exact (hsize _).trans hsource
   have hr : shiftRadius.digits.length≤ cutoff := by dsimp only [shiftRadius];rw [canonicalCounter_length];exact hsize _
   have hm : modulusBits.digits.length≤ modulus := by dsimp only [modulusBits];rw [canonicalCounter_length];exact hsize _
   have hc : colorBits.digits.length≤ color := by dsimp only [colorBits];rw [canonicalCounter_length];exact hsize _
   have hst : shiftStart.digits.length≤ baseline.length+cutoff+1 :=
     (signedAdd_length baselineSign false baseline shiftRadius.digits).trans (by omega)
   have hsh : shift.digits.length≤ baseline.length+3*cutoff+3 :=
     (signedAdd_length shiftStart.negative true shiftStart.digits address.digits).trans (by omega)
   have hlo : lower.digits.length≤ boundary.length+baseline.length+3*cutoff+4 :=
     (signedAdd_length boundarySign shift.negative boundary shift.digits).trans (by omega)
   have hus : upperStart.digits.length≤ modulus+boundary.length+1 :=
     (signedAdd_length false (!boundarySign) modulusBits.digits boundary).trans (by omega)
   have hup : upper.digits.length≤ modulus+boundary.length+baseline.length+3*cutoff+5 :=
     (signedAdd_length upperStart.negative shift.negative upperStart.digits shift.digits).trans (by omega)
   have hsw := divideCounter_work input (doubleCounter cutoff).count.succ (Nat.succ_pos _)
   change source.work≤_ at hsw
   simp only [doubleCounter_value,Nat.succ_eq_add_one] at hsw
   have haw := (canonicalCounter_work source.remainder).trans
     (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (show source.remainder+1≤2*cutoff+2 by omega) 2))
   change address.work≤_ at haw
   have hrw := canonicalCounter_work cutoff
   change shiftRadius.work≤_ at hrw
   have hmw := canonicalCounter_work modulus
   change modulusBits.work≤_ at hmw
   have hcw := canonicalCounter_work color
   change colorBits.work≤_ at hcw
   have hstw : shiftStart.work≤20*L+8 := (signedAdd_work baselineSign false baseline shiftRadius.digits).trans (by dsimp [L];omega)
   have hshw : shift.work≤20*L+8 := (signedAdd_work shiftStart.negative true shiftStart.digits address.digits).trans (by dsimp [L];omega)
   have hlow : lower.work≤20*L+8 := (signedAdd_work boundarySign shift.negative boundary shift.digits).trans (by dsimp [L];omega)
   have husw : upperStart.work≤20*L+8 := (signedAdd_work false (!boundarySign) modulusBits.digits boundary).trans (by dsimp [L];omega)
   have hupw : upper.work≤20*L+8 := (signedAdd_work upperStart.negative shift.negative upperStart.digits shift.digits).trans (by dsimp [L];omega)
   have hltw : (signedLe boundarySign false boundary colorBits.digits).work≤24*L+18 :=
     (signedLe_work boundarySign false boundary colorBits.digits).trans (by dsimp [L];omega)
   have hltw' : (signedLe lower.negative false lower.digits colorBits.digits).work≤24*L+18 :=
     (signedLe_work lower.negative false lower.digits colorBits.digits).trans (by dsimp [L];omega)
   have hutw : (signedLe upperStart.negative false upperStart.digits colorBits.digits).work≤24*L+18 :=
     (signedLe_work upperStart.negative false upperStart.digits colorBits.digits).trans (by dsimp [L];omega)
   have hutw' : (signedLe upper.negative false upper.digits colorBits.digits).work≤24*L+18 :=
     (signedLe_work upper.negative false upper.digits colorBits.digits).trans (by dsimp [L];omega)
   change (doubleCounter cutoff).work+source.work+address.work+shiftRadius.work+modulusBits.work+colorBits.work+
     shiftStart.work+shift.work+lower.work+upperStart.work+upper.work+
     (signedLe boundarySign false boundary colorBits.digits).work+
     (signedLe lower.negative false lower.digits colorBits.digits).work+
     (signedLe upperStart.negative false upperStart.digits colorBits.digits).work+
     (signedLe upper.negative false upper.digits colorBits.digits).work+20≤_
   rw [doubleCounter_work]
   unfold protectedPaletteWork
   dsimp only [L] at hstw hshw hlow husw hupw hltw hltw' hutw hutw'
   omega

end AFT.BinaryArithmetic
