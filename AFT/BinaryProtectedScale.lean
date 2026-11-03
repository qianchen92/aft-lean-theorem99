import AFT.BinaryProtectedFeatureCost

/-! The nonzero scale coordinate decoded by two real binary divisions. -/
namespace AFT.BinaryArithmetic
open AFT.BoundaryCalibration AFT.RationalRejectionProgram

 def protectedScaleAddress (modulus chart : ℕ) : UnaryCounterResult :=
   let square := multiplyCounter modulus modulus
   let outer := divideCounter chart square.count
   let inner := divideCounter outer.remainder modulus
   ⟨inner.quotient,square.work+outer.work+inner.work+3⟩

 theorem protectedScaleAddress_value (modulus chart : ℕ) (hm : 0 < modulus) :
     (protectedScaleAddress modulus chart).count=(chart%(modulus*modulus))/modulus := by
   dsimp only [protectedScaleAddress]
   rw [(divideCounter_value _ _ hm).1,multiplyCounter_value,
     (divideCounter_value _ _ (Nat.mul_pos hm hm)).2]

 theorem protectedScaleAddress_lt (modulus chart : ℕ) (hm : 0 < modulus) :
     (protectedScaleAddress modulus chart).count< modulus := by
   rw [protectedScaleAddress_value modulus chart hm]
   exact (Nat.div_lt_iff_lt_mul hm).mpr (Nat.mod_lt _ (Nat.mul_pos hm hm))

 def protectedScale (modulus : ℕ) [NeZero modulus] (chart : Fin (modulus*(modulus*modulus))) : CountedValue (Fin modulus) :=
   let result := protectedScaleAddress modulus chart.val
   ⟨⟨result.count,protectedScaleAddress_lt modulus chart.val (Nat.pos_of_ne_zero (NeZero.ne _))⟩,result.work⟩

 theorem protectedScale_value (modulus : ℕ) [NeZero modulus] (chart : Fin (modulus*(modulus*modulus))) :
     (protectedScale modulus chart).value=finiteAffineScale modulus chart := by
   apply (ZMod.finEquiv modulus).injective
   have hcoord := (finiteChartEquiv_coordinate modulus chart).2.1
   simp only [finiteAffineScale,RingEquiv.apply_symm_apply,hcoord]
   have hcast (x : Fin modulus) : (ZMod.finEquiv modulus) x=(x.val : ZMod modulus) := by
     cases modulus with
     | zero => exact (NeZero.ne 0 rfl).elim
     | succ n => apply Fin.ext;exact (Nat.mod_eq_of_lt x.isLt).symm
   rw [hcast]
   simp only [protectedScale,protectedScaleAddress_value _ _ (Nat.pos_of_ne_zero (NeZero.ne _))]

 def protectedScaleWork (modulus chart : ℕ) : ℕ :=
   modulus*(2*modulus+3)+1+500*(chart+modulus*modulus+2)^2+
     500*(modulus*modulus+modulus+2)^2+3

 theorem protectedScaleAddress_work (modulus chart : ℕ) (hm : 0 < modulus) :
     (protectedScaleAddress modulus chart).work≤ protectedScaleWork modulus chart := by
   have houter := divideCounter_work chart (multiplyCounter modulus modulus).count (by rw [multiplyCounter_value];exact Nat.mul_pos hm hm)
   have hr : (divideCounter chart (multiplyCounter modulus modulus).count).remainder≤ modulus*modulus := by
     rw [multiplyCounter_value,(divideCounter_value _ _ (Nat.mul_pos hm hm)).2]
     exact (Nat.mod_lt _ (Nat.mul_pos hm hm)).le
   have hi := divideCounter_work (divideCounter chart (multiplyCounter modulus modulus).count).remainder modulus hm
   have hi' := hi.trans (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (show
     (divideCounter chart (multiplyCounter modulus modulus).count).remainder+modulus+2≤ modulus*modulus+modulus+2 by omega) 2))
   simp only [multiplyCounter_value] at houter hi'
   simp only [protectedScaleAddress,protectedScaleWork,multiplyCounter_work,multiplyCounter_value]
   omega

end AFT.BinaryArithmetic
