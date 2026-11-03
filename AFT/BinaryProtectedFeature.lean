import AFT.BinaryCounterDivision
import AFT.CountedChartCoordinates

/-! Protected affine features evaluated by explicit counter loops and binary
long division. `ZMod` appears only in the correctness statements. -/
namespace AFT.BinaryArithmetic
open AFT.BoundaryCalibration

 def modularDifference (address cutoff modulus : ℕ) : UnaryCounterResult :=
   let reduced := divideCounter cutoff modulus
   let offset := differenceCounter modulus reduced.remainder
   let shifted := addCounter address offset.count
   let result := divideCounter shifted.count modulus
   ⟨result.remainder,reduced.work+offset.work+shifted.work+result.work+4⟩

 theorem modularDifference_value (address cutoff modulus : ℕ) (hm : 0 <  modulus) :
     ((modularDifference address cutoff modulus).count : ZMod modulus)=(address : ZMod modulus)-(cutoff : ZMod modulus) := by
   have hcut := (divideCounter_value cutoff modulus hm).2
   have hfinal := (divideCounter_value (addCounter address (differenceCounter modulus (divideCounter cutoff modulus).remainder).count).count modulus hm).2
   dsimp only [modularDifference]
   rw [hfinal]
   simp only [addCounter_value,differenceCounter_value,hcut]
   rw [ZMod.natCast_mod,Nat.cast_add,Nat.cast_sub (Nat.le_of_lt (Nat.mod_lt cutoff hm)),ZMod.natCast_self,ZMod.natCast_mod]
   ring

 theorem modularDifference_lt (address cutoff modulus : ℕ) (hm : 0 <  modulus) :
     (modularDifference address cutoff modulus).count< modulus := by
   dsimp only [modularDifference]
   rw [(divideCounter_value _ _ hm).2]
   exact Nat.mod_lt _ hm

 def protectedFeatureAddress (cutoff modulus input chart : ℕ) : UnaryCounterResult :=
   let doubled := doubleCounter cutoff
   let width := doubled.count.succ
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
   let result := divideCounter total.count modulus
   ⟨result.remainder,doubled.work+source.work+square.work+outer.work+inner.work+first.work+second.work+
     firstProduct.work+secondProduct.work+prefixSum.work+total.work+result.work+13⟩

 theorem protectedFeatureAddress_lt (cutoff modulus input chart : ℕ) (hm : 0 <  modulus) :
     (protectedFeatureAddress cutoff modulus input chart).count< modulus := by
   dsimp only [protectedFeatureAddress]
   rw [(divideCounter_value _ _ hm).2]
   exact Nat.mod_lt _ hm

 theorem protectedFeatureAddress_formula (cutoff modulus input chart : ℕ) (hm : 0 <  modulus) :
     ((protectedFeatureAddress cutoff modulus input chart).count : ZMod modulus)=
       (chart/(modulus*modulus) : ℕ)+
         ((chart%(modulus*modulus))/modulus : ℕ)*((input/(2*cutoff+1) : ℕ)-(cutoff : ZMod modulus))+
         ((chart%(modulus*modulus))%modulus : ℕ)*((input%(2*cutoff+1) : ℕ)-(cutoff : ZMod modulus)) := by
   dsimp only [protectedFeatureAddress]
   rw [(divideCounter_value _ _ hm).2,ZMod.natCast_mod]
   simp only [addCounter_value,multiplyCounter_value,Nat.cast_add,Nat.cast_mul,modularDifference_value _ _ _ hm]
   simp only [(divideCounter_value _ _ (Nat.mul_pos hm hm)).1,(divideCounter_value _ _ (Nat.mul_pos hm hm)).2,
     (divideCounter_value _ _ hm).1,(divideCounter_value _ _ hm).2,doubleCounter_value]
   rw [(divideCounter_value input (2*cutoff+1) (by omega)).1,(divideCounter_value input (2*cutoff+1) (by omega)).2]

 theorem finiteChartEquiv_coordinate (modulus : ℕ) [NeZero modulus]
     (chart : Fin (modulus*(modulus*modulus))) :
     (finiteChartEquiv modulus chart).1=(chart.val/(modulus*modulus) : ℕ) ∧
       (finiteChartEquiv modulus chart).2.1=((chart.val%(modulus*modulus))/modulus : ℕ) ∧
       (finiteChartEquiv modulus chart).2.2=((chart.val%(modulus*modulus))%modulus : ℕ) := by
   cases modulus with
   | zero => exact (NeZero.ne 0 rfl).elim
   | succ modulus =>
     simp only [finiteChartEquiv,Equiv.trans_apply,Equiv.prodCongr_apply,finProdFinEquiv_symm_apply,
       ZMod.finEquiv,RingEquiv.toEquiv_eq_coe,EquivLike.coe_coe]
     constructor
     · apply Fin.ext
       exact (Nat.mod_eq_of_lt (Fin.divNat chart).isLt).symm
     constructor
     · apply Fin.ext
       exact (Nat.mod_eq_of_lt (Fin.divNat (Fin.modNat chart)).isLt).symm
     · apply Fin.ext
       exact (Nat.mod_eq_of_lt (Fin.modNat (Fin.modNat chart)).isLt).symm

 def protectedFeature (cutoff modulus : ℕ) [NeZero modulus]
     (input : Fin ((2*cutoff+1)*(2*cutoff+1))) (chart : Fin (modulus*(modulus*modulus))) :
     AFT.RationalRejectionProgram.CountedValue (Fin modulus) :=
   let result := protectedFeatureAddress cutoff modulus input.val chart.val
   ⟨⟨result.count,protectedFeatureAddress_lt cutoff modulus input.val chart.val (Nat.pos_of_ne_zero (NeZero.ne _))⟩,result.work⟩

 theorem protectedFeature_value (cutoff modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]
     (input : Fin ((2*cutoff+1)*(2*cutoff+1))) (chart : Fin (modulus*(modulus*modulus))) :
     (protectedFeature cutoff modulus input chart).value=finiteProtectedFeatures cutoff modulus input chart := by
   have hm : 0 <  modulus := Nat.pos_of_ne_zero (NeZero.ne _)
   have hf := protectedFeatureAddress_formula cutoff modulus input.val chart.val hm
   have hc := finiteChartEquiv_coordinate modulus chart
   have hcast (x : Fin modulus) : (ZMod.finEquiv modulus) x=(x.val : ZMod modulus) := by
     cases modulus with
     | zero => exact (NeZero.ne 0 rfl).elim
     | succ n => apply Fin.ext;exact (Nat.mod_eq_of_lt x.isLt).symm
   apply (ZMod.finEquiv modulus).injective
   rw [hcast]
   change ((protectedFeatureAddress cutoff modulus input.val chart.val).count : ZMod modulus)=_
   rw [hf]
   simp only [finiteProtectedFeatures,finiteAffineFeature,RingEquiv.apply_symm_apply,feature,hc.1,hc.2.1,hc.2.2]
   simp only [finiteInputEquiv,Equiv.trans_apply,Equiv.prodCongr_apply,finProdFinEquiv_symm_apply,
     FiniteConvolutionProgram.windowIndexEquiv,Equiv.coe_fn_mk,Prod.map_apply,Int.cast_sub,Int.cast_natCast]
   rfl

end AFT.BinaryArithmetic
