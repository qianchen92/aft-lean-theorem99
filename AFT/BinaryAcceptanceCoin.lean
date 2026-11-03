import AFT.BinaryDyadicFloor

/-! # The actual binary acceptance coin

The program reads exactly the prescribed fair bits, clips and rounds the
encoded rational score, and decides acceptance by one binary borrow test.
It is pointwise identical to the earlier rational acceptance sampler.
-/
namespace AFT.BinaryArithmetic
open RationalNumerics PermutationProgram BetaReference

private theorem rationalAcceptance_threshold (bits : ℕ) (input : ℚ) (word : Fin bits → Fin 2) :
    (RationalAcceptanceCoin.draw bits input word).val=
      if (FiniteTicketSampler.bitTicket bits word).val<RationalAcceptanceCoin.count bits input then 0 else 1 := by
  have ht := (FiniteTicketSampler.bitTicket bits word).isLt
  have hc := RationalAcceptanceCoin.count_le bits input
  simp only [RationalAcceptanceCoin.draw,RationalAcceptanceCoin.counts,FiniteTicketSampler.drawBitTable,
    FiniteTicketSampler.drawFin,Fin.val_cast,List.ofFn_succ,List.ofFn_zero,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_fin_one]
  rw [FiniteTicketSampler.bucket]
  split_ifs with hfirst
  · rfl
  · have hh : (FiniteTicketSampler.bitTicket bits word).val-RationalAcceptanceCoin.count bits input <
        2^bits-RationalAcceptanceCoin.count bits input := by omega
    simp only [FiniteTicketSampler.bucket,if_pos hh,Nat.add_zero]

def binaryAcceptance (input : RationalBits) (bits : ℕ) (word : Fin bits → Fin 2) : CountedNatural :=
  let clipped := input.clipUnit
  let accepted := clipped.data.dyadicFloor bits
  let ticket := readBitTape bits word
  let comparison := subtract false ticket.digits accepted.digits
  ⟨if comparison.borrow then 0 else 1,
    clipped.work+accepted.work+ticket.work+comparison.work+4⟩

theorem binaryAcceptance_value (input : RationalBits) (bits : ℕ) (word : Fin bits → Fin 2) :
    (binaryAcceptance input bits word).value=(RationalAcceptanceCoin.draw bits input.decode word).val := by
  rw [rationalAcceptance_threshold]
  have hb := subtract_borrow (readBitTape bits word).digits (input.clipUnit.data.dyadicFloor bits).digits
  rw [readBitTape_value,RationalBits.dyadicFloor_value,RationalBits.clipUnit_value] at hb
  change (if (subtract false (readBitTape bits word).digits (input.clipUnit.data.dyadicFloor bits).digits).borrow
      then 0 else 1)=_
  simp only [RationalAcceptanceCoin.count]
  split_ifs with haccept hthreshold hthreshold
  · rfl
  · exact False.elim (hthreshold (hb.mp haccept))
  · exact False.elim (haccept (hb.mpr hthreshold))
  · rfl

def binaryAcceptanceWork (height bits : ℕ) : ℕ :=
  RationalBits.dyadicFloorWork height bits+50*(height+bits+1)+20

theorem binaryAcceptance_work (input : RationalBits) (height bits : ℕ) (word : Fin bits → Fin 2)
    (hh : HeightBound input.decode height) :
    (binaryAcceptance input bits word).work≤ binaryAcceptanceWork height bits := by
  have hc := RationalBits.clipUnit_height input height hh
  have wc := RationalBits.clipUnit_work input height hh
  have wa := RationalBits.dyadicFloor_work input.clipUnit.data height bits hc
  have ha := RationalBits.dyadicFloor_height input.clipUnit.data height bits hc
  have wm : max (readBitTape bits word).digits.length (input.clipUnit.data.dyadicFloor bits).digits.length≤
      height+bits+1 := by rw [readBitTape_length];omega
  simp only [binaryAcceptance,binaryAcceptanceWork,subtract_work,readBitTape_work]
  omega

end AFT.BinaryArithmetic
