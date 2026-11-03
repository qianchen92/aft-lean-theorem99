import AFT.BinaryFiniteArithmetic
import AFT.BinaryLoopControl

/-! Actual binary rational evaluation of the finite Taylor, arctangent,
and Machin-style pi series, including every dynamic denominator. -/
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics

def arctanTerm (input : RationalBits) (index : ℕ) : RationalResult :=
  let doubled := doubleCounter index
  let degree := doubled.count.succ
  let sign := power minusOne index
  let argument := power input degree
  let numerator := multiply sign.data argument.data
  let denominator := ofCounter degree
  let result := quotient numerator.data denominator.data
  ⟨result.data,sign.work+argument.work+numerator.work+denominator.work+result.work+doubled.work+5⟩

def taylorTerm (input : RationalBits) (index : ℕ) : RationalResult :=
  let numerator := power input index
  let denominator := factorial index
  let result := quotient numerator.data denominator.data
  ⟨result.data,numerator.work+denominator.work+result.work+3⟩

def arctan (input : RationalBits) (terms : ℕ) : RationalResult := sumRange (arctanTerm input) terms
def taylor (input : RationalBits) (terms : ℕ) : RationalResult := sumRange (taylorTerm input) terms

theorem arctanTerm_value (input : RationalBits) (index : ℕ) :
    (arctanTerm input index).data.decode=(-1 : ℚ)^index*input.decode^(2*index+1)/(2*index+1 : ℕ) := by
  simp only [arctanTerm,doubleCounter_value,quotient_value,multiply_value,power_value,ofCounter_value,minusOne_value]

theorem taylorTerm_value (input : RationalBits) (index : ℕ) :
    (taylorTerm input index).data.decode=input.decode^index/(index.factorial : ℚ) := by
  simp only [taylorTerm,quotient_value,power_value,factorial_value]

theorem arctan_value (input : RationalBits) (terms : ℕ) :
    (arctan input terms).data.decode=arctanSum input.decode terms := by
  simp only [arctan,sumRange_value,arctanTerm_value,arctanSum]

theorem taylor_value (input : RationalBits) (terms : ℕ) :
    (taylor input terms).data.decode=expSum input.decode terms := by
  simp only [taylor,sumRange_value,taylorTerm_value,expSum]

def seriesTermBits (bits terms : ℕ) : ℕ := (2*terms+2)^2*(bits+1)
def seriesStepWork (bits terms : ℕ) : ℕ :=
  primitiveWorkBound (seriesTermBits bits terms)+60*(2*terms+2)^2+10

def seriesTermWork (bits terms : ℕ) : ℕ := 10*(terms+1)*seriesStepWork bits terms

def seriesWork (bits terms : ℕ) : ℕ :=
  terms*(seriesTermWork bits terms+primitiveWorkBound ((terms+1)*(seriesTermBits bits terms+1))+2)+2

private theorem termBits_bounds (bits terms index : ℕ) (hi : index ≤ terms) :
    bits*(2*index+2) ≤ seriesTermBits bits terms ∧
    (index+1)^2 ≤ seriesTermBits bits terms ∧
    (2*index+1)*(bits+1) ≤ seriesTermBits bits terms ∧
    index*bits+index*index ≤ seriesTermBits bits terms := by
  dsimp [seriesTermBits]
  have hs : (index+1)^2 ≤ (terms+1)^2 := Nat.pow_le_pow_left (by omega) _
  have hlinear : 2*index+2 ≤ (2*terms+2)^2 := by nlinarith
  refine ⟨?_,?_,?_,?_⟩
  · calc
      bits*(2*index+2) ≤ (bits+1)*(2*index+2) := Nat.mul_le_mul_right _ (by omega)
      _ ≤ (bits+1)*(2*terms+2)^2 := Nat.mul_le_mul_left _ hlinear
      _ = _ := Nat.mul_comm ..
  · nlinarith
  · exact Nat.mul_le_mul_right _ (by omega)
  · nlinarith

theorem arctanTerm_height (input : RationalBits) (bits terms index : ℕ)
    (h : HeightBound input.decode bits) (hi : index ≤ terms) :
    HeightBound (arctanTerm input index).data.decode (seriesTermBits bits terms) := by
  rw [arctanTerm_value]
  have hh := (((HeightBound.one.neg).pow index).mul (h.pow (2*index+1))).div (HeightBound.nat_coarse (2*index+1))
  apply hh.mono
  have hb := (termBits_bounds bits terms index hi).2.2.1
  simp only [Nat.zero_mul,Nat.zero_add]
  nlinarith

theorem taylorTerm_height (input : RationalBits) (bits terms index : ℕ)
    (h : HeightBound input.decode bits) (hi : index ≤ terms) :
    HeightBound (taylorTerm input index).data.decode (seriesTermBits bits terms) := by
  rw [taylorTerm_value]
  exact ((h.pow index).div (factorial_height index)).mono (by
    have hb := (termBits_bounds bits terms index hi).2.2.2
    nlinarith)

theorem arctanTerm_work (input : RationalBits) (bits terms index : ℕ)
    (h : HeightBound input.decode bits) (hi : index ≤ terms) :
    (arctanTerm input index).work ≤ seriesTermWork bits terms := by
  let B := seriesTermBits bits terms
  let P := primitiveWorkBound B
  have hb := termBits_bounds bits terms index hi
  have h0 : HeightBound minusOne.decode 0 := by rw [minusOne_value];exact HeightBound.one.neg
  have hsign := power_work minusOne 0 index h0
  have harg := power_work input bits (2*index+1) h
  have hp0 : primitiveWorkBound (0*(index+1)) ≤ P := primitiveWorkBound_mono (by omega)
  have hpa : primitiveWorkBound (bits*(2*index+1+1)) ≤ P := primitiveWorkBound_mono (by simpa only [Nat.add_assoc] using hb.1)
  have hs : HeightBound (power minusOne index).data.decode B := by
    rw [power_value,minusOne_value]
    exact ((HeightBound.one.neg).pow index).mono (by simp)
  have ha : HeightBound (power input (2*index+1)).data.decode B := by
    rw [power_value];exact (h.pow _).mono (by dsimp [B];nlinarith [hb.1])
  have hm := multiply_work (power minusOne index).data (power input (2*index+1)).data B hs ha
  have hn := ofCounter_work (2*index+1)
  have hn' : (ofCounter (2*index+1)).work ≤ 60*(2*terms+2)^2 :=
    hn.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  have hnum : HeightBound (multiply (power minusOne index).data (power input (2*index+1)).data).data.decode B := by
    rw [multiply_value,power_value,power_value,minusOne_value]
    exact (((HeightBound.one.neg).pow index).mul (h.pow _)).mono (by simp only [Nat.zero_mul,Nat.zero_add];dsimp [B];nlinarith [hb.1])
  have hden : HeightBound (ofCounter (2*index+1)).data.decode B := by
    rw [ofCounter_value];exact (HeightBound.nat_coarse _).mono (by dsimp [B];nlinarith [hb.2.2.1])
  have hq := quotient_work _ _ B hnum hden
  simp only [arctanTerm,doubleCounter_value,doubleCounter_work,seriesTermWork,seriesStepWork]
  dsimp only [P,B] at hp0 hpa
  nlinarith

theorem taylorTerm_work (input : RationalBits) (bits terms index : ℕ)
    (h : HeightBound input.decode bits) (hi : index ≤ terms) :
    (taylorTerm input index).work ≤ seriesTermWork bits terms := by
  let B := seriesTermBits bits terms
  let P := primitiveWorkBound B
  have hb := termBits_bounds bits terms index hi
  have hnum := power_work input bits index h
  have hden := factorial_work_le index terms hi
  have hpa : primitiveWorkBound (bits*(index+1)) ≤ P := primitiveWorkBound_mono (by dsimp [B];nlinarith [hb.1])
  have hpf : primitiveWorkBound ((terms+1)^2) ≤ P :=
    primitiveWorkBound_mono (termBits_bounds bits terms terms le_rfl).2.1
  have hp : HeightBound (power input index).data.decode B := by
    rw [power_value];exact (h.pow _).mono (by dsimp [B];nlinarith [hb.1])
  have hf : HeightBound (factorial index).data.decode B := by
    rw [factorial_value];exact (factorial_height index).mono (by dsimp [B];nlinarith [hb.2.1])
  have hq := quotient_work _ _ B hp hf
  have hsq : (terms+2)^2 ≤ (2*terms+2)^2 := Nat.pow_le_pow_left (by omega) _
  simp only [taylorTerm,seriesTermWork,seriesStepWork,factorialWorkStep] at *
  dsimp only [P,B] at hpa hpf hq
  nlinarith

theorem arctan_work (input : RationalBits) (bits terms : ℕ) (h : HeightBound input.decode bits) :
    (arctan input terms).work ≤ seriesWork bits terms :=
  sumRange_work (arctanTerm input) (seriesTermBits bits terms) (seriesTermWork bits terms) terms
    (fun index hi => arctanTerm_height input bits terms index h hi.le)
    (fun index hi => arctanTerm_work input bits terms index h hi.le)

theorem taylor_work (input : RationalBits) (bits terms : ℕ) (h : HeightBound input.decode bits) :
    (taylor input terms).work ≤ seriesWork bits terms :=
  sumRange_work (taylorTerm input) (seriesTermBits bits terms) (seriesTermWork bits terms) terms
    (fun index hi => taylorTerm_height input bits terms index h hi.le)
    (fun index hi => taylorTerm_work input bits terms index h hi.le)

def pi (bits : ℕ) : RationalResult :=
  let count := addCounter bits 3
  let first := arctan half count.count
  let second := arctan third count.count
  let sum := add first.data second.data
  let result := multiply four sum.data
  ⟨result.data,first.work+second.work+sum.work+result.work+count.work+4⟩

theorem pi_value (bits : ℕ) : (pi bits).data.decode=piApprox bits := by
  simp only [pi,addCounter_value,multiply_value,add_value,arctan_value,half_value,third_value,four_value,piApprox]

def piWork (bits : ℕ) : ℕ := 2*seriesWork 2 (bits+3)+2*primitiveWorkBound (piHeight bits)+(2*bits+1)+4

theorem pi_work (bits : ℕ) : (pi bits).work ≤ piWork bits := by
  have hh : HeightBound half.decode 2 := by rw [half_value];norm_num [HeightBound]
  have ht : HeightBound third.decode 2 := by rw [third_value];norm_num [HeightBound]
  have hw1 := arctan_work half 2 (bits+3) hh
  have hw2 := arctan_work third 2 (bits+3) ht
  have h1 := arctanSum_height half.decode 2 (bits+3) hh
  have h2 := arctanSum_height third.decode 2 (bits+3) ht
  rw [← arctan_value] at h1 h2
  have hb : (bits+3)*((2*(bits+3)+1)*2+(2*(bits+3)+1)+1) ≤ piHeight bits := by unfold piHeight;nlinarith
  have hs := add_work (arctan half (bits+3)).data (arctan third (bits+3)).data (piHeight bits) (h1.mono hb) (h2.mono hb)
  have hsum : HeightBound (add (arctan half (bits+3)).data (arctan third (bits+3)).data).data.decode (piHeight bits) := by
    rw [add_value]
    exact (h1.add h2).mono (by unfold piHeight;nlinarith)
  have hf : HeightBound four.decode (piHeight bits) := by
    rw [four_value]
    exact (show HeightBound (4 : ℚ) 2 by norm_num [HeightBound]).mono (by unfold piHeight;nlinarith)
  have hm := multiply_work four (add (arctan half (bits+3)).data (arctan third (bits+3)).data).data (piHeight bits) hf hsum
  simp only [pi,piWork,addCounter_value,addCounter_work]
  omega

end AFT.BinaryArithmetic.RationalBits
