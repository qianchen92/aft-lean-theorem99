import AFT.RationalHeight
import AFT.RationalGaussianResources

/-! # Binary heights of the actual finite pi and exponential series -/
namespace AFT.RationalNumerics
open scoped BigOperators

theorem factorial_height (count : ℕ) : HeightBound (count.factorial : ℚ) (count*count) := by
  apply HeightBound.of_nat
  calc
    _ ≤ count^count := Nat.factorial_le_pow count
    _ ≤ (2^count)^count := Nat.pow_le_pow_left (Nat.lt_two_pow_self (n:=count)).le _
    _ = _ := by rw [← pow_mul]

theorem arctanSum_height (value : ℚ) (bits terms : ℕ) (h : HeightBound value bits) :
    HeightBound (arctanSum value terms) (terms*((2*terms+1)*bits+(2*terms+1)+1)) := by
  unfold arctanSum
  have hh := HeightBound.sum (Finset.range terms)
    (fun index => (-1 : ℚ)^index*value^(2*index+1)/(2*index+1 : ℕ))
    ((2*terms+1)*bits+(2*terms+1)) (by
      intro index hi
      have hi' : index < terms := Finset.mem_range.mp hi
      have hs : HeightBound (-1 : ℚ) 0 := HeightBound.one.neg
      have hp := ((hs.pow index).mul (h.pow (2*index+1))).div (HeightBound.nat_coarse (2*index+1))
      apply hp.mono
      simp only [Nat.zero_mul,zero_add]
      nlinarith)
  simpa only [Finset.card_range] using hh

def piHeight (bits : ℕ) : ℕ := 2*((bits+3)*(6*(bits+3)+4))+3

theorem piApprox_height (bits : ℕ) : HeightBound (piApprox bits) (piHeight bits) := by
  have hh : HeightBound (1/2 : ℚ) 2 := by norm_num [HeightBound]
  have ht : HeightBound (1/3 : ℚ) 2 := by norm_num [HeightBound]
  have hf : HeightBound (4 : ℚ) 2 := by norm_num [HeightBound]
  have h1 := arctanSum_height (1/2) 2 (bits+3) hh
  have h2 := arctanSum_height (1/3) 2 (bits+3) ht
  have he := hf.mul (h1.add h2)
  convert he using 1
  unfold piHeight
  ring

theorem expSum_height (value : ℚ) (bits terms : ℕ) (h : HeightBound value bits) :
    HeightBound (expSum value terms) (terms*(terms*bits+terms^2+1)) := by
  unfold expSum
  have hh := HeightBound.sum (Finset.range terms)
    (fun index => value^index/(index.factorial : ℕ)) (terms*bits+terms^2) (by
      intro index hi
      have hi' : index < terms := Finset.mem_range.mp hi
      have hp := (h.pow index).div (factorial_height index)
      apply hp.mono
      nlinarith)
  simpa only [Finset.card_range] using hh

theorem max_zero_height (value : ℚ) (bits : ℕ) (h : HeightBound value bits) :
    HeightBound (max value 0) bits := by
  rcases le_total value 0 with hn|hp
  · rw [max_eq_right hn]
    exact HeightBound.zero.mono (Nat.zero_le _)
  · rwa [max_eq_left hp]

/-- This controls the actual range-reduced rational program, including its
Taylor denominator and final reciprocal power. -/
theorem expNegScaled_height (argument : ℚ) (bits scale precision : ℕ) (h : HeightBound argument bits) :
    HeightBound (expNegScaled argument scale precision)
      ((precision+scale+1)*((precision+scale+1)*(bits+scale)+(precision+scale+1)^2+1)*scale) := by
  have hv := h.div (HeightBound.nat_coarse scale)
  exact (expSum_height _ _ _ hv).inv.pow scale

theorem gaussianApprox_height (squaredWidth : ℚ) (point : ℤ) (precision ratioBits : ℕ)
    (hratio : HeightBound (gaussianRatio squaredWidth point) ratioBits) :
    HeightBound (gaussianApprox squaredWidth point precision)
      (gaussianTaylorTerms squaredWidth point precision*
        (gaussianTaylorTerms squaredWidth point precision*
          (piHeight (gaussianPiPrecision squaredWidth point precision)+ratioBits+
            gaussianExpScale squaredWidth point precision)+
          gaussianTaylorTerms squaredWidth point precision^2+1)*
        gaussianExpScale squaredWidth point precision) := by
  rw [gaussianApprox_eq_series]
  have harg := (piApprox_height (gaussianPiPrecision squaredWidth point precision)).mul hratio
  have hv := (max_zero_height _ _ harg).div (HeightBound.nat_coarse (gaussianExpScale squaredWidth point precision))
  exact (expSum_height _ _ _ hv).inv.pow _

end AFT.RationalNumerics
