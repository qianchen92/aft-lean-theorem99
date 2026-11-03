import AFT.BinaryFiniteArithmetic
import AFT.UnaryPolynomialCounters
import CurrentAFT.BinaryCalibrationIteration

/-! # Binomial coefficients with a fixed number of binary arithmetic steps

The loop length is the selected degree, not the population. Every subtraction,
conversion and rational operation belongs to the executed program.
-/
namespace CurrentAFT.BinaryBinomialCoefficient
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

def current (population : ℕ) : ℕ → RationalResult
  | 0 => ⟨one, 2⟩
  | count+1 =>
    let previous := current population count
    let remaining := subtractCounter population count
    let numerator := ofCounter remaining.count
    let denominator := ofCounter (count+1)
    let product := multiply previous.data numerator.data
    let result := quotient product.data denominator.data
    ⟨result.data, previous.work+remaining.work+numerator.work+denominator.work+product.work+result.work+5⟩

theorem current_value (population count : ℕ) :
    (current population count).data.decode = (population.choose count : ℚ) := by
  induction count with
  | zero => simp [current]
  | succ count ih =>
    simp only [current, quotient_value, RationalBits.multiply_value, ofCounter_value, subtractCounter_value, ih]
    apply (div_eq_iff (show (count+1 : ℕ) ≠ (0 : ℚ) by positivity)).mpr
    exact_mod_cast (Nat.choose_succ_right_eq population count).symm

def stepWork (order population : ℕ) : ℕ :=
  2*population+2 + 60*(population+1)^2 + 60*(order+2)^2 +
    3*primitiveWorkBound ((order+1)*(population+order+2)) + 7

theorem current_bounds (order population count : ℕ) (hc : count ≤ order) :
    HeightBound (current population count).data.decode (count*(population+order+1)) ∧
      (current population count).work ≤ count*stepWork order population+2 := by
  induction count with
  | zero => simp only [current, one_value, zero_mul, zero_add]; exact ⟨HeightBound.one, le_rfl⟩
  | succ count ih =>
    have hp := ih (by omega)
    let B := (order+1)*(population+order+2)
    have hr := subtractCounter_work_left population count
    have hn := ofCounter_work (subtractCounter population count).count
    have hd := ofCounter_work (count+1)
    have hsmall : (subtractCounter population count).count ≤ population := by
      rw [subtractCounter_value]; exact Nat.sub_le _ _
    have hnh : HeightBound (ofCounter (subtractCounter population count).count).data.decode population := by
      rw [ofCounter_value]
      exact (HeightBound.nat_coarse _).mono hsmall
    have hdh : HeightBound (ofCounter (count+1)).data.decode (order+1) := by
      rw [ofCounter_value]
      exact (HeightBound.nat_coarse _).mono (by omega)
    have hprod := hp.1.mul hnh
    have hpB : count*(population+order+1) ≤ B := by dsimp [B]; nlinarith
    have hnB : population ≤ B := by dsimp [B]; nlinarith
    have hdB : order+1 ≤ B := by dsimp [B]; nlinarith
    have hprodB : count*(population+order+1)+population ≤ B := by dsimp [B]; nlinarith
    have hm := multiply_work (current population count).data
      (ofCounter (subtractCounter population count).count).data B (hp.1.mono hpB) (hnh.mono hnB)
    have hq := quotient_work
      (multiply (current population count).data (ofCounter (subtractCounter population count).count).data).data
      (ofCounter (count+1)).data B (by rw [RationalBits.multiply_value]; exact hprod.mono hprodB) (hdh.mono hdB)
    constructor
    · simp only [current, quotient_value, RationalBits.multiply_value]
      exact (hprod.div hdh).mono (by nlinarith)
    · have hn' : (ofCounter (subtractCounter population count).count).work ≤ 60*(population+1)^2 :=
        hn.trans (by gcongr)
      have hd' : (ofCounter (count+1)).work ≤ 60*(order+2)^2 := hd.trans (by gcongr; omega)
      change (current population count).work + (subtractCounter population count).work +
        (ofCounter (subtractCounter population count).count).work + (ofCounter (count+1)).work +
        (multiply (current population count).data (ofCounter (subtractCounter population count).count).data).work +
        (quotient (multiply (current population count).data (ofCounter (subtractCounter population count).count).data).data
          (ofCounter (count+1)).data).work + 5 ≤ _
      dsimp only [B] at hm hq
      have hstep : (subtractCounter population count).work +
        (ofCounter (subtractCounter population count).count).work + (ofCounter (count+1)).work +
        (multiply (current population count).data (ofCounter (subtractCounter population count).count).data).work +
        (quotient (multiply (current population count).data (ofCounter (subtractCounter population count).count).data).data
          (ofCounter (count+1)).data).work + 5 ≤ stepWork order population := by
        unfold stepWork
        omega
      nlinarith [hp.2]

theorem stepWork_mono (order : ℕ) {population larger : ℕ} (h : population ≤ larger) :
    stepWork order population ≤ stepWork order larger := by
  unfold stepWork primitiveWorkBound
  gcongr

noncomputable def heightPolynomial (order : ℕ) (population : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C order * (population + Polynomial.C (order+1))

noncomputable def workPolynomial (order : ℕ) (population : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C order * (2*population+2+60*(population+1)^2+Polynomial.C (60*(order+2)^2)+
    3*BinaryCalibrationIteration.primitivePolynomial
      (Polynomial.C (order+1)*(population+Polynomial.C (order+2)))+7)+2

theorem polynomial_bounds (order population count security : ℕ) (hc : count ≤ order)
    (P : Polynomial ℕ) (hP : population ≤ P.eval security) :
    HeightBound (current population count).data.decode ((heightPolynomial order P).eval security) ∧
      (current population count).work ≤ (workPolynomial order P).eval security := by
  have h := current_bounds order population count hc
  constructor
  · apply h.1.mono
    simp only [heightPolynomial, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C]
    calc
      count*(population+order+1) ≤ order*(P.eval security+order+1) := by gcongr
      _ = _ := by ac_rfl
  · apply h.2.trans
    have hs := stepWork_mono order hP
    have hh := Nat.add_le_add_right (Nat.mul_le_mul hc hs) 2
    apply hh.trans_eq
    simp only [workPolynomial, stepWork, primitiveWorkBound, BinaryCalibrationIteration.primitivePolynomial,
      Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_one, Polynomial.eval_ofNat]
    congr 2

end CurrentAFT.BinaryBinomialCoefficient
