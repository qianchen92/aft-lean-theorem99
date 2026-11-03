import AFT.Parameters
import AFT.BetaCountedSearch

/-! # A bounded executable search for the actual public prime modulus

The program uses trial division and a bounded scan. Its arithmetic counter
is deliberately coarse; no primality oracle is supplied to the executable
program. The result is exactly the prime selected in `Parameters.modulus`.
-/
namespace AFT.ParameterProgram
open BetaReference

structure CountedDecision where
  value : Bool
  work : ℕ

/-- Test divisors `2,...,length+1` by literal natural remainders. -/
def trialDivisors (candidate : ℕ) : ℕ → CountedDecision
  | 0 => ⟨true,0⟩
  | length+1 =>
      let previous := trialDivisors candidate length
      let remainder := candidate%(length+2)
      ⟨previous.value && decide (remainder ≠ 0),previous.work+2⟩

theorem trialDivisors_value (candidate length : ℕ) :
    (trialDivisors candidate length).value=true ↔
      ∀ d,2 ≤ d → d < length+2 → ¬d ∣ candidate := by
  induction length with
  | zero =>
    simp only [trialDivisors]
    constructor
    · intro _ d hlo hhi
      omega
    · intro _
      trivial
  | succ length ih =>
    simp only [trialDivisors,Bool.and_eq_true,decide_eq_true_eq,ih]
    constructor
    · rintro ⟨hprev,hlast⟩ d hlo hhi
      by_cases h : d < length+2
      · exact hprev d hlo h
      · have he : d=length+2 := by omega
        rw [he,Nat.dvd_iff_mod_eq_zero]
        exact hlast
    · intro h
      exact ⟨fun d hlo hhi => h d hlo (by omega),by simpa only [Nat.dvd_iff_mod_eq_zero] using h (length+2) (by omega) (by omega)⟩

@[simp] theorem trialDivisors_work (candidate length : ℕ) :
    (trialDivisors candidate length).work=2*length := by
  induction length with
  | zero => rfl
  | succ length ih => simp only [trialDivisors,ih]; omega

def primeTest (candidate : ℕ) : CountedDecision :=
  if candidate < 2 then ⟨false,1⟩ else
    let result := trialDivisors candidate (candidate-2)
    ⟨result.value,result.work+2⟩

theorem primeTest_value (candidate : ℕ) :
    (primeTest candidate).value=true ↔ candidate.Prime := by
  rw [Nat.prime_def_lt']
  by_cases h : candidate < 2
  · simp only [primeTest,if_pos h,Bool.false_eq_true,false_iff]
    omega
  · simp only [primeTest,if_neg h,trialDivisors_value]
    have he : candidate-2+2=candidate := by omega
    rw [he]
    exact (and_iff_right (by omega : 2 ≤ candidate)).symm

theorem primeTest_work_le (candidate : ℕ) :
    (primeTest candidate).work ≤ 2*candidate+2 := by
  simp only [primeTest]
  split_ifs <;> simp only [trialDivisors_work] <;> omega

/-- The scan is structurally recursive on the declared finite upper bound.
After finding a witness it retains that same least witness. -/
def boundedLeast (test : ℕ → CountedDecision) : ℕ → CountedNatural
  | 0 => ⟨0,0⟩
  | bound+1 =>
      let previous := boundedLeast test bound
      let checked := test previous.value
      ⟨if checked.value then previous.value else bound+1,previous.work+checked.work+1⟩

theorem boundedLeast_le (test : ℕ → CountedDecision) (bound : ℕ) :
    (boundedLeast test bound).value ≤ bound := by
  induction bound with
  | zero => simp [boundedLeast]
  | succ bound ih => simp only [boundedLeast]; split_ifs <;> omega

theorem boundedLeast_exact (test : ℕ → CountedDecision) (least bound : ℕ)
    (hleast : (test least).value=true)
    (hminimal : ∀ index,index < least → (test index).value=false)
    (hbound : least ≤ bound) : (boundedLeast test bound).value=least := by
  induction bound with
  | zero =>
    have he : least=0 := by omega
    simp only [he,boundedLeast]
  | succ bound ih =>
    by_cases h : least ≤ bound
    · simp only [boundedLeast,ih h,hleast,ite_true]
    · have he : least=bound+1 := by omega
      have hp := boundedLeast_le test bound
      have ht := hminimal (boundedLeast test bound).value (by omega)
      simp only [boundedLeast,ht,Bool.false_eq_true,ite_false,he]

theorem boundedLeast_work_le (test : ℕ → CountedDecision) (bound cost : ℕ)
    (hcost : ∀ index,index ≤ bound → (test index).work ≤ cost) :
    (boundedLeast test bound).work ≤ bound*(cost+1) := by
  induction bound with
  | zero => simp [boundedLeast]
  | succ bound ih =>
    have hp := ih (fun index hi => hcost index (by omega))
    have hq := hcost (boundedLeast test bound).value ((boundedLeast_le test bound).trans (by omega))
    simp only [boundedLeast]
    nlinarith

/-- Every tested property is evaluated from integer operations. -/
def modulusTest (base candidate : ℕ) : CountedDecision :=
  let prime := primeTest candidate
  ⟨prime.value && decide (base < candidate) && decide (candidate ≤ 2*base),prime.work+3⟩

theorem modulusTest_value (base candidate : ℕ) :
    (modulusTest base candidate).value=true ↔
      candidate.Prime ∧ base < candidate ∧ candidate ≤ 2*base := by
  simp only [modulusTest,Bool.and_eq_true,decide_eq_true_eq,primeTest_value,and_assoc]

def modulus (parameter : ℕ) : CountedNatural :=
  let base := CountedInteger.power ((max 2 parameter : ℕ) : ℤ) 40
  let result := boundedLeast (modulusTest base.value.toNat) (2*base.value.toNat)
  ⟨result.value,base.work+result.work+2⟩

private theorem base_value (parameter : ℕ) :
    (CountedInteger.power ((max 2 parameter : ℕ) : ℤ) 40).value.toNat=Parameters.security parameter^40 := by
  rw [CountedInteger.power_value]
  have hh : ((max 2 parameter : ℕ) : ℤ)^40=((max 2 parameter)^40 : ℕ) := by push_cast; rfl
  rw [hh,Int.toNat_natCast]
  rfl

theorem modulus_value (parameter : ℕ) : (modulus parameter).value=Parameters.modulus parameter := by
  simp only [modulus,base_value]
  apply boundedLeast_exact
  · exact (modulusTest_value _ _).mpr (Parameters.modulus_spec parameter)
  · intro index hi
    apply Bool.eq_false_iff.mpr
    intro ht
    have hs := (modulusTest_value _ _).mp ht
    have hmin : Parameters.modulus parameter ≤ index := by
      unfold Parameters.modulus
      exact Nat.find_min' _ hs
    omega
  · exact (Parameters.modulus_bounds parameter).2

/-- The public-prime scan, including its trial divisions, has a concrete
polynomial arithmetic-operation budget in the security parameter. -/
theorem modulus_work_le (parameter : ℕ) :
    (modulus parameter).work ≤ 100*Parameters.security parameter^80 := by
  let base := Parameters.security parameter^40
  have hb : 1 ≤ base := by dsimp [base]; exact Nat.one_le_pow _ _ (by have := Parameters.security_ge_two parameter; omega)
  have hcost : ∀ index,index ≤ 2*base → (modulusTest base index).work ≤ 4*base+5 := by
    intro index hi
    have hh := primeTest_work_le index
    simp only [modulusTest]
    omega
  have hs := boundedLeast_work_le (modulusTest base) (2*base) (4*base+5) hcost
  simp only [modulus,base_value,CountedInteger.power_work]
  have he : Parameters.security parameter^80=base^2 := by dsimp [base]; rw [← pow_mul]
  rw [he]
  change 40+(boundedLeast (modulusTest base) (2*base)).work+2 ≤ 100*base^2
  nlinarith

end AFT.ParameterProgram
