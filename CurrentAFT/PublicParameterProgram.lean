import CurrentAFT.Parameters
import AFT.BinaryParameterResources

/-! # Executable current-parameter prime generation

The scan uses the existing explicit unary loop control and Boolean-list
long division. Its defining value is the current least prime, including
the factor `65536` and the non-strict threshold. The work theorem is in
the repository's explicit counter/list-operation model; it is not a
compilation theorem for a Turing machine or for the complete sampler.
-/
namespace CurrentAFT.PublicParameterProgram
open AFT.BinaryArithmetic AFT.ParameterProgram Polynomial
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.primeThreshold
attribute [local irreducible] addCounter powerCounter multiplyCounter doubleCounter boundedLeast

def primeTest (threshold candidate : ℕ) : CountedDecision :=
  let prime := binaryPrimeTest candidate
  let below := lessCounter candidate threshold
  ⟨prime.value && !below.value, prime.work + below.work + 3⟩

theorem primeTest_value (threshold candidate : ℕ) :
    (primeTest threshold candidate).value = true ↔ threshold ≤ candidate ∧ candidate.Prime := by
  simp only [primeTest, Bool.and_eq_true, Bool.not_eq_true_eq_eq_false, binaryPrimeTest_value,
    AFT.ParameterProgram.primeTest_value]
  have hbelow : (lessCounter candidate threshold).value = false ↔ threshold ≤ candidate := by
    constructor
    · intro hfalse
      by_contra hsmall
      have htrue := (lessCounter_value candidate threshold).mpr (Nat.lt_of_not_ge hsmall)
      rw [hfalse] at htrue
      cases htrue
    · intro hlower
      apply Bool.eq_false_iff.mpr
      intro htrue
      have hlt := (lessCounter_value candidate threshold).mp htrue
      omega
  rw [hbelow, and_comm]

def testWork (threshold candidate : ℕ) : ℕ :=
  binaryPrimeWork candidate + 3 * (candidate + threshold) + 5

theorem primeTest_work (threshold candidate : ℕ) :
    (primeTest threshold candidate).work ≤ testWork threshold candidate := by
  have hp := binaryPrimeTest_work candidate
  have hl := lessCounter_work candidate threshold
  unfold primeTest testWork
  dsimp only
  omega

theorem testWork_mono {threshold candidate larger : ℕ} (h : candidate ≤ larger) :
    testWork threshold candidate ≤ testWork threshold larger := by
  unfold testWork binaryPrimeWork
  gcongr

/- These checked executable packages keep kernel conversion from running
the very large counter loops while it checks the program's correctness.
Their bodies are the actual previously verified counter algorithms. -/
private opaque checkedPower (base exponent : ℕ) :
    {result : UnaryCounterResult // result.count = base^exponent ∧ result.work ≤ powerCounterWork base exponent} :=
  ⟨powerCounter base exponent, powerCounter_value base exponent, powerCounter_work base exponent⟩

private opaque checkedProduct (first second : ℕ) :
    {result : UnaryCounterResult // result.count = first*second ∧ result.work = first*(2*second+3)+1} :=
  ⟨multiplyCounter first second, multiplyCounter_value first second, multiplyCounter_work first second⟩

private opaque checkedScan (test : ℕ → CountedDecision) (bound : ℕ) :
    {result : AFT.BetaReference.CountedNatural // result = boundedLeast test bound} :=
  ⟨boundedLeast test bound, rfl⟩

private theorem checkedPower_count (base exponent : ℕ) : (checkedPower base exponent).val.count = base^exponent :=
  (checkedPower base exponent).property.1

private theorem checkedProduct_count (first second : ℕ) : (checkedProduct first second).val.count = first*second :=
  (checkedProduct first second).property.1

private theorem checkedScan_value (test : ℕ → CountedDecision) (bound : ℕ) :
    (checkedScan test bound).val.value = (boundedLeast test bound).value :=
  congrArg AFT.BetaReference.CountedNatural.value (checkedScan test bound).property

theorem scan_exact (security cutoff bound : ℕ) (hcutoff : cutoff = Parameters.primeThreshold security)
    (hbound : Parameters.modulus security ≤ bound) :
    (boundedLeast (primeTest cutoff) bound).value = Parameters.modulus security := by
  apply boundedLeast_exact (primeTest cutoff) (Parameters.modulus security) bound
  · apply (primeTest_value _ _).mpr
    rw [hcutoff]
    exact Parameters.modulus_spec security
  · intro candidate hsmall
    apply Bool.eq_false_iff.mpr
    intro htrue
    have hc := (primeTest_value _ _).mp htrue
    have hthreshold : Parameters.primeThreshold security ≤ candidate := hcutoff ▸ hc.1
    exact (not_le_of_gt hsmall) (Parameters.modulus_least security candidate hthreshold hc.2)
  · exact hbound

/-- All numeric loop bounds are computed by actual counter programs.
The scan itself is structurally recursive on its computed unary bound. -/
def modulus (security : ℕ) : UnaryCounterResult :=
  let base := addCounter security 2
  let power := (checkedPower base.count 64).val
  let threshold := (checkedProduct 65536 power.count).val
  let upper := doubleCounter threshold.count
  let found := (checkedScan (primeTest threshold.count) upper.count).val
  ⟨found.value, base.work + power.work + threshold.work + upper.work + found.work + 6⟩

theorem modulus_value (security : ℕ) : (modulus security).count = Parameters.modulus security := by
  have hthreshold : 65536 * (security + 2)^64 = Parameters.primeThreshold security := by
    simp only [Parameters.primeThreshold_eq, Parameters.base]
  let base := addCounter security 2
  let power := (checkedPower base.count 64).val
  let cutoff := (checkedProduct 65536 power.count).val
  let upper := doubleCounter cutoff.count
  have hc : cutoff.count = Parameters.primeThreshold security := by
    exact ((checkedProduct 65536 power.count).property.1).trans
      ((congrArg (fun value => 65536 * value) ((checkedPower base.count 64).property.1)).trans
        ((congrArg (fun value => 65536 * value^64) (addCounter_value security 2)).trans hthreshold))
  have hu : Parameters.modulus security ≤ upper.count := by
    change _ ≤ (doubleCounter cutoff.count).count
    rw [doubleCounter_value, hc]
    exact Parameters.modulus_upper security
  change (checkedScan (primeTest cutoff.count) upper.count).val.value = _
  exact (checkedScan_value _ _).trans (scan_exact security cutoff.count upper.count hc hu)

def workBound (security : ℕ) : ℕ :=
  let base := security + 2
  let threshold := 65536 * base^64
  2 * security + 1 + powerCounterWork base 64 +
    (65536 * (2 * base^64 + 3) + 1) + (3 * threshold + 1) +
      2 * threshold * (testWork threshold (2 * threshold) + 1) + 6

theorem modulus_work (security : ℕ) : (modulus security).work ≤ workBound security := by
  let base := addCounter security 2
  let power := (checkedPower base.count 64).val
  let cutoff := (checkedProduct 65536 power.count).val
  let upper := doubleCounter cutoff.count
  let found := (checkedScan (primeTest cutoff.count) upper.count).val
  have hb : base.count = security + 2 := addCounter_value security 2
  have hp : power.count = (security + 2)^64 := ((checkedPower base.count 64).property.1).trans (congrArg (·^64) hb)
  have hc : cutoff.count = 65536 * (security+2)^64 := ((checkedProduct 65536 power.count).property.1).trans (congrArg (65536 * ·) hp)
  have hu : upper.count = 2 * (65536 * (security+2)^64) := (doubleCounter_value cutoff.count).trans (congrArg (2 * ·) hc)
  have hbase : base.work = 2*security+1 := addCounter_work security 2
  have hpower : power.work ≤ powerCounterWork (security+2) 64 := by
    exact ((checkedPower base.count 64).property.2).trans_eq (congrArg (fun value => powerCounterWork value 64) hb)
  have hcutoff : cutoff.work = 65536 * (2*(security+2)^64+3)+1 := by
    exact ((checkedProduct 65536 power.count).property.2).trans (congrArg (fun value => 65536*(2*value+3)+1) hp)
  have hupper : upper.work = 3*(65536*(security+2)^64)+1 :=
    (doubleCounter_work cutoff.count).trans (congrArg (fun value => 3*value+1) hc)
  have hscan : found.work ≤ upper.count * (testWork cutoff.count upper.count + 1) := by
    dsimp only [found]
    rw [(checkedScan _ _).property]
    exact boundedLeast_work_le _ _ _ (fun candidate hcandidate =>
      (primeTest_work cutoff.count candidate).trans (testWork_mono hcandidate))
  rw [hc, hu] at hscan
  change base.work + power.work + cutoff.work + upper.work + found.work + 6 ≤ _
  unfold workBound
  dsimp only
  omega

noncomputable def workPolynomial : Polynomial ℕ :=
  let base := X + 2
  let threshold := 65536 * base^64
  2 * X + 1 + 65 * (6 * (base + 1)^66 + 4) +
    (65536 * (2 * base^64 + 3) + 1) + (3 * threshold + 1) +
      2 * threshold * (binaryPrimeWorkPolynomial (2 * threshold) +
        3 * (2 * threshold + threshold) + 6) + 6

theorem workPolynomial_eval (security : ℕ) : workPolynomial.eval security = workBound security := by
  simp only [workPolynomial, workBound, testWork, binaryPrimeWorkPolynomial,
    binaryPrimeWork, powerCounterWork, eval_add, eval_mul, eval_pow, eval_ofNat, eval_X]
  norm_num
  omega

/-- A single executable program works at every security parameter. The
polynomial is a proved cost bound, not an input certificate or oracle. -/
theorem modulus_polynomial_work (security : ℕ) :
    (modulus security).work ≤ workPolynomial.eval security := by
  rw [workPolynomial_eval]
  exact modulus_work security

end CurrentAFT.PublicParameterProgram
