import AFT.BetaCountedSearch

/-! # A counted fair-bit beta program with a rational output pair

The output is an unreduced pair of natural integers. This avoids requiring
rational arithmetic for the final typical-value check.
-/
namespace AFT.BetaReference
open scoped BigOperators

namespace CountedNatural

/-- Read the little-endian ticket, computing each binary place by the
same counted repeated-multiplication evaluator. -/
def bitTicket : (bits : ℕ) → (Fin bits → Fin 2) → CountedNatural
  | 0, _ => ⟨0,0⟩
  | bits+1, word =>
      let earlier := bitTicket bits (fun i => word i.castSucc)
      let place := CountedInteger.power 2 bits
      ⟨earlier.value+(word (Fin.last bits)).val*place.value.toNat,
        earlier.work+place.work+2⟩

theorem bitTicket_value (bits : ℕ) (word : Fin bits → Fin 2) :
    (bitTicket bits word).value=(FiniteTicketSampler.bitTicket bits word).val := by
  rw [FiniteTicketSampler.bitTicket_value]
  induction bits with
  | zero => simp [bitTicket]
  | succ bits ih =>
    simp only [bitTicket,CountedInteger.power_value,
      Int.toNat_pow_of_nonneg (by norm_num : 0 ≤ (2 : ℤ))]
    rw [Fin.sum_univ_castSucc]
    rw [show (2 : ℤ).toNat=2 from rfl]
    congr 1
    simpa only [Fin.val_castSucc] using ih (fun i => word i.castSucc)

theorem bitTicket_work_le (bits : ℕ) (word : Fin bits → Fin 2) :
    (bitTicket bits word).work ≤ bits*(bits+2) := by
  induction bits with
  | zero => simp [bitTicket]
  | succ bits ih =>
    simp only [bitTicket,CountedInteger.power_work]
    have hh := ih (fun i => word i.castSucc)
    nlinarith

end CountedNatural

structure CountedFraction where
  numerator : ℕ
  denominator : ℕ
  work : ℕ

namespace CountedFraction

def value (result : CountedFraction) : ℚ := result.numerator/result.denominator

/-- Exactly one addition, six multiplications, and two comparisons determine
whether the rational grid point is typical. The result needs no division. -/
def safePoint (N K M index : ℕ) : CountedFraction :=
  let point := index+1
  let lowerLeft := K*M
  let lowerRight := (2*N)*point
  let upperLeft := point*N
  let upperRight := (2*K)*M
  if lowerLeft ≤ lowerRight ∧ upperLeft ≤ upperRight then ⟨point,M,9⟩ else ⟨K,N,9⟩

@[simp] theorem safePoint_work (N K M index : ℕ) : (safePoint N K M index).work=9 := by
  simp only [safePoint]
  split_ifs <;> rfl

theorem safePoint_value (N K M : ℕ) (hN : 0 < N) (hM : 0 < M) (index : Fin M) :
    (safePoint N K M index.val).value=safeGridValue N K M index := by
  have hNr : (0 : ℚ) < N := by exact_mod_cast hN
  have hMr : (0 : ℚ) < M := by exact_mod_cast hM
  have hc : K*M ≤ (2*N)*(index.val+1) ∧ (index.val+1)*N ≤ (2*K)*M ↔
      (K : ℚ)/(2*N) ≤ ((index.val+1 : ℕ) : ℚ)/M ∧
      ((index.val+1 : ℕ) : ℚ)/M ≤ 2*(K : ℚ)/N := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℚ) < 2*N) hMr,
      div_le_div_iff₀ hMr hNr]
    norm_cast
    constructor <;> intro h <;> constructor <;> nlinarith [h.1,h.2]
  simp only [safePoint,safeGridValue,value]
  by_cases h : K*M ≤ (2*N)*(index.val+1) ∧ (index.val+1)*N ≤ (2*K)*M
  · simp only [if_pos h,if_pos (hc.mp h)]
  · simp only [if_neg h,if_neg ((not_congr hc).mp h)]

/-- The full executable beta routine takes exactly the supplied `bits`
binary values. Computing the beta shape costs the two natural subtractions. -/
def beta (N K depth bits : ℕ) (word : Fin bits → Fin 2) : CountedFraction :=
  let ticket := CountedNatural.bitTicket bits word
  let result := CountedNatural.betaSearch K (N-K-1) depth bits ticket.value
  let grid := CountedInteger.power 2 depth
  let final := safePoint N K grid.value.toNat result.value
  ⟨final.numerator,final.denominator,ticket.work+result.work+grid.work+final.work+2⟩

theorem beta_value (N K depth bits : ℕ) (hN : 0 < N) (word : Fin bits → Fin 2) :
    (beta N K depth bits word).value=integerSafeDraw N K depth bits word := by
  simp only [beta,value,CountedNatural.betaSearch_value,CountedNatural.bitTicket_value,
    CountedInteger.power_value,Int.toNat_pow_of_nonneg (by norm_num : 0 ≤ (2 : ℤ))]
  change (safePoint N K (2^depth) (integerDraw K (N-K-1) depth bits word).val).value=_
  exact safePoint_value N K (2^depth) hN (by positivity) _

theorem beta_work_le (N K depth bits : ℕ) (word : Fin bits → Fin 2) :
    (beta N K depth bits word).work ≤
      bits*(bits+2)+2*depth+depth*(18*(K+(N-K-1)+1)^2+bits+depth+2)+11 := by
  have ht := CountedNatural.bitTicket_work_le bits word
  have hs := CountedNatural.betaSearch_work_le K (N-K-1) depth bits
    (CountedNatural.bitTicket bits word).value
  simp only [beta,CountedInteger.power_work,safePoint_work]
  omega

end CountedFraction
end AFT.BetaReference
