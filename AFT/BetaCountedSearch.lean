import AFT.BetaCountedArithmetic

/-! # The binary beta search with an executable arithmetic counter

The evaluator recomputes the midpoint power at each level and counts the
query's actual arithmetic evaluator, the midpoint addition, and comparison.
-/
namespace AFT.BetaReference

structure CountedNatural where
  value : ℕ
  work : ℕ

namespace CountedNatural

/-- The query is evaluated once at each level. The branches return the
same checked result structure, so the counter follows the executed path. -/
def locate (query : ℕ → CountedInteger) : ℕ → ℕ → ℕ → CountedNatural
  | 0, lower, _ => ⟨lower,0⟩
  | depth+1, lower, ticket =>
      let midpoint := (CountedInteger.literal lower).add (CountedInteger.power 2 depth)
      let cumulative := query midpoint.value.toNat
      let result := if ticket < cumulative.value.toNat then locate query depth lower ticket
        else locate query depth midpoint.value.toNat ticket
      ⟨result.value,midpoint.work+cumulative.work+result.work+1⟩

private theorem midpoint_value (lower depth : ℕ) :
    ((CountedInteger.literal lower).add (CountedInteger.power 2 depth)).value.toNat=lower+2^depth := by
  simp only [CountedInteger.add,CountedInteger.literal,CountedInteger.power_value]
  have hh : (lower : ℤ)+(2 : ℤ)^depth=((lower+2^depth : ℕ) : ℤ) := by push_cast; rfl
  rw [hh,Int.toNat_natCast]

private theorem midpoint_work (lower depth : ℕ) :
    ((CountedInteger.literal lower).add (CountedInteger.power 2 depth)).work=depth+1 := by
  simp only [CountedInteger.add,CountedInteger.literal,CountedInteger.power_work,Nat.zero_add]

theorem locate_value (query : ℕ → CountedInteger) (depth lower ticket : ℕ) :
    (locate query depth lower ticket).value=
      BinaryCDFSampler.locate (fun a => (query a).value.toNat) depth lower ticket := by
  induction depth generalizing lower with
  | zero => rfl
  | succ depth ih =>
    simp only [locate,midpoint_value,BinaryCDFSampler.locate]
    split_ifs <;> exact ih _

theorem locate_work_le (query : ℕ → CountedInteger) (bound : ℕ)
    (hquery : ∀ a,(query a).work ≤ bound) (depth lower ticket : ℕ) :
    (locate query depth lower ticket).work ≤ depth*(bound+depth+2) := by
  induction depth generalizing lower with
  | zero => simp [locate]
  | succ depth ih =>
    simp only [locate,midpoint_work,midpoint_value]
    split_ifs
    · have hh := ih lower
      have hq := hquery (lower+2^depth)
      nlinarith
    · have hh := ih (lower+2^depth)
      have hq := hquery (lower+2^depth)
      nlinarith

/-- Concrete search, including the arithmetic to construct its grid base.
The input ticket is already an integer extracted from the given fair bits. -/
def betaSearch (K n depth bits ticket : ℕ) : CountedNatural :=
  let grid := CountedInteger.power 2 depth
  let result := locate (CountedInteger.cdfCut K n grid.value.toNat bits) depth 0 ticket
  ⟨result.value,grid.work+result.work⟩

private theorem power_two_toNat (depth : ℕ) :
    (CountedInteger.power 2 depth).value.toNat=2^depth := by
  rw [CountedInteger.power_value,Int.toNat_pow_of_nonneg (by norm_num : 0 ≤ (2 : ℤ))]
  rfl

theorem betaSearch_value (K n depth bits ticket : ℕ) :
    (betaSearch K n depth bits ticket).value=
      BinaryCDFSampler.locate (integerCut K n depth bits) depth 0 ticket := by
  simp only [betaSearch,power_two_toNat,locate_value]
  apply BinaryCDFSampler.locate_congr_on
  intro a _ ha
  rw [CountedInteger.cdfCut_value K n depth bits a (by simpa only [zero_add] using ha),Int.toNat_natCast]

theorem betaSearch_work_le (K n depth bits ticket : ℕ) :
    (betaSearch K n depth bits ticket).work ≤
      depth+depth*(18*(K+n+1)^2+bits+depth+2) := by
  simp only [betaSearch,power_two_toNat,CountedInteger.power_work]
  apply Nat.add_le_add_left
  exact locate_work_le _ _ (fun a => CountedInteger.cdfCut_work_le K n (2^depth) bits a) depth 0 ticket

end CountedNatural
end AFT.BetaReference
