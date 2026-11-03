import AFT.BetaFiniteSampler

/-! # A bounded-time beta sample with rational typical-value fallback -/
namespace AFT.BetaReference

/-- Both the grid and its fallback are rational and are computed by finite
arithmetic. No ideal real-valued sample or unbounded rejection is used. -/
def safeGridValue (N K M : ℕ) (j : Fin M) : ℚ :=
  let value : ℚ := (j.val+1 : ℕ)/M
  if (K : ℚ)/(2*N) ≤ value ∧ value ≤ 2*(K : ℚ)/N then value else (K : ℚ)/N

theorem safeGridValue_typical (N K M : ℕ) (j : Fin M) :
    (K : ℚ)/(2*N) ≤ safeGridValue N K M j ∧ safeGridValue N K M j ≤ 2*(K : ℚ)/N := by
  unfold safeGridValue
  dsimp only
  split_ifs with h
  · exact h
  · have hk : (0 : ℚ) ≤ (K : ℚ)/N := by positivity
    have he : (K : ℚ)/(2*N)=((K : ℚ)/N)/2 := by ring
    rw [he]
    constructor <;> linarith [show 2*(K : ℚ)/N=2*((K : ℚ)/N) by ring]

theorem safeGridValue_real_typical (N K M : ℕ) (j : Fin M) :
    (K : ℝ)/(2*N) ≤ (safeGridValue N K M j : ℝ) ∧
      (safeGridValue N K M j : ℝ) ≤ 2*(K : ℝ)/N := by
  have ht := safeGridValue_typical N K M j
  constructor
  · simpa only [Rat.cast_div,Rat.cast_mul,Rat.cast_natCast,Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).mpr ht.1
  · simpa only [Rat.cast_div,Rat.cast_mul,Rat.cast_natCast,Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).mpr ht.2

theorem safeGridValue_real_eq (N K M : ℕ) (j : Fin M)
    (h : (K : ℝ)/(2*N) ≤ ((j.val+1 : ℕ) : ℝ)/M ∧
      ((j.val+1 : ℕ) : ℝ)/M ≤ 2*(K : ℝ)/N) :
    (safeGridValue N K M j : ℝ)=((j.val+1 : ℕ) : ℝ)/M := by
  have hh : (K : ℚ)/(2*N) ≤ ((j.val+1 : ℕ) : ℚ)/M ∧
      ((j.val+1 : ℕ) : ℚ)/M ≤ 2*(K : ℚ)/N := by
    constructor
    · apply (Rat.cast_le (K:=ℝ)).mp
      simpa only [Rat.cast_div,Rat.cast_mul,Rat.cast_natCast,Rat.cast_ofNat] using h.1
    · apply (Rat.cast_le (K:=ℝ)).mp
      simpa only [Rat.cast_div,Rat.cast_mul,Rat.cast_natCast,Rat.cast_ofNat] using h.2
  simp only [safeGridValue,if_pos hh,Rat.cast_div,Rat.cast_natCast]

/-- The entire beta routine is a deterministic function of exactly `bits`
fair bits, followed by a finite rational interval test. -/
def safeFiniteDraw (N K depth bits : ℕ) (word : Fin bits → Fin 2) : ℚ :=
  safeGridValue N K (2^depth) (finiteDraw K (N-K-1) depth bits word)

theorem safeFiniteDraw_typical (N K depth bits : ℕ) (word : Fin bits → Fin 2) :
    (K : ℚ)/(2*N) ≤ safeFiniteDraw N K depth bits word ∧
      safeFiniteDraw N K depth bits word ≤ 2*(K : ℚ)/N :=
  safeGridValue_typical N K (2^depth) _

end AFT.BetaReference
