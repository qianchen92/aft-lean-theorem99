import AFT.ProfileHilbert

/-! # Finite Hilbert means and exact centering identities -/

namespace AFT.FiniteConcentration

open scoped BigOperators Classical

noncomputable section

variable {Sample Queue Index Hilbert : Type*} [Fintype Sample] [Fintype Queue] [Fintype Index]
  [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]

omit [Fintype Queue] [Fintype Index] in
theorem vectorMean_const (law : FiniteDist Sample) (value : Hilbert) :
    vectorMean law (fun _ => value) = value := by
  simp only [vectorMean, ← Finset.sum_smul, law.sum_one, one_smul]

omit [Fintype Queue] [Fintype Index] in
theorem vectorMean_add (law : FiniteDist Sample) (first second : Sample → Hilbert) :
    vectorMean law (fun sample => first sample + second sample) =
      vectorMean law first + vectorMean law second := by
  simp only [vectorMean, smul_add, Finset.sum_add_distrib]

omit [Fintype Queue] [Fintype Index] in
theorem vectorMean_sub (law : FiniteDist Sample) (first second : Sample → Hilbert) :
    vectorMean law (fun sample => first sample - second sample) =
      vectorMean law first - vectorMean law second := by
  simp only [vectorMean, smul_sub, Finset.sum_sub_distrib]

omit [Fintype Queue] [Fintype Index] in
theorem vectorMean_smul (law : FiniteDist Sample) (value : Sample → Hilbert) (scalar : ℝ) :
    vectorMean law (fun sample => scalar • value sample) = scalar • vectorMean law value := by
  simp only [vectorMean, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro sample _
  rw [mul_comm]

omit [Fintype Queue] in
theorem vectorMean_sum (law : FiniteDist Sample) (value : Index → Sample → Hilbert) :
    vectorMean law (fun sample => ∑ index, value index sample) =
      ∑ index, vectorMean law (value index) := by
  simp only [vectorMean, Finset.smul_sum]
  rw [Finset.sum_comm]

omit [Fintype Index] in
theorem vectorMean_comm (first : FiniteDist Sample) (second : FiniteDist Queue)
    (value : Sample → Queue → Hilbert) :
    vectorMean first (fun sample => vectorMean second (value sample)) =
      vectorMean second (fun queue => vectorMean first (fun sample => value sample queue)) := by
  simp only [vectorMean, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro queue _
  apply Finset.sum_congr rfl
  intro sample _
  rw [mul_comm]

omit [Fintype Queue] [Fintype Index] in
/-- Any fixed deterministic centering disappears upon recentering by the
actual conditioned mean. -/
theorem recenter_sub_const (law : FiniteDist Sample) (value : Sample → Hilbert)
    (constant : Hilbert) (sample : Sample) :
    (value sample - constant) - vectorMean law (fun sample => value sample - constant) =
      value sample - vectorMean law value := by
  rw [vectorMean_sub, vectorMean_const]
  abel

omit [Fintype Index] in
/-- A mean-zero mixture whose queue realizations move at most `bound` from
one common baseline has conditional means bounded by `2 * bound`. -/
theorem mean_le_twice_displacement (root : FiniteDist Sample) (queue : FiniteDist Queue)
    (value : Sample → Queue → Hilbert) (baseline : Sample → Hilbert) (bound : ℝ)
    (hmean : vectorMean queue (fun q => vectorMean root (fun sample => value sample q)) = 0)
    (hmove : ∀ sample q, ‖value sample q - baseline sample‖ ≤ bound) (q : Queue) :
    ‖vectorMean root (fun sample => value sample q)‖ ≤ 2 * bound := by
  have hrepr : vectorMean queue (fun other =>
      vectorMean root (fun sample => value sample q - value sample other)) =
      vectorMean root (fun sample => value sample q) := by
    simp only [vectorMean_sub, vectorMean_const, hmean, sub_zero]
  rw [← hrepr]
  apply vectorMean_norm_le
  intro other
  apply vectorMean_norm_le
  intro sample
  calc
    _ = ‖(value sample q - baseline sample) - (value sample other - baseline sample)‖ := by congr 1; abel
    _ ≤ ‖value sample q - baseline sample‖ + ‖value sample other - baseline sample‖ := norm_sub_le _ _
    _ ≤ 2 * bound := by linarith [hmove sample q, hmove sample other]

end

end AFT.FiniteConcentration
