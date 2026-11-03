import AFT.CanonicalSmoothing

/-! Exact finite equivalence transport for joint mass profiles and core seeds. -/

namespace CurrentAFT.PairReindex

open AFT AFT.SafePair AFT.SafeConvolution
open scoped BigOperators Classical

noncomputable section

variable {First Second : Type*} [Fintype First] [Fintype Second]

def liftPair (equiv : First ≃ Second) (profile : First → First → ℝ) : Second → Second → ℝ :=
  fun first second => profile (equiv.symm first) (equiv.symm second)

theorem liftPair_first_sum (equiv : First ≃ Second) (profile : First → First → ℝ) (second : Second) :
    (∑ first, liftPair equiv profile first second) = ∑ first, profile first (equiv.symm second) :=
  by
    unfold liftPair
    exact equiv.symm.sum_comp (fun first : First => profile first (equiv.symm second))

theorem liftPair_second_sum (equiv : First ≃ Second) (profile : First → First → ℝ) (first : Second) :
    (∑ second, liftPair equiv profile first second) = ∑ second, profile (equiv.symm first) second :=
  by
    unfold liftPair
    exact equiv.symm.sum_comp (fun second : First => profile (equiv.symm first) second)

theorem liftPair_total (equiv : First ≃ Second) (profile : First → First → ℝ) :
    (∑ first, ∑ second, liftPair equiv profile first second) = ∑ first, ∑ second, profile first second := by
  calc
    _ = ∑ first : Second, ∑ second : First, profile (equiv.symm first) second := by
      apply Finset.sum_congr rfl
      intro first _
      exact liftPair_second_sum equiv profile first
    _ = _ := equiv.symm.sum_comp (fun first : First => ∑ second : First, profile first second)

omit [Fintype First] [Fintype Second] in
theorem liftPair_symmetric (equiv : First ≃ Second) (profile : First → First → ℝ)
    (hsymmetric : ∀ first second, profile first second = profile second first) (first second : Second) :
    liftPair equiv profile first second = liftPair equiv profile second first :=
  hsymmetric (equiv.symm first) (equiv.symm second)

theorem liftPair_countingL2 (equiv : First ≃ Second) (profile : First → First → ℝ) :
    pairCountingL2 (liftPair equiv profile) = pairCountingL2 profile := by
  unfold pairCountingL2 countingL2
  congr 1
  simpa only [Fintype.sum_prod_type, liftPair] using liftPair_total equiv (fun first second => profile first second ^ 2)

variable [DecidableEq First] [DecidableEq Second]

omit [Fintype First] [Fintype Second] [DecidableEq First] [DecidableEq Second] in
theorem mem_map (equiv : First ≃ Second) (core : Finset First) (color : Second) :
    color ∈ core.map equiv.toEmbedding ↔ equiv.symm color ∈ core := by
  constructor
  · intro h
    obtain ⟨first, hfirst, heq⟩ := Finset.mem_map.mp h
    simpa only [← heq, Equiv.coe_toEmbedding, Equiv.symm_apply_apply] using hfirst
  · intro h
    exact Finset.mem_map.mpr ⟨equiv.symm color, h, equiv.apply_symm_apply color⟩

omit [Fintype First] [Fintype Second] in
theorem uniformFiniteProfile_map (equiv : First ≃ Second) (core : Finset First) (color : Second) :
    uniformFiniteProfile (core.map equiv.toEmbedding) color = uniformFiniteProfile core (equiv.symm color) := by
  simp only [uniformFiniteProfile, mem_map, Finset.card_map]

omit [Fintype First] [Fintype Second] in
theorem restrictPair_map (equiv : First ≃ Second) (core : Finset First) (profile : First → First → ℝ) :
    restrictPair (core.map equiv.toEmbedding) (liftPair equiv profile) = liftPair equiv (restrictPair core profile) := by
  funext first second
  simp only [restrictPair, mem_map, liftPair]

omit [DecidableEq First] [DecidableEq Second] in
theorem canonicalPair_lift (equiv : First ≃ Second) (reference : First → ℝ) (profile : First → First → ℝ) :
    canonicalPair (reference ∘ equiv.symm) (liftPair equiv profile) = liftPair equiv (canonicalPair reference profile) := by
  funext first second
  simp only [canonicalPair, Function.comp_apply]
  rw [liftPair_first_sum, liftPair_second_sum, liftPair_total]
  rfl

theorem coreSeed_map (equiv : First ≃ Second) (core : Finset First) (profile : First → First → ℝ) :
    coreSeed (core.map equiv.toEmbedding) (liftPair equiv profile) = liftPair equiv (coreSeed core profile) := by
  unfold coreSeed
  rw [restrictPair_map]
  have href : uniformFiniteProfile (core.map equiv.toEmbedding) = uniformFiniteProfile core ∘ equiv.symm :=
    funext (uniformFiniteProfile_map equiv core)
  rw [href, canonicalPair_lift]

omit [DecidableEq First] [DecidableEq Second] in
theorem canonicalPair_uniform_lift (equiv : First ≃ Second) (profile : First → First → ℝ) :
    canonicalPair (fun _ => 1 / (Fintype.card Second : ℝ)) (liftPair equiv profile) =
      liftPair equiv (canonicalPair (fun _ => 1 / (Fintype.card First : ℝ)) profile) := by
  simpa only [Fintype.card_congr equiv, Function.comp_def] using
    canonicalPair_lift equiv (fun _ : First => 1 / (Fintype.card First : ℝ)) profile

omit [DecidableEq First] [DecidableEq Second] in
theorem liftPair_difference_countingL2 (equiv : First ≃ Second)
    (first second : First → First → ℝ) :
    pairCountingL2 (liftPair equiv first - liftPair equiv second) = pairCountingL2 (first - second) :=
  liftPair_countingL2 equiv (first - second)

omit [DecidableEq First] [DecidableEq Second] in
theorem liftPair_uniform_error_countingL2 (equiv : First ≃ Second)
    (seed mass : First → First → ℝ) :
    pairCountingL2 (liftPair equiv seed -
      canonicalPair (fun _ => 1 / (Fintype.card Second : ℝ)) (liftPair equiv mass)) =
    pairCountingL2 (seed - canonicalPair (fun _ => 1 / (Fintype.card First : ℝ)) mass) := by
  rw [canonicalPair_uniform_lift]
  exact liftPair_difference_countingL2 equiv seed _

end

end CurrentAFT.PairReindex
