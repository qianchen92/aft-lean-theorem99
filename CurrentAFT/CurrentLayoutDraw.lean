import CurrentAFT.CurrentCorePolynomialWork
import CurrentAFT.CurrentPermutationCache

/-! An independently sampled placement, retained outside the rejection loop.
A canonical role numbering is followed by the same executed finite permutation
program; its two directions remain cached. -/
namespace CurrentAFT.CurrentLayoutDraw
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
open CurrentProposalDimensions CurrentProposalResources
open ActualCycleMeanMGF ConditionalHistogramMean
open scoped BigOperators Polynomial
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
attribute [local irreducible] Parameters.bodySize Parameters.legCount CurrentProposalDimensions.current


def canonicalLayout (security : ℕ) : RoleIndex security ≃ BodyIndex security :=
  ((Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv).trans (finCongr (by
    have h := ProposalPrimary.population_room security
    unfold BackgroundPopulationBounds.freeCount
    omega))

abbrev Cache (security : ℕ) := CurrentPermutationDraw.CachedPermutation (current security).body
abbrev Tape (security bits : ℕ) := Fin ((current security).body * bits) → Fin 2

def draw (security bits : ℕ) (word : Tape security bits) : CountedValue (Cache security) :=
  let result := CurrentPermutationDraw.draw (current security).body bits (Vector.ofFn word)
  ⟨result.value, (current security).work + result.work + (current security).body * bits + 2⟩

def Cache.layout {security : ℕ} (cache : Cache security) : RoleIndex security ≃ BodyIndex security :=
  (canonicalLayout security).trans ((bodyEquiv security).permCongr cache.toEquiv)

noncomputable section
open scoped Classical
local instance layoutNonempty (security : ℕ) : Nonempty (RoleIndex security ≃ BodyIndex security) :=
  ⟨canonicalLayout security⟩

def placementEquiv (security : ℕ) : Equiv.Perm (BodyIndex security) ≃ (RoleIndex security ≃ BodyIndex security) where
  toFun permutation := (canonicalLayout security).trans permutation
  invFun layout := (canonicalLayout security).symm.trans layout
  left_inv _ := by ext index; simp
  right_inv _ := by ext index; simp

def law (security bits : ℕ) : FiniteDist (RoleIndex security ≃ BodyIndex security) :=
  (FiniteDist.uniform (Tape security bits)).map (fun word => Cache.layout (draw security bits word).value)

theorem law_eq (security bits : ℕ) : law security bits =
    (CurrentPermutationDraw.law (current security).body bits).map
      (((bodyEquiv security).permCongr).trans (placementEquiv security)) := by
  unfold law CurrentPermutationDraw.law
  rw [FiniteDist.map_map]
  rfl

theorem law_l1 (security bits : ℕ) :
    (∑ layout, |(law security bits).weight layout -
      (FiniteDist.uniform (RoleIndex security ≃ BodyIndex security)).weight layout|) ≤
      2 * ((current security).body : ℝ)^2 / (2 : ℝ)^bits := by
  rw [law_eq]
  have h := FiniteDist.l1_map_le (CurrentPermutationDraw.law (current security).body bits)
    (FiniteDist.uniform (Equiv.Perm (Fin (current security).body)))
    (((bodyEquiv security).permCongr).trans (placementEquiv security))
  rw [FiniteDist.uniform_map_equiv] at h
  exact h.trans (CurrentPermutationDraw.law_l1 (current security).body bits)

noncomputable def workPolynomial (bits : Polynomial ℕ) : Polynomial ℕ :=
  metadataWorkPolynomial + CurrentCorePolynomialWork.permutationPolynomial bits + countPolynomial * bits + 2

theorem polynomial_work (security : ℕ) (bits : Polynomial ℕ) (word : Tape security (bits.eval security)) :
    (draw security (bits.eval security) word).work ≤ (workPolynomial bits).eval security := by
  have hc := (count_bounds security).2.2.2.1
  have hm := metadata_work security
  have hp := (CurrentPermutationDraw.draw_work (current security).body (bits.eval security) (Vector.ofFn word)).trans
    (CurrentCorePolynomialWork.permutation_work security (current security).body bits hc)
  have hb := Nat.mul_le_mul_right (bits.eval security) hc
  change (current security).work + (CurrentPermutationDraw.draw _ _ _).work + (current security).body * bits.eval security + 2 ≤ _
  simp only [workPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
  omega

end
end CurrentAFT.CurrentLayoutDraw
