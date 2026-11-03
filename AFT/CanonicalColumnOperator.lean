import AFT.RepresentedCanonical
import AFT.RepresentedLinearActivity

/-! # Extending literal canonical cutoff columns to finite linear response operators -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Color : Type*} [Fintype Color]

/-- The genuine finite response domain, expressed on literal monomials. -/
def CanonicalColumnDomain (primary body : FiniteDist Color)
    (order : InputSeed Color → ℕ) (cutoff : ℕ) (powers : InputSeed Color →₀ ℕ) : Prop :=
  weightedOrder order powers≤cutoff ∧ ∀ seed∈powers.support,
    Hoeffding.Canonical (inputReference primary body seed) Finset.univ seed.kernel

def canonicalRestrictedColumn (primary body : FiniteDist Color)
    (order : InputSeed Color → ℕ) (cutoff : ℕ)
    (columns : (InputSeed Color →₀ ℕ) → Table (InputSeed Color))
    (powers : InputSeed Color →₀ ℕ) : Table (InputSeed Color) :=
  if CanonicalColumnDomain primary body order cutoff powers then truncate order cutoff (columns powers) else 0

def canonicalColumnLinear (primary body : FiniteDist Color)
    (order : InputSeed Color → ℕ) (cutoff : ℕ)
    (columns : (InputSeed Color →₀ ℕ) → Table (InputSeed Color)) :
    Module.End ℝ (Table (InputSeed Color)) :=
  Finsupp.linearCombination ℝ (canonicalRestrictedColumn primary body order cutoff columns)

theorem canonicalColumnLinear_monomial (primary body : FiniteDist Color)
    (order : InputSeed Color → ℕ) (cutoff : ℕ)
    (columns : (InputSeed Color →₀ ℕ) → Table (InputSeed Color))
    (powers : InputSeed Color →₀ ℕ) (scalar : ℝ)
    (h : CanonicalColumnDomain primary body order cutoff powers) :
    canonicalColumnLinear primary body order cutoff columns (MvPolynomial.monomial powers scalar)=
      scalar • truncate order cutoff (columns powers) := by
  change Finsupp.linearCombination ℝ _ (Finsupp.single powers scalar)=_
  rw [Finsupp.linearCombination_single]
  simp only [canonicalRestrictedColumn,if_pos h]

theorem canonicalColumnLinear_canonical (primary body : FiniteDist Color)
    (order : InputSeed Color → ℕ) (cutoff : ℕ)
    (columns : (InputSeed Color →₀ ℕ) → Table (InputSeed Color))
    (h : ∀ powers,CanonicalColumnDomain primary body order cutoff powers →
      InputTableCanonical primary body (columns powers))
    (table : Table (InputSeed Color)) :
    InputTableCanonical primary body (canonicalColumnLinear primary body order cutoff columns table) := by
  change InputTableCanonical _ _ (∑ powers∈table.support,
    MvPolynomial.coeff powers table • canonicalRestrictedColumn primary body order cutoff columns powers)
  apply InputTableCanonical.sum
  intro powers _
  rw [MvPolynomial.smul_eq_C_mul]
  apply InputTableCanonical.mul (InputTableCanonical.C _)
  unfold canonicalRestrictedColumn
  split_ifs with hd
  · exact (h powers hd).truncate _ _
  · exact InputTableCanonical.zero

theorem canonicalColumnLinear_activity_le (primary body : FiniteDist Color)
    (order : InputSeed Color → ℕ) (cutoff : ℕ)
    (columns : (InputSeed Color →₀ ℕ) → Table (InputSeed Color))
    (weight : InputSeed Color → ℝ) (hw : ∀ seed,0≤weight seed) (bound : ℝ) (hb : 0≤bound)
    (h : ∀ powers,CanonicalColumnDomain primary body order cutoff powers →
      activity weight (columns powers)≤bound*monomialWeight weight powers)
    (table : Table (InputSeed Color)) :
    activity weight (canonicalColumnLinear primary body order cutoff columns table)≤bound*activity weight table := by
  apply activity_linearCombination_le weight weight hw
  intro powers
  unfold canonicalRestrictedColumn
  split_ifs with hd
  · exact (activity_truncate_le weight hw _ _ _).trans (h powers hd)
  · rw [activity_zero]
    exact mul_nonneg hb (monomialWeight_nonneg weight hw powers)

/-- A canonical table already within the cutoff sees every genuine column,
so extending by zero never changes the response on the intended domain. -/
theorem canonicalColumnLinear_eq_sum (primary body : FiniteDist Color)
    (order : InputSeed Color → ℕ) (cutoff : ℕ)
    (columns : (InputSeed Color →₀ ℕ) → Table (InputSeed Color))
    (table : Table (InputSeed Color)) (hc : InputTableCanonical primary body table)
    (ht : truncate order cutoff table=table) :
    canonicalColumnLinear primary body order cutoff columns table=
      ∑ powers∈table.support,MvPolynomial.coeff powers table • truncate order cutoff (columns powers) := by
  change (∑ powers∈table.support,MvPolynomial.coeff powers table • canonicalRestrictedColumn primary body order cutoff columns powers)=_
  apply Finset.sum_congr rfl
  intro powers hp
  have hd : weightedOrder order powers≤cutoff := by
    have hm : powers∈(truncate order cutoff table).support := by rw [ht]; exact hp
    exact (Finset.mem_filter.mp hm).2
  simp only [canonicalRestrictedColumn,CanonicalColumnDomain,if_pos (And.intro hd (hc powers hp))]

end
end AFT.RepresentedPolynomial
