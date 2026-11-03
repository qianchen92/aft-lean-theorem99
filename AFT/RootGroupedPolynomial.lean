import AFT.GroupedRootTensor
import AFT.RepresentedPolynomial

/-! # Exact polynomial Fubini for arbitrary joint grouped root responses -/
namespace AFT.RootTensor
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {Index Source Color : Type*} [Fintype Index] [DecidableEq Index]
  [Fintype Source] [Fintype Color]
variable (Slots : Index → Type*) [∀ index,Fintype (Slots index)]
local instance groupedPolynomialSigmaDecEq : DecidableEq (Sigma Slots) := Classical.decEq _
local instance groupedPolynomialLocalDecEq (index : Index) : DecidableEq (Slots index) := Classical.decEq _

omit [Fintype Source] in
/-- Finite sums over the complete output word factor only over the local
physical groups; no factorization of a joint root coefficient is used. -/
theorem sum_sigma_word_product {R : Type*} [CommSemiring R]
    (function : (index : Index) → (Slots index → Color) → R) :
    (∑ output : Sigma Slots → Color, ∏ index,function index (fun slot => output ⟨index,slot⟩))=
      ∏ index,∑ output : Slots index → Color,function index output := by
  have he := (Equiv.piCurry (fun index (_ : Slots index) => Color)).sum_comp
    (fun output => ∏ index,function index (output index))
  exact he.trans (Fintype.prod_sum function).symm

/-- The complete joint density polynomial equals the expectation of the
product of the genuine local response polynomials. The kernel is arbitrary. -/
theorem groupedDensity_polynomial (source : Index → FiniteDist Source)
    (reference : Sigma Slots → FiniteDist Color)
    (matrix : (index : Index) → Source → (Slots index → Color) → ℝ)
    (kernel : (Index → Source) → ℝ) :
    (∑ word : Sigma Slots → Color,
      MvPolynomial.C (groupedDensity Slots source matrix kernel word*
        ∏ slot,(reference slot).weight (word slot))*∏ slot,MvPolynomial.X (word slot))=
    ∑ roots : Index → Source,
      MvPolynomial.C ((FiniteDist.independent source).weight roots*kernel roots)*
        ∏ index,∑ word : Slots index → Color,
          MvPolynomial.C (matrix index (roots index) word*
            ∏ slot,(reference ⟨index,slot⟩).weight (word slot))*∏ slot,MvPolynomial.X (word slot) := by
  let localPolynomial (roots : Index → Source) (index : Index) (word : Slots index → Color) :
      MvPolynomial Color ℝ :=
    MvPolynomial.C (matrix index (roots index) word*∏ slot,(reference ⟨index,slot⟩).weight (word slot))*
      ∏ slot,MvPolynomial.X (word slot)
  have hpoint (word : Sigma Slots → Color) :
      MvPolynomial.C (groupedDensity Slots source matrix kernel word*
          ∏ slot,(reference slot).weight (word slot))*∏ slot,MvPolynomial.X (word slot)=
        ∑ roots : Index → Source,MvPolynomial.C ((FiniteDist.independent source).weight roots*kernel roots)*
          ∏ index,localPolynomial roots index (fun slot => word ⟨index,slot⟩) := by
    unfold groupedDensity FiniteDist.expectation
    rw [Finset.sum_mul,map_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro roots _
    simp only [localPolynomial,map_mul,map_prod,Fintype.prod_sigma,Finset.prod_mul_distrib]
    ring
  simp only [hpoint]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro roots _
  rw [← Finset.mul_sum,sum_sigma_word_product]
end
end AFT.RootTensor
