import CurrentAFT.GroupedKernelCanonical
import CurrentAFT.GradedControlAlgebra

/-! # Finite arity patterns of the genuine canonical coefficient product -/

namespace CurrentAFT.GroupedKernelProduct
open AFT ControlCoordinates ControlProduct ControlNorm GradedControlAlgebra
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

def sigmaHeadEquiv {count : ℕ} (Slots : Fin (count + 1) → Type*) :
    Sigma Slots ≃ (Slots 0 ⊕ Sigma (fun index : Fin count => Slots index.succ)) where
  toFun word := Fin.cases (fun value => Sum.inl value)
    (fun index value => Sum.inr ⟨index, value⟩) word.1 word.2
  invFun word := Sum.elim (fun value => ⟨0, value⟩)
    (fun tail => ⟨tail.1.succ, tail.2⟩) word
  left_inv word := by
    rcases word with ⟨index, value⟩
    cases index using Fin.cases <;> rfl
  right_inv word := by cases word <;> rfl

def slotsEquiv : (count : ℕ) → (sizes : Fin count → ℕ) →
    (Sigma (fun index => Fin (sizes index))) ≃ Fin (∑ index, sizes index)
  | 0, sizes => (Equiv.equivOfIsEmpty _ (Fin 0)).trans (finCongr (by simp))
  | count + 1, sizes =>
      (sigmaHeadEquiv (fun index => Fin (sizes index))).trans
        ((Equiv.sumCongr (Equiv.refl (Fin (sizes 0)))
          (slotsEquiv count (fun index => sizes index.succ))).trans
            (finSumFinEquiv.trans (finCongr (Fin.sum_univ_succ sizes).symm)))

/-- Only the finite arity choices are expanded. Colors remain arguments
of one joint kernel throughout the later Hilbert contraction. -/
theorem product_family_arity_expansion {Group : Type*} [Fintype Group]
    (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (families : Group → KernelFamily primary body order) :
    (∏ group, families group) =
      ∑ pattern : Group → TruncatedArity order,
        ∏ group, Pi.single (pattern group) (families group (pattern group)) := by
  conv_lhs => arg 2; ext group; rw [← Finset.univ_sum_single (families group)]
  exact Fintype.prod_sum _

def embedArity (order r s : ℕ) (hdegree : r + s ≤ order) : TruncatedArity order :=
  ⟨(⟨r, by omega⟩, ⟨s, by omega⟩), hdegree⟩

def embed (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    {r s : ℕ} (hdegree : r + s ≤ order) (kernel : canonicalKernels primary body r s) :
    KernelFamily primary body order := Pi.single (embedArity order r s hdegree) kernel

theorem embed_transport (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    {r s r' s' : ℕ} (hr : r = r') (hs : s = s')
    (hdegree : r + s ≤ order) (hdegree' : r' + s' ≤ order)
    (kernel : canonicalKernels primary body r s) :
    embed primary body order hdegree' (transportKernel primary body hr hs kernel) =
      embed primary body order hdegree kernel := by
  subst r'; subst s'; rfl

theorem embed_mul (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    {r s r' s' : ℕ} (hfirst : r + s ≤ order) (hsecond : r' + s' ≤ order)
    (hdegree : (r + r') + (s + s') ≤ order)
    (first : canonicalKernels primary body r s) (second : canonicalKernels primary body r' s') :
    embed primary body order hfirst first * embed primary body order hsecond second =
      embed primary body order hdegree (homogeneousProduct primary body first second) := by
  change familyProduct primary body order
    (Pi.single (embedArity order r s hfirst) first)
    (Pi.single (embedArity order r' s' hsecond) second) = _
  exact familyProduct_single_retained primary body order
    (embedArity order r s hfirst) (embedArity order r' s' hsecond) first second hdegree

/-- Ordered iterated homogeneous products, with only the true slot-count
equalities transported between successive finite fibers. -/
def iteratedProduct (primary : FiniteDist Primary) (body : FiniteDist Body) :
    (count : ℕ) → (r s : Fin count → ℕ) →
    ((index : Fin count) → canonicalKernels primary body (r index) (s index)) →
      canonicalKernels primary body (∑ index, r index) (∑ index, s index)
  | 0, _, _, _ => scalarUnit primary body
  | count + 1, r, s, kernels =>
      transportKernel primary body (Fin.sum_univ_succ r).symm (Fin.sum_univ_succ s).symm
        (homogeneousProduct primary body (kernels 0)
          (iteratedProduct primary body count (fun index => r index.succ)
            (fun index => s index.succ) (fun index => kernels index.succ)))

theorem product_embed (primary : FiniteDist Primary) (body : FiniteDist Body) (order count : ℕ)
    (r s : Fin count → ℕ)
    (kernels : (index : Fin count) → canonicalKernels primary body (r index) (s index))
    (hdegree : (∑ index, r index) + (∑ index, s index) ≤ order)
    (hlocal : ∀ index, r index + s index ≤ order) :
    (∏ index, embed primary body order (hlocal index) (kernels index)) =
      embed primary body order hdegree (iteratedProduct primary body count r s kernels) := by
  induction count with
  | zero =>
    simp only [Fin.prod_univ_zero]
    rfl
  | succ count ih =>
    have htail : (∑ index : Fin count, r index.succ) + (∑ index : Fin count, s index.succ) ≤ order := by
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at hdegree
      omega
    rw [Fin.prod_univ_succ, ih (fun index => r index.succ) (fun index => s index.succ)
      (fun index => kernels index.succ) htail (fun index => hlocal index.succ)]
    conv_rhs => rw [iteratedProduct]
    rw [embed_transport primary body order _ _
      (show (r 0 + ∑ index : Fin count, r index.succ) + (s 0 + ∑ index : Fin count, s index.succ) ≤ order by
        simpa only [Fin.sum_univ_succ] using hdegree) hdegree]
    exact embed_mul primary body order _ _ _ _ _

end
end CurrentAFT.GroupedKernelProduct
