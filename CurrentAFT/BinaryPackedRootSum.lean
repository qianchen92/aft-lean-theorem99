import CurrentAFT.BinaryTupleSum
import CurrentAFT.RationalPackedRootProgram
import CurrentAFT.CurrentProposalResources

/-! The joint root/control source is enumerated by actual nested finite loops.
Every source word is materialized by charged prepend operations. The bijection
to the paper's flat base-q source index is used only in the semantic proof. -/
namespace CurrentAFT.BinaryPackedRootSum
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus

abbrev Source (security groups : ℕ) := Vector (Fin (CurrentRectangleIndex.colors security)) (groups*3)


def current (security groups : ℕ) (kernel : Source security groups → RationalResult) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let result := BinaryTupleSum.current modulus.count (groups*3) kernel
  ⟨result.data, modulus.work+result.work+2⟩

 theorem current_value (security groups : ℕ) (kernel : Source security groups → RationalResult)
    (ideal : (Fin groups → Fin 3 → ℕ) → ℚ)
    (hkernel : ∀ source, (kernel source).data.decode = ideal (fun group slot => (source.get (finProdFinEquiv (group,slot))).val)) :
    (current security groups kernel).data.decode =
      ∑ index : Fin ((CurrentRectangleIndex.colors security)^(groups*3)),
        ideal (RationalPackedRootProgram.sourceWord security groups index) := by
  change (BinaryTupleSum.current _ _ _).data.decode = _
  rw [BinaryTupleSum.current_value]
  simp only [hkernel, Vector.get_ofFn]
  exact ((GroupSourcePadding.tupleEquiv (CurrentRectangleIndex.colors security) (groups*3)
    (CurrentRectangleIndex.colors_pos security)).symm.sum_comp
      (fun source => ideal (fun group slot => (source (finProdFinEquiv (group,slot))).val))).symm

noncomputable section

 theorem height_mono {pool larger count first second : ℕ} (hp : pool ≤ larger) (hh : first ≤ second) :
    BinaryTupleSum.height pool count first ≤ BinaryTupleSum.height larger count second := by
  induction count with
  | zero => exact hh
  | succ count ih => exact Nat.mul_le_mul hp (Nat.add_le_add_right ih 1)

 theorem work_mono {pool larger count first second firstWork secondWork : ℕ}
    (hp : pool ≤ larger) (hh : first ≤ second) (hw : firstWork ≤ secondWork) :
    BinaryTupleSum.work pool count first firstWork ≤ BinaryTupleSum.work larger count second secondWork := by
  induction count generalizing firstWork secondWork with
  | zero => exact hw
  | succ count ih =>
    have ht := height_mono (count := count) hp hh
    have hr := ih (Nat.add_le_add_right (Nat.add_le_add_left hw (BinaryTupleSum.prependWork count)) 1)
    simp only [BinaryTupleSum.work]
    exact Nat.add_le_add_right (Nat.mul_le_mul hp (Nat.add_le_add_right (Nat.add_le_add hr
      (BinaryArithmetic.RationalBits.primitiveWorkBound_mono (Nat.mul_le_mul (Nat.add_le_add_right hp 1) (Nat.add_le_add_right ht 1)))) 2)) 2


def heightPolynomial (limit : ℕ) (leafHeight : Polynomial ℕ) : Polynomial ℕ :=
  ∑ count ∈ Finset.range (limit*3+1),
    BinaryTupleSum.heightPolynomial CurrentProposalResources.primeSizePolynomial count leafHeight


def workPolynomial (limit : ℕ) (leafHeight leafWork : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial +
    (∑ count ∈ Finset.range (limit*3+1),
      BinaryTupleSum.workPolynomial CurrentProposalResources.primeSizePolynomial count leafHeight leafWork) + 2

 theorem current_polynomial_bounds (security groups limit : ℕ) (hgroups : groups ≤ limit)
    (kernel : Source security groups → RationalResult) (leafHeight leafWork : Polynomial ℕ)
    (hh : ∀ source, HeightBound (kernel source).data.decode (leafHeight.eval security))
    (hw : ∀ source, (kernel source).work ≤ leafWork.eval security) :
    HeightBound (current security groups kernel).data.decode ((heightPolynomial limit leafHeight).eval security) ∧
      (current security groups kernel).work ≤ (workPolynomial limit leafHeight leafWork).eval security := by
  have h := BinaryTupleSum.current_bounds (CurrentRectangleIndex.colors security) (groups*3) kernel _ _ hh hw
  have hq : CurrentRectangleIndex.colors security ≤ CurrentProposalResources.primeSizePolynomial.eval security := by
    rw [CurrentRectangleIndex.colors_eq]
    simpa only [CurrentProposalResources.primeSizePolynomial, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat, Parameters.base] using (Parameters.modulus_bounds security).2
  have hh' := h.1.mono (height_mono (count := groups*3) hq le_rfl)
  have hw' := h.2.trans (work_mono (count := groups*3) hq le_rfl le_rfl)
  have hheight : BinaryTupleSum.height (CurrentProposalResources.primeSizePolynomial.eval security) (groups*3) (leafHeight.eval security) ≤
      (heightPolynomial limit leafHeight).eval security := by
    rw [← BinaryTupleSum.heightPolynomial_eval]
    simp only [heightPolynomial, Polynomial.eval_finset_sum]
    exact Finset.single_le_sum (a := groups*3) (s := Finset.range (limit*3+1))
      (f := fun count => (BinaryTupleSum.heightPolynomial CurrentProposalResources.primeSizePolynomial count leafHeight).eval security)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
  have hwork : BinaryTupleSum.work (CurrentProposalResources.primeSizePolynomial.eval security) (groups*3) (leafHeight.eval security) (leafWork.eval security) ≤
      (∑ count ∈ Finset.range (limit*3+1),
        BinaryTupleSum.workPolynomial CurrentProposalResources.primeSizePolynomial count leafHeight leafWork).eval security := by
    rw [← BinaryTupleSum.workPolynomial_eval]
    simp only [Polynomial.eval_finset_sum]
    exact Finset.single_le_sum (a := groups*3) (s := Finset.range (limit*3+1))
      (f := fun count => (BinaryTupleSum.workPolynomial CurrentProposalResources.primeSizePolynomial count leafHeight leafWork).eval security)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
  refine ⟨hh'.mono hheight, ?_⟩
  have hp := PublicParameterProgram.modulus_work security
  change (PublicParameterProgram.modulus security).work + (BinaryTupleSum.current _ _ kernel).work + 2 ≤ _
  simp only [workPolynomial, Polynomial.eval_add, Polynomial.eval_ofNat, PublicParameterProgram.workPolynomial_eval]
  omega

end
end CurrentAFT.BinaryPackedRootSum
