import AFT.IntegerLinearReduction
import AFT.Histogram

/-! # Uniform vertex relabeling is a legal affine postcomposition -/
namespace AFT
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

def chargeLatticeRelabel (count : ℕ) (q : ℤ) (permutation : Equiv.Perm (Fin (count+1))) :
    chargeLattice count q ≃ₗ[ℤ] chargeLattice count q where
  toFun word := ⟨fun index => word.val (permutation index),by
    change q ∣ ∑ index,word.val (permutation index)
    rw [Equiv.sum_comp permutation]
    exact word.property⟩
  invFun word := ⟨fun index => word.val (permutation.symm index),by
    change q ∣ ∑ index,word.val (permutation.symm index)
    rw [Equiv.sum_comp permutation.symm]
    exact word.property⟩
  left_inv word := by apply Subtype.ext; funext index; simp
  right_inv word := by apply Subtype.ext; funext index; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def vertexRelabelIntegerEquiv (count q : ℕ) [NeZero q]
    (column : Fin (count+1) → ℤ) (hcolumn : totalCharge column=(q : ℤ))
    (permutation : Equiv.Perm (Fin (count+1))) :
    ((Fin count → ℤ) × ℤ) ≃ₗ[ℤ] ((Fin count → ℤ) × ℤ) :=
  ((roundingCoordinates count q (by exact_mod_cast (NeZero.ne q)) column hcolumn).trans
    (chargeLatticeRelabel count q permutation)).trans
      (roundingCoordinates count q (by exact_mod_cast (NeZero.ne q)) column hcolumn).symm

theorem vertexRelabelIntegerEquiv_load (count q : ℕ) [NeZero q]
    (column : Fin (count+1) → ℤ) (hcolumn : totalCharge column=(q : ℤ))
    (permutation : Equiv.Perm (Fin (count+1))) (input : (Fin count → ℤ) × ℤ) :
    roundingLoad count column (vertexRelabelIntegerEquiv count q column hcolumn permutation input)=
      fun index => roundingLoad count column input (permutation index) := by
  change ((roundingCoordinates count q (by exact_mod_cast (NeZero.ne q)) column hcolumn)
    ((roundingCoordinates count q (by exact_mod_cast (NeZero.ne q)) column hcolumn).symm
      (chargeLatticeRelabel count q permutation
        ((roundingCoordinates count q (by exact_mod_cast (NeZero.ne q)) column hcolumn) input)))).val=_
  rw [LinearEquiv.apply_symm_apply]
  rfl

def vertexRelabelLinearEquiv (count q : ℕ) [NeZero q]
    (column : Fin (count+1) → ℤ) (hcolumn : totalCharge column=(q : ℤ))
    (permutation : Equiv.Perm (Fin (count+1))) :
    ((Fin count → ZMod q) × ZMod q) ≃ₗ[ZMod q] ((Fin count → ZMod q) × ZMod q) :=
  reduceIntegerLinearEquiv count q (vertexRelabelIntegerEquiv count q column hcolumn permutation)

def endpointRelabel (count q : ℕ) (permutation : Equiv.Perm (Fin (count+1))) :
    EndpointHyperplane count q ≃ EndpointHyperplane count q where
  toFun word := ⟨fun index => word.val (permutation index),by rw [Equiv.sum_comp permutation]; exact word.property⟩
  invFun word := ⟨fun index => word.val (permutation.symm index),by rw [Equiv.sum_comp permutation.symm]; exact word.property⟩
  left_inv word := by apply Subtype.ext; funext index; simp
  right_inv word := by apply Subtype.ext; funext index; simp

theorem vertexRelabelLinearEquiv_endpoint (count q : ℕ) [NeZero q]
    (column : Fin (count+1) → ℤ) (hcolumn : totalCharge column=(q : ℤ))
    (permutation : Equiv.Perm (Fin (count+1))) (input : (Fin count → ZMod q) × ZMod q) :
    endpointProjection count q column hcolumn (vertexRelabelLinearEquiv count q column hcolumn permutation input)=
      endpointRelabel count q permutation (endpointProjection count q column hcolumn input) := by
  have hr := reduce_liftCoordinates count q input
  conv_lhs => rw [← hr]
  unfold vertexRelabelLinearEquiv
  rw [reduceIntegerLinearEquiv_apply]
  apply Subtype.ext
  funext index
  rw [endpointProjection_reduceCoordinates,vertexRelabelIntegerEquiv_load]
  rfl

/-- The integer carry sum is invariant under every vertex permutation,
including on unbounded inputs. Thus zero-fiber membership is preserved. -/
theorem vertexRelabelLinearEquiv_label (count q : ℕ) [NeZero q]
    (column : Fin (count+1) → ℤ) (hcolumn : totalCharge column=(q : ℤ))
    (permutation : Equiv.Perm (Fin (count+1))) (input : (Fin count → ZMod q) × ZMod q) :
    fiberLabel count q column (vertexRelabelLinearEquiv count q column hcolumn permutation input)=
      fiberLabel count q column input := by
  have hr := reduce_liftCoordinates count q input
  conv_lhs => rw [← hr]
  unfold vertexRelabelLinearEquiv
  rw [reduceIntegerLinearEquiv_apply,fiberLabel_reduceCoordinates count q column hcolumn]
  unfold integerLabel
  rw [vertexRelabelIntegerEquiv_load]
  change ((∑ index,roundingLoad count column (liftCoordinates count q input) (permutation index)/(q : ℤ) : ℤ) : ZMod q)=_
  rw [Equiv.sum_comp permutation (fun index => roundingLoad count column (liftCoordinates count q input) index/(q : ℤ))]
  rfl

def AffinePair.postcompose {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (pair : AffinePair R V) (linear : V ≃ₗ[R] V) : AffinePair R V :=
  ⟨pair.linear.trans linear,linear pair.offset⟩

theorem AffinePair.postcompose_eval {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (pair : AffinePair R V) (linear : V ≃ₗ[R] V) (input : V) :
    (pair.postcompose linear).eval input=linear (pair.eval input) := by
  simp only [AffinePair.postcompose,AffinePair.eval,LinearEquiv.trans_apply,map_add]

end
end AFT
