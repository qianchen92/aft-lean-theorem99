import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.BigOperators

/-! # Explicit numberings of block roots, endpoints and edges

These are arithmetic sum/product encodings; no chosen finite enumeration
is part of the runtime representation.
-/
namespace AFT

 def blockNumbering (legs rest : ℕ) : (Fin legs⊕Fin rest)≃Fin (legs+rest) := finSumFinEquiv

 abbrev blockSlotsProgram (legs rest : ℕ) (index : Fin legs⊕Fin rest) :=
  Fin (Sum.elim (fun _ => 3) (fun _ => 1) index)

 def blockVertexSplit (legs rest : ℕ) :
    (Sigma (blockSlotsProgram legs rest))≃
      ((Fin legs×Fin 3)⊕(Fin rest×Fin 1)) where
  toFun point := match point with
    | ⟨.inl leg,slot⟩ => .inl (leg,slot)
    | ⟨.inr body,slot⟩ => .inr (body,slot)
  invFun point := match point with
    | .inl (leg,slot) => ⟨.inl leg,slot⟩
    | .inr (body,slot) => ⟨.inr body,slot⟩
  left_inv point := by rcases point with ⟨leg|body,slot⟩ <;> rfl
  right_inv point := by rcases point with ⟨leg,slot⟩|⟨body,slot⟩ <;> rfl

 def blockVertexNumbering (legs rest : ℕ) :
    (Sigma (blockSlotsProgram legs rest))≃
      Fin (legs*3+rest) :=
  (blockVertexSplit legs rest).trans
    ((Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans
      (finSumFinEquiv.trans (finCongr (by omega))))

 def blockEdgeNumbering (legs path : ℕ) :
    ((Fin legs×Fin 2)⊕Fin path)≃Fin (legs*2+path) :=
  (Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans finSumFinEquiv

end AFT
