import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Sorting a finite public set using an explicitly given coordinate code -/
namespace AFT

 def finiteSetNumbering {State : Type*} {size : ℕ} (index : State≃Fin size) (set : Finset State) :
    Fin set.card≃set :=
  letI : LinearOrder State := LinearOrder.lift' index index.injective
  (set.orderIsoOfFin rfl).toEquiv

 def finiteSetMatching {State : Type*} {size : ℕ} (index : State≃Fin size)
    (first second : Finset State) (hcard : first.card≤second.card) : first↪second :=
  (finiteSetNumbering index first).symm.toEmbedding.trans
    ((Fin.castLEEmb hcard).trans (finiteSetNumbering index second).toEmbedding)

end AFT
