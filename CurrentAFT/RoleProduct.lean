import CurrentAFT.GradedNewtonNorm

/-!
# Three actual population roles in a complete fixed-queue product

This is the finite bookkeeping used for free bodies, queue bodies and
complete leg triples. The one queue atom is shared by its entire population.
The estimate retains cancellation of the combined linear coefficient.
-/

namespace CurrentAFT.RoleProduct

open AFT ControlCoordinates GradedControlAlgebra GradedControlNorm GradedNewtonNorm
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

abbrev RoleIndex (freeCount queueCount legCount : ℕ) :=
  Fin freeCount ⊕ (Fin queueCount ⊕ Fin legCount)

def roleAtoms (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (freeCount queueCount legCount : ℕ) (free queue leg : KernelFamily primary body order) :
    RoleIndex freeCount queueCount legCount → KernelFamily primary body order :=
  Sum.elim (fun _ => free) (Sum.elim (fun _ => queue) (fun _ => leg))

theorem roleAtoms_sum (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (freeCount queueCount legCount : ℕ) (free queue leg : KernelFamily primary body order) :
    (∑ index, roleAtoms primary body order freeCount queueCount legCount free queue leg index) =
      freeCount • free + queueCount • queue + legCount • leg := by
  simp only [roleAtoms, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  abel

theorem roleAtoms_product (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (freeCount queueCount legCount : ℕ) (free queue leg : KernelFamily primary body order) :
    (∏ index, (1 + roleAtoms primary body order freeCount queueCount legCount free queue leg index)) =
      (1 + free) ^ freeCount * (1 + queue) ^ queueCount * (1 + leg) ^ legCount := by
  simp only [roleAtoms, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [mul_assoc]

theorem complete_role_product_norm_le (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (pf bf : ℝ) (hpf : 0 ≤ pf) (hbf : 0 ≤ bf) (freeCount queueCount legCount : ℕ)
    (hsize : order ≤ freeCount + queueCount + legCount) (free queue leg : KernelFamily primary body order)
    (hfreeZero : free (zeroArity order) = 0) (hqueueZero : queue (zeroArity order) = 0)
    (hlegZero : leg (zeroArity order) = 0)
    (delta : ℝ) (hdelta : 0 ≤ delta) (hsmall : delta ≤ 1)
    (hfirst : familyNorm primary body order pf bf
      (freeCount • free + queueCount • queue + legCount • leg) ≤ delta)
    (hsquares : (freeCount : ℝ) * familyNorm primary body order pf bf free ^ 2 +
      (queueCount : ℝ) * familyNorm primary body order pf bf queue ^ 2 +
      (legCount : ℝ) * familyNorm primary body order pf bf leg ^ 2 ≤ delta)
    (hfree : familyNorm primary body order pf bf free ≤ 1)
    (hqueue : familyNorm primary body order pf bf queue ≤ 1)
    (hleg : familyNorm primary body order pf bf leg ≤ 1) :
    familyNorm primary body order pf bf
      ((1 + free) ^ freeCount * (1 + queue) ^ queueCount * (1 + leg) ^ legCount - 1) ≤
        (order : ℝ) * delta * ((order + 1 : ℕ) : ℝ) ^ order := by
  let atoms := roleAtoms primary body order freeCount queueCount legCount free queue leg
  have hzero (index : RoleIndex freeCount queueCount legCount) : atoms index (zeroArity order) = 0 := by
    cases index with
    | inl index => exact hfreeZero
    | inr index => cases index with
      | inl index => exact hqueueZero
      | inr index => exact hlegZero
  have hcard : order ≤ Fintype.card (RoleIndex freeCount queueCount legCount) := by
    simpa only [RoleIndex, Fintype.card_sum, Fintype.card_fin, Nat.add_assoc] using hsize
  have hfirst' : familyNorm primary body order pf bf (∑ index, atoms index) ≤ delta := by
    rw [show (∑ index, atoms index) = freeCount • free + queueCount • queue + legCount • leg from
      roleAtoms_sum primary body order freeCount queueCount legCount free queue leg]
    exact hfirst
  have hsquares' : (∑ index, familyNorm primary body order pf bf (atoms index) ^ 2) ≤ delta := by
    simpa only [atoms, roleAtoms, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, add_assoc] using hsquares
  have hatoms (index : RoleIndex freeCount queueCount legCount) :
      familyNorm primary body order pf bf (atoms index) ≤ 1 := by
    cases index with
    | inl index => exact hfree
    | inr index => cases index with
      | inl index => exact hqueue
      | inr index => exact hleg
  have h := complete_product_norm_le primary body order pf bf hpf hbf atoms hzero hcard delta hdelta hsmall
    hfirst' hsquares' hatoms
  rw [roleAtoms_product primary body order freeCount queueCount legCount free queue leg] at h
  exact h

end

end CurrentAFT.RoleProduct
