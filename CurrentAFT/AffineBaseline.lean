import CurrentAFT.LobsterMixerMatrix

/-! # Shared baseline, public closure, and integral affine offsets -/
namespace CurrentAFT.AffineBaseline
open AFT PublicCharge LobsterCoordinates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable {Leg : Type*} [Fintype Leg] {bodyEdges : ℕ}

def baseline (modulus : ℕ) (centers : Fin (bodyEdges + 1) → ℤ) (shift intercept : Leg → ℤ) :
    EndpointIndex (bodyEdges + 1) Leg → ℤ
  | .inl vertex => centers vertex
  | .inr (.inl leg) => intercept leg
  | .inr (.inr leg) => (modulus : ℤ) - 1 + shift leg - intercept leg

theorem sum_baseline (modulus : ℕ) (centers : Fin (bodyEdges + 1) → ℤ) (shift intercept : Leg → ℤ) :
    ∑ index, baseline modulus centers shift intercept index =
      (∑ vertex, centers vertex) + (∑ leg, shift leg) + (Fintype.card Leg : ℤ) * ((modulus : ℤ) - 1) := by
  simp only [Fintype.sum_sum_type, baseline, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

def closure (bodyEdges : ℕ) (scalar : ℤ) (vertex : Fin (bodyEdges + 1)) : ℤ :=
  (if vertex = Fin.last bodyEdges then scalar else 0) - (if vertex = 0 then scalar else 0)

theorem sum_closure (bodyEdges : ℕ) (scalar : ℤ) : ∑ vertex, closure bodyEdges scalar vertex = 0 := by
  simp [closure, Finset.sum_sub_distrib]

def offset (modulus : ℕ) (centers : Fin (bodyEdges + 1) → ℤ) (shift intercept : Leg → ℤ)
    (placement : Equiv.Perm (Fin (bodyEdges + 1))) (closureScalar : ℤ) :
    EndpointIndex (bodyEdges + 1) Leg → ℤ :=
  baseline modulus centers shift intercept + Sum.elim
    (fun vertex => closure bodyEdges closureScalar (placement.symm vertex)) (fun _ => 0)

theorem sum_offset (modulus : ℕ) (centers : Fin (bodyEdges + 1) → ℤ) (shift intercept : Leg → ℤ)
    (placement : Equiv.Perm (Fin (bodyEdges + 1))) (closureScalar : ℤ) :
    ∑ index, offset modulus centers shift intercept placement closureScalar index =
      (∑ vertex, centers vertex) + (∑ leg, shift leg) + (Fintype.card Leg : ℤ) * ((modulus : ℤ) - 1) := by
  simp only [offset, Pi.add_apply, Finset.sum_add_distrib]
  rw [sum_baseline]
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.sum_const_zero, add_zero]
  rw [Equiv.sum_comp placement.symm, sum_closure, add_zero]

theorem offset_charge_iff (modulus : ℕ) (centers : Fin (bodyEdges + 1) → ℤ) (shift intercept : Leg → ℤ)
    (placement : Equiv.Perm (Fin (bodyEdges + 1))) (closureScalar : ℤ) :
    (modulus : ℤ) ∣ ∑ index, offset modulus centers shift intercept placement closureScalar index ↔
      PublicChargeTest modulus centers shift := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, sum_offset]
  unfold PublicChargeTest
  push_cast
  simp only [ZMod.natCast_self, zero_sub, mul_neg, mul_one]
  constructor <;> intro h <;> linear_combination h

def numberedOffset (bodyEdges legs modulus : ℕ) (centers : Fin (bodyEdges + 1) → ℤ)
    (shift intercept : Fin legs → ℤ) (placement : Equiv.Perm (Fin (bodyEdges + 1))) (closureScalar : ℤ)
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1))) :
    Fin (bodyEdges + (legs + legs) + 1) → ℤ :=
  fun index => offset modulus centers shift intercept placement closureScalar
    ((vertexIndex bodyEdges legs).symm (relabeling.symm index))

theorem numberedOffset_charge (bodyEdges legs modulus : ℕ) (centers : Fin (bodyEdges + 1) → ℤ)
    (shift intercept : Fin legs → ℤ) (placement : Equiv.Perm (Fin (bodyEdges + 1))) (closureScalar : ℤ)
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1)))
    (hcharge : PublicChargeTest modulus centers shift) :
    (modulus : ℤ) ∣ totalCharge (numberedOffset bodyEdges legs modulus centers shift intercept placement closureScalar relabeling) := by
  unfold totalCharge numberedOffset
  rw [Equiv.sum_comp relabeling.symm (fun index =>
    offset modulus centers shift intercept placement closureScalar ((vertexIndex bodyEdges legs).symm index)),
    Equiv.sum_comp (vertexIndex bodyEdges legs).symm]
  exact (offset_charge_iff modulus centers shift intercept placement closureScalar).mpr hcharge

/-- The actual baseline and closure offset have a unique integral pullback
through the fixed rounding matrix, after every final endpoint relabeling. -/
theorem offset_integral_preimage (bodyEdges legs modulus : ℕ) (hmodulus : modulus ≠ 0)
    (roundingColumn : Fin (bodyEdges + (legs + legs) + 1) → ℤ)
    (hcolumn : totalCharge roundingColumn = (modulus : ℤ))
    (centers : Fin (bodyEdges + 1) → ℤ) (shift intercept : Fin legs → ℤ)
    (placement : Equiv.Perm (Fin (bodyEdges + 1))) (closureScalar : ℤ)
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1)))
    (hcharge : PublicChargeTest modulus centers shift) :
    ∃! preimage, roundingLoad (bodyEdges + (legs + legs)) roundingColumn preimage =
      numberedOffset bodyEdges legs modulus centers shift intercept placement closureScalar relabeling :=
  unique_integral_preimage _ modulus (by exact_mod_cast hmodulus) roundingColumn hcolumn _
    (numberedOffset_charge bodyEdges legs modulus centers shift intercept placement closureScalar relabeling hcharge)

end
end CurrentAFT.AffineBaseline
