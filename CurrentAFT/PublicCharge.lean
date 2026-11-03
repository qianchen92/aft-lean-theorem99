import Mathlib

/-!
# The current construction's pointwise public charge identity

This file follows `def:body-injection`, `def:shared-baseline-vector`,
`sec:queue-injection`, and `sec:df-public-charge-verification` in the
current manuscript. It does not import the frozen V7 formalization.

The endpoint assembly keeps the body's closing edge, both off-body leg
colors, the same second input at the companion and attachment, and one
shared queue scalar. The only geometric hypothesis in the modular result
is the queue's prescribed cardinality. No charge identity is assumed.
Safe support and carry cancellation are separate statements: the algebra
below holds for all values of the hidden inputs.
-/

namespace CurrentAFT

open scoped BigOperators

namespace PublicCharge

variable {G : Type*} [AddCommGroup G] {body : ℕ}
variable {Leg : Type*} [Fintype Leg]

/-- Body vertices, primary leg vertices, and companion leg vertices.
An attachment is a body vertex and therefore has no second baseline. -/
abbrev EndpointIndex (body : ℕ) (Leg : Type*) := Fin body ⊕ (Leg ⊕ Leg)

/-- Cyclic differences with the predecessor taken modulo the full body
length. In particular, the first coordinate retains the closing edge. -/
def cycleDifference (latent : Fin body → G) (vertex : Fin body) : G :=
  latent vertex - latent ((finRotate body).symm vertex)

theorem cycleDifference_first (latent : Fin (body + 1) → G) :
    cycleDifference latent 0 = latent 0 - latent (Fin.last body) := by
  have hclose : (finRotate (body + 1)).symm 0 = Fin.last body := by
    apply (finRotate (body + 1)).injective
    simp
  simp only [cycleDifference, hclose]

/-- The closing edge makes the complete cycle's charge zero over the
integers, and more generally in every additive commutative group. -/
theorem sum_cycleDifference (latent : Fin body → G) :
    ∑ vertex, cycleDifference latent vertex = 0 := by
  unfold cycleDifference
  rw [Finset.sum_sub_distrib, (finRotate body).symm.sum_comp]
  exact sub_self _

/-- Place each second leg input at its body attachment. The same input
is subtracted from its companion below. -/
def attachmentIncrement (attachment : Leg → Fin body) (second : Leg → G)
    (vertex : Fin body) : G :=
  ∑ leg, if attachment leg = vertex then second leg else 0

theorem sum_attachmentIncrement (attachment : Leg → Fin body) (second : Leg → G) :
    ∑ vertex, attachmentIncrement attachment second vertex = ∑ leg, second leg := by
  unfold attachmentIncrement
  rw [Finset.sum_comm]
  simp

/-- Every queue vertex receives the same scalar. -/
def queueIncrement (queue : Finset (Fin body)) (scalar : G) (vertex : Fin body) : G :=
  if vertex ∈ queue then scalar else 0

theorem sum_queueIncrement (queue : Finset (Fin body)) (scalar : G) :
    ∑ vertex, queueIncrement queue scalar vertex = queue.card • scalar := by
  simp [queueIncrement]

/-- The off-body companion retains the shared second input; the
primary may itself depend on both hidden coordinates and the public map. -/
def legCompanion (legConstant : G) (shift second primary : Leg → G) (leg : Leg) : G :=
  legConstant + shift leg - second leg - primary leg

theorem leg_charge (legConstant shift second primary : G) :
    primary + (legConstant + shift - second - primary) + second =
      legConstant + shift := by
  abel

/-- The actual additive endpoint assembly before final relabeling.
The body placement moves the entire closed cycle. -/
def assembledEndpoint (centers : Fin body → G) (shift : Leg → G)
    (legConstant : G) (latent : Fin body → G) (bodyPlacement : Equiv.Perm (Fin body))
    (attachment : Leg → Fin body) (second primary : Leg → G)
    (queue : Finset (Fin body)) (scalar : G) : EndpointIndex body Leg → G
  | .inl vertex => centers vertex + cycleDifference latent (bodyPlacement.symm vertex) +
      attachmentIncrement attachment second vertex + queueIncrement queue scalar vertex
  | .inr (.inl leg) => primary leg
  | .inr (.inr leg) => legCompanion legConstant shift second primary leg

/-- Summing all endpoints cancels the entire cycle, every primary,
and every transferred second input. Attachments need not be distinct
for this identity; the manuscript's disjoint placement is a special case. -/
theorem sum_assembledEndpoint (centers : Fin body → G) (shift : Leg → G)
    (legConstant : G) (latent : Fin body → G) (bodyPlacement : Equiv.Perm (Fin body))
    (attachment : Leg → Fin body) (second primary : Leg → G)
    (queue : Finset (Fin body)) (scalar : G) :
    ∑ vertex, assembledEndpoint centers shift legConstant latent bodyPlacement
      attachment second primary queue scalar vertex =
      (∑ vertex, centers vertex) + (∑ leg, shift leg) +
        Fintype.card Leg • legConstant + queue.card • scalar := by
  simp only [Fintype.sum_sum_type, assembledEndpoint, legCompanion,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
  rw [bodyPlacement.symm.sum_comp, sum_cycleDifference,
    sum_attachmentIncrement, sum_queueIncrement]
  abel

/-- The integer total before reduction modulo the modulus. A queue of
size `modulus` contributes exactly `modulus * scalar`, not independent
scalars at its vertices. -/
theorem integer_endpoint_sum (modulus : ℕ) (centers : Fin body → ℤ) (shift : Leg → ℤ)
    (latent : Fin body → ℤ) (bodyPlacement : Equiv.Perm (Fin body))
    (attachment : Leg → Fin body) (second primary : Leg → ℤ)
    (queue : Finset (Fin body)) (hqueue : queue.card = modulus) (scalar : ℤ) :
    ∑ vertex, assembledEndpoint centers shift ((modulus : ℤ) - 1) latent bodyPlacement
      attachment second primary queue scalar vertex =
      (∑ vertex, centers vertex) + (∑ leg, shift leg) +
        (Fintype.card Leg : ℤ) * ((modulus : ℤ) - 1) + (modulus : ℤ) * scalar := by
  simpa only [hqueue, nsmul_eq_mul] using
    sum_assembledEndpoint centers shift ((modulus : ℤ) - 1) latent bodyPlacement
      attachment second primary queue scalar

/-- Public charge reads only the sampled centers and leg shifts. It
does not read any hidden input, cycle realization, queue scalar, or map. -/
def PublicChargeTest (modulus : ℕ) (centers : Fin body → ℤ) (shift : Leg → ℤ) : Prop :=
  (((∑ vertex, centers vertex) + (∑ leg, shift leg) : ℤ) : ZMod modulus) =
    (Fintype.card Leg : ZMod modulus)

/-- The protected endpoint's total residue is the centers' sum plus
the shifts' sum minus the number of legs. No probabilistic assumption
or conditioning is used. -/
theorem endpoint_charge (modulus : ℕ) (centers : Fin body → ℤ) (shift : Leg → ℤ)
    (latent : Fin body → ℤ) (bodyPlacement : Equiv.Perm (Fin body))
    (attachment : Leg → Fin body) (second primary : Leg → ℤ)
    (queue : Finset (Fin body)) (hqueue : queue.card = modulus) (scalar : ℤ) :
    (∑ vertex, ((assembledEndpoint centers shift ((modulus : ℤ) - 1) latent bodyPlacement
      attachment second primary queue scalar vertex : ℤ) : ZMod modulus)) =
      (((∑ vertex, centers vertex) + (∑ leg, shift leg) : ℤ) : ZMod modulus) -
        (Fintype.card Leg : ZMod modulus) := by
  rw [← Int.cast_sum, integer_endpoint_sum modulus centers shift latent bodyPlacement
    attachment second primary queue hqueue scalar]
  push_cast
  simp [sub_eq_add_neg]

/-- A permutation relabels the full endpoint vector and preserves its
charge, including when the permutation is itself public randomness. -/
def relabelEndpoint {Index : Type*} (permutation : Equiv.Perm Index)
    (endpoint : Index → G) (vertex : Index) : G := endpoint (permutation.symm vertex)

theorem sum_relabelEndpoint {Index : Type*} [Fintype Index]
    (permutation : Equiv.Perm Index) (endpoint : Index → G) :
    ∑ vertex, relabelEndpoint permutation endpoint vertex = ∑ vertex, endpoint vertex :=
  permutation.symm.sum_comp endpoint

/-- Pointwise equivalence of the public test and membership of the
complete protected endpoint in the zero-sum hyperplane, after the final
common relabeling. Every remaining random variable is arbitrary. -/
theorem public_charge_iff_zeroSum (modulus : ℕ) (centers : Fin body → ℤ) (shift : Leg → ℤ)
    (latent : Fin body → ℤ) (bodyPlacement : Equiv.Perm (Fin body))
    (attachment : Leg → Fin body) (second primary : Leg → ℤ)
    (queue : Finset (Fin body)) (hqueue : queue.card = modulus) (scalar : ℤ)
    (finalRelabeling : Equiv.Perm (EndpointIndex body Leg)) :
    (∑ vertex, relabelEndpoint finalRelabeling
      (fun index => ((assembledEndpoint centers shift ((modulus : ℤ) - 1) latent bodyPlacement
        attachment second primary queue scalar index : ℤ) : ZMod modulus)) vertex) = 0 ↔
      PublicChargeTest modulus centers shift := by
  rw [sum_relabelEndpoint, endpoint_charge modulus centers shift latent bodyPlacement
    attachment second primary queue hqueue scalar]
  exact sub_eq_zero

end PublicCharge

end CurrentAFT
