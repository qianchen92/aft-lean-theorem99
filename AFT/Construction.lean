import AFT.Geometry
import AFT.Affine
import AFT.TransportBound

/-!
# Concrete endpoint-to-zero-fiber theorem for V7's rounding matrix

Unlike the generic probability lemma, the pullback here is the proved
equivalence for the actual path rounding matrix, and the target is genuinely
uniform on its carry-label zero fiber. The endpoint error and bad-carry
probability remain explicit hypotheses: Section 9 must supply those estimates.
-/

namespace AFT

open scoped Classical BigOperators

noncomputable instance endpointHyperplaneFintype (n q : ℕ) [NeZero q] :
    Fintype (EndpointHyperplane n q) := by unfold EndpointHyperplane; infer_instance

instance endpointHyperplaneNonempty (n q : ℕ) : Nonempty (EndpointHyperplane n q) :=
  ⟨⟨0, by simp⟩⟩

noncomputable instance zeroFiberFintype (n q : ℕ) [NeZero q]
    (column : Fin (n + 1) → ℤ) : Fintype (ZeroFiber n q column) := by
  unfold ZeroFiber
  infer_instance

instance zeroFiberNonempty (n q : ℕ) (column : Fin (n + 1) → ℤ) :
    Nonempty (ZeroFiber n q column) := by
  refine ⟨⟨0, ?_⟩⟩
  simp [fiberLabel, integerLabel, liftCoordinates, roundingLoad, canonicalCarry, totalCharge]
  change (∑ i : Fin (n + 1), ((pathLoad n 0 i / (q : ℤ) : ℤ) : ZMod q)) = 0
  simp

/-- Uniform on the actual zero fiber, embedded in the ambient residue space. -/
noncomputable def uniformZeroFiber (n q : ℕ) [NeZero q]
    (column : Fin (n + 1) → ℤ) : FiniteDist ((Fin n → ZMod q) × ZMod q) :=
  (FiniteDist.uniform (ZeroFiber n q column)).map Subtype.val

/-- The canonical endpoint bijection carries the uniform hyperplane law to
the uniform zero-fiber law, not merely to an abstract reference distribution. -/
theorem canonical_uniform_transport (n q : ℕ) [NeZero q]
    (column : Fin (n + 1) → ℤ) (hcolumn : totalCharge column = (q : ℤ)) :
    (FiniteDist.uniform (EndpointHyperplane n q)).map
        (fun endpoint => (canonicalEndpointEquiv n q column hcolumn endpoint).val) =
      uniformZeroFiber n q column := by
  rw [← FiniteDist.map_map]
  rw [FiniteDist.uniform_map_equiv]
  rfl

/-- V7 Lemma 6.12 for the concrete rounding map, with arbitrary finite joint
randomness and the actual integer carry. It applies to any finite sampler's
affine outputs. Gaussian residues themselves form a finite source space. -/
theorem concrete_endpoint_carry_bound {Sample : Type*} [Fintype Sample]
    (n q : ℕ) [NeZero q] (column : Fin (n + 1) → ℤ)
    (hcolumn : totalCharge column = (q : ℤ))
    (randomness : FiniteDist Sample) (integerOutput : Sample → (Fin n → ℤ) × ℤ)
    {endpointError carryError : ℝ}
    (hendpoint : FiniteDist.TVBound
      (randomness.map (fun sample => endpointProjection n q column hcolumn
        (reduceCoordinates n q (integerOutput sample))))
      (FiniteDist.uniform (EndpointHyperplane n q)) endpointError)
    (hcarry : (∑ sample, if (q : ℤ) ∣
      totalCharge (canonicalCarry n q (roundingLoad n column (integerOutput sample)))
      then 0 else randomness.weight sample) ≤ carryError) :
    FiniteDist.TVBound (randomness.map (fun sample => reduceCoordinates n q (integerOutput sample)))
      (uniformZeroFiber n q column) (endpointError + carryError) := by
  have h := FiniteDist.endpoint_carry_bound randomness
    (fun sample => reduceCoordinates n q (integerOutput sample))
    (fun sample => endpointProjection n q column hcolumn
      (reduceCoordinates n q (integerOutput sample)))
    (fun endpoint => (canonicalEndpointEquiv n q column hcolumn endpoint).val)
    (FiniteDist.uniform (EndpointHyperplane n q))
    (fun sample => ¬ (q : ℤ) ∣
      totalCharge (canonicalCarry n q (roundingLoad n column (integerOutput sample))))
    (fun sample hgood => (canonical_endpoint_agreement_iff_carry n q column hcolumn
      (integerOutput sample)).2 (not_not.mp hgood))
    hendpoint (by simpa only [ite_not] using hcarry)
  rwa [canonical_uniform_transport] at h

/-- The same theorem specialized to the first-`q`-vertices injection column
of Definition 6.9. Here the number of vertices is `n + 1`. -/
theorem explicit_rounding_endpoint_carry_bound {Sample : Type*} [Fintype Sample]
    (n q : ℕ) [NeZero q] (hq : q ≤ n + 1)
    (randomness : FiniteDist Sample) (integerOutput : Sample → (Fin n → ℤ) × ℤ)
    {endpointError carryError : ℝ}
    (hendpoint : FiniteDist.TVBound
      (randomness.map (fun sample => endpointProjection n q (injectionColumn n q)
        (totalCharge_injectionColumn n q hq) (reduceCoordinates n q (integerOutput sample))))
      (FiniteDist.uniform (EndpointHyperplane n q)) endpointError)
    (hcarry : (∑ sample, if (q : ℤ) ∣
      totalCharge (canonicalCarry n q (roundingLoad n (injectionColumn n q) (integerOutput sample)))
      then 0 else randomness.weight sample) ≤ carryError) :
    FiniteDist.TVBound (randomness.map (fun sample => reduceCoordinates n q (integerOutput sample)))
      (uniformZeroFiber n q (injectionColumn n q)) (endpointError + carryError) :=
  concrete_endpoint_carry_bound n q (injectionColumn n q)
    (totalCharge_injectionColumn n q hq) randomness integerOutput hendpoint hcarry

end AFT
