import AFT.Algebra

/-!
# Canonical endpoint and carry identities

The modular output below is the coordinatewise reduction of the actual integer
rounding preimage. No quotient-isomorphism or carry-correctness hypothesis is
assumed. We prove the exact carry criterion for the fixed path rounding map.
-/

namespace AFT

/-- Coordinatewise reduction of an integral transport output. -/
def reduceCoordinates (n q : ℕ) (x : (Fin n → ℤ) × ℤ) :
    (Fin n → ZMod q) × ZMod q := (fun i => (x.1 i : ZMod q), (x.2 : ZMod q))

/-- Equality of modular outputs is exactly divisibility of their integer difference. -/
theorem reduceCoordinates_eq_iff (n q : ℕ) (x y : (Fin n → ℤ) × ℤ) :
    reduceCoordinates n q x = reduceCoordinates n q y ↔
      ∃ k : (Fin n → ℤ) × ℤ, x - y = (q : ℤ) • k := by
  constructor
  · intro h
    have he : ∀ i, (q : ℤ) ∣ x.1 i - y.1 i := by
      intro i
      apply (ZMod.intCast_eq_intCast_iff_dvd_sub (y.1 i) (x.1 i) q).1
      exact (congrArg (fun v : (Fin n → ZMod q) × ZMod q => v.1 i) h).symm
    choose e he using he
    have ha : (q : ℤ) ∣ x.2 - y.2 :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub y.2 x.2 q).1 (congrArg Prod.snd h).symm
    obtain ⟨a, ha⟩ := ha
    refine ⟨(e, a), Prod.ext ?_ ?_⟩
    · funext i
      exact he i
    · exact ha
  · rintro ⟨k, hk⟩
    apply Prod.ext
    · funext i
      apply Eq.symm
      apply (ZMod.intCast_eq_intCast_iff_dvd_sub (y.1 i) (x.1 i) q).2
      exact ⟨k.1 i, congrArg (fun v : (Fin n → ℤ) × ℤ => v.1 i) hk⟩
    · apply Eq.symm
      apply (ZMod.intCast_eq_intCast_iff_dvd_sub y.2 x.2 q).2
      exact ⟨k.2, congrArg Prod.snd hk⟩

/-- Canonical integer endpoint representative, entrywise in `[0,q)`. -/
def canonicalEndpoint (n q : ℕ) (load : Fin (n + 1) → ℤ) : Fin (n + 1) → ℤ :=
  fun i => load i % (q : ℤ)

/-- Canonical carry; integer division agrees with floor division for positive `q`. -/
def canonicalCarry (n q : ℕ) (load : Fin (n + 1) → ℤ) : Fin (n + 1) → ℤ :=
  fun i => load i / (q : ℤ)

/-- Exact integer division-with-remainder identity, including negative loads. -/
theorem canonical_endpoint_carry (n q : ℕ) (load : Fin (n + 1) → ℤ) :
    load - canonicalEndpoint n q load = (q : ℤ) • canonicalCarry n q load := by
  funext i
  change load i - load i % (q : ℤ) = (q : ℤ) * (load i / (q : ℤ))
  have h := Int.emod_add_mul_ediv (load i) (q : ℤ)
  omega

/-- The canonical endpoint representative is in the box. -/
theorem canonicalEndpoint_in_box (n q : ℕ) (hq : 0 < q)
    (load : Fin (n + 1) → ℤ) (i : Fin (n + 1)) :
    0 ≤ canonicalEndpoint n q load i ∧ canonicalEndpoint n q load i < (q : ℤ) := by
  exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩

/-- Removing the canonical carry preserves membership in the rounding image lattice. -/
theorem canonicalEndpoint_mem_lattice (n q : ℕ) (load : Fin (n + 1) → ℤ)
    (hload : (q : ℤ) ∣ totalCharge load) :
    (q : ℤ) ∣ totalCharge (canonicalEndpoint n q load) := by
  have h := congrArg totalCharge (canonical_endpoint_carry n q load)
  rw [totalCharge_sub, totalCharge_smul] at h
  have hd : (q : ℤ) ∣ totalCharge load - totalCharge (canonicalEndpoint n q load) :=
    ⟨totalCharge (canonicalCarry n q load), h⟩
  exact (dvd_sub_right hload).1 hd

/-- Integral canonical pullback through the fixed rounding map. -/
noncomputable def canonicalPullback (n q : ℕ) (hq : q ≠ 0)
    (c : Fin (n + 1) → ℤ) (hc : totalCharge c = (q : ℤ))
    (load : Fin (n + 1) → ℤ) (hload : (q : ℤ) ∣ totalCharge load) :
    (Fin n → ℤ) × ℤ :=
  (roundingCoordinates n q (by exact_mod_cast hq) c hc).symm
    ⟨canonicalEndpoint n q load, canonicalEndpoint_mem_lattice n q load hload⟩

@[simp] theorem roundingLoad_canonicalPullback (n q : ℕ) (hq : q ≠ 0)
    (c : Fin (n + 1) → ℤ) (hc : totalCharge c = (q : ℤ))
    (load : Fin (n + 1) → ℤ) (hload : (q : ℤ) ∣ totalCharge load) :
    roundingLoad n c (canonicalPullback n q hq c hc load hload) =
      canonicalEndpoint n q load := by
  change ((roundingCoordinates n q (by exact_mod_cast hq) c hc)
    ((roundingCoordinates n q (by exact_mod_cast hq) c hc).symm _)
      : Fin (n + 1) → ℤ) = _
  rw [LinearEquiv.apply_symm_apply]

/-- Additivity of the actual rounding map. -/
theorem roundingLoad_sub (n : ℕ) (c : Fin (n + 1) → ℤ)
    (x y : (Fin n → ℤ) × ℤ) :
    roundingLoad n c (x - y) = roundingLoad n c x - roundingLoad n c y := by
  simp only [roundingLoad, Prod.fst_sub, Prod.snd_sub, sub_smul]
  have hp : pathLoad n (x.1 - y.1) = pathLoad n x.1 - pathLoad n y.1 :=
    (pathIncidence n).map_sub x.1 y.1
  rw [hp]
  abel

theorem roundingLoad_smul (n : ℕ) (c : Fin (n + 1) → ℤ)
    (a : ℤ) (x : (Fin n → ℤ) × ℤ) :
    roundingLoad n c (a • x) = a • roundingLoad n c x := by
  simp [roundingLoad, smul_add, smul_smul]

/-- Exact canonical carry criterion in V7: the reduced integral output equals
its endpoint's canonical pullback exactly when the canonical carry is in the
rounding image lattice. The statement does not assume a probability estimate. -/
theorem canonical_carry_criterion (n q : ℕ) (hq : q ≠ 0)
    (c : Fin (n + 1) → ℤ) (hc : totalCharge c = (q : ℤ))
    (x : (Fin n → ℤ) × ℤ) :
    let load := roundingLoad n c x
    let hload := (rounding_image_lattice n q c hc load).1 ⟨x, rfl⟩
    reduceCoordinates n q x =
      reduceCoordinates n q (canonicalPullback n q hq c hc load hload) ↔
        (q : ℤ) ∣ totalCharge (canonicalCarry n q load) := by
  dsimp only
  let y := canonicalPullback n q hq c hc (roundingLoad n c x)
    ((rounding_image_lattice n q c hc _).1 ⟨x, rfl⟩)
  have hy : roundingLoad n c y = canonicalEndpoint n q (roundingLoad n c x) :=
    roundingLoad_canonicalPullback n q hq c hc _ _
  have hdiff : roundingLoad n c (x - y) =
      (q : ℤ) • canonicalCarry n q (roundingLoad n c x) := by
    rw [roundingLoad_sub, hy]
    exact canonical_endpoint_carry n q _
  change reduceCoordinates n q x = reduceCoordinates n q y ↔ _
  rw [reduceCoordinates_eq_iff]
  constructor
  · rintro ⟨k, hk⟩
    rw [hk, roundingLoad_smul] at hdiff
    have hkload : roundingLoad n c k = canonicalCarry n q (roundingLoad n c x) := by
      funext i
      have hi := congrFun hdiff i
      exact mul_left_cancel₀ (by exact_mod_cast hq : (q : ℤ) ≠ 0) hi
    exact (rounding_image_lattice n q c hc _).1 ⟨k, hkload⟩
  · intro h
    obtain ⟨k, hk⟩ := (rounding_image_lattice n q c hc _).2 h
    refine ⟨k, roundingLoad_injective n q (by exact_mod_cast hq) c hc ?_⟩
    rw [roundingLoad_smul, hk, hdiff]

end AFT

namespace AFT

open scoped BigOperators

/-- Canonical lift of a modular coordinate vector, in the coordinate order
(edges, injection coordinate) used throughout the formalization. -/
def liftCoordinates (n q : ℕ) (x : (Fin n → ZMod q) × ZMod q) :
    (Fin n → ℤ) × ℤ := (fun i => (x.1 i).val, x.2.val)

@[simp] theorem reduce_liftCoordinates (n q : ℕ) [NeZero q]
    (x : (Fin n → ZMod q) × ZMod q) :
    reduceCoordinates n q (liftCoordinates n q x) = x := by
  ext i <;> simp [reduceCoordinates, liftCoordinates]

/-- The concrete one-dimensional LAR label on any integer lift. -/
def integerLabel (n q : ℕ) (c : Fin (n + 1) → ℤ)
    (x : (Fin n → ℤ) × ℤ) : ZMod q :=
  (totalCharge (canonicalCarry n q (roundingLoad n c x)) : ZMod q)

/-- The label is independent of the chosen integer lift. -/
theorem integerLabel_congr (n q : ℕ) [NeZero q]
    (c : Fin (n + 1) → ℤ) (hc : totalCharge c = (q : ℤ))
    (x y : (Fin n → ℤ) × ℤ)
    (h : reduceCoordinates n q x = reduceCoordinates n q y) :
    integerLabel n q c x = integerLabel n q c y := by
  obtain ⟨k, hk⟩ := (reduceCoordinates_eq_iff n q x y).1 h
  have hr : roundingLoad n c x = roundingLoad n c y + (q : ℤ) • roundingLoad n c k := by
    have ht := congrArg (roundingLoad n c) hk
    rw [roundingLoad_sub, roundingLoad_smul] at ht
    exact sub_eq_iff_eq_add.mp ht |>.trans (add_comm _ _)
  have hcarry : canonicalCarry n q (roundingLoad n c x) =
      canonicalCarry n q (roundingLoad n c y) + roundingLoad n c k := by
    funext i
    rw [hr]
    exact Int.add_mul_ediv_left _ _ (by exact_mod_cast NeZero.ne q)
  unfold integerLabel
  rw [hcarry, totalCharge_add, Int.cast_add]
  have hd := (rounding_image_lattice n q c hc (roundingLoad n c k)).1 ⟨k, rfl⟩
  rw [(ZMod.intCast_zmod_eq_zero_iff_dvd _ q).2 hd, add_zero]

/-- LAR label on the residue vector, computed using its canonical lift. -/
def fiberLabel (n q : ℕ) (c : Fin (n + 1) → ℤ)
    (x : (Fin n → ZMod q) × ZMod q) : ZMod q :=
  integerLabel n q c (liftCoordinates n q x)

@[simp] theorem fiberLabel_reduceCoordinates (n q : ℕ) [NeZero q]
    (c : Fin (n + 1) → ℤ) (hc : totalCharge c = (q : ℤ))
    (x : (Fin n → ℤ) × ℤ) :
    fiberLabel n q c (reduceCoordinates n q x) = integerLabel n q c x := by
  apply integerLabel_congr n q c hc
  exact reduce_liftCoordinates n q _

/-- Actual zero fiber, defined by the canonical carry label. -/
def ZeroFiber (n q : ℕ) (c : Fin (n + 1) → ℤ) :=
  {x : (Fin n → ZMod q) × ZMod q // fiberLabel n q c x = 0}

/-- The zero-sum endpoint hyperplane over `ZMod q`. -/
def EndpointHyperplane (n q : ℕ) :=
  {r : Fin (n + 1) → ZMod q // ∑ i, r i = 0}

/-- Canonical integer lift of an endpoint. -/
def endpointLift (n q : ℕ) (r : EndpointHyperplane n q) : Fin (n + 1) → ℤ :=
  fun i => (r.val i).val

theorem endpointLift_mem_lattice (n q : ℕ) [NeZero q]
    (r : EndpointHyperplane n q) : (q : ℤ) ∣ totalCharge (endpointLift n q r) := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).1
  simpa [totalCharge, endpointLift] using r.property

@[simp] theorem canonicalCarry_endpointLift (n q : ℕ) [NeZero q]
    (r : EndpointHyperplane n q) : canonicalCarry n q (endpointLift n q r) = 0 := by
  funext i
  change ((r.val i).val : ℤ) / (q : ℤ) = 0
  apply Int.ediv_eq_zero_of_lt
  · exact_mod_cast Nat.zero_le _
  · exact_mod_cast ZMod.val_lt (r.val i)

/-- Integral preimage of a canonical endpoint lift. -/
noncomputable def endpointIntegralPreimage (n q : ℕ) [NeZero q]
    (c : Fin (n + 1) → ℤ) (hc : totalCharge c = (q : ℤ))
    (r : EndpointHyperplane n q) : (Fin n → ℤ) × ℤ :=
  (roundingCoordinates n q (by exact_mod_cast NeZero.ne q) c hc).symm
    ⟨endpointLift n q r, endpointLift_mem_lattice n q r⟩

@[simp] theorem roundingLoad_endpointIntegralPreimage (n q : ℕ) [NeZero q]
    (c : Fin (n + 1) → ℤ) (hc : totalCharge c = (q : ℤ))
    (r : EndpointHyperplane n q) :
    roundingLoad n c (endpointIntegralPreimage n q c hc r) = endpointLift n q r := by
  change ((roundingCoordinates n q (by exact_mod_cast NeZero.ne q) c hc)
    ((roundingCoordinates n q (by exact_mod_cast NeZero.ne q) c hc).symm _)
      : Fin (n + 1) → ℤ) = _
  rw [LinearEquiv.apply_symm_apply]

/-- Canonical endpoint pullback into the actual zero fiber. -/
noncomputable def zeroFiberPullback (n q : ℕ) [NeZero q]
    (c : Fin (n + 1) → ℤ) (hc : totalCharge c = (q : ℤ))
    (r : EndpointHyperplane n q) : ZeroFiber n q c :=
  ⟨reduceCoordinates n q (endpointIntegralPreimage n q c hc r), by
    rw [fiberLabel_reduceCoordinates n q c hc]
    simp [integerLabel, totalCharge]⟩

/-- Endpoint residue of a modular output, with its zero-sum property proved from
the integral rounding image lattice. -/
def endpointProjection (n q : ℕ)
    (c : Fin (n + 1) → ℤ) (hc : totalCharge c = (q : ℤ))
    (x : (Fin n → ZMod q) × ZMod q) : EndpointHyperplane n q :=
  ⟨fun i => (roundingLoad n c (liftCoordinates n q x) i : ZMod q), by
    have hd := (rounding_image_lattice n q c hc
      (roundingLoad n c (liftCoordinates n q x))).1 ⟨_, rfl⟩
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).2 hd
    simpa [totalCharge] using hz⟩

/-- Rounding commutes with changing integer representatives modulo `q`. -/
theorem roundingLoad_reduce_congr (n q : ℕ) (c : Fin (n + 1) → ℤ)
    (x y : (Fin n → ℤ) × ℤ)
    (h : reduceCoordinates n q x = reduceCoordinates n q y) (i : Fin (n + 1)) :
    (roundingLoad n c x i : ZMod q) = (roundingLoad n c y i : ZMod q) := by
  obtain ⟨k, hk⟩ := (reduceCoordinates_eq_iff n q x y).1 h
  have hr := congrArg (roundingLoad n c) hk
  rw [roundingLoad_sub, roundingLoad_smul] at hr
  apply Eq.symm
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ q).2
  exact ⟨roundingLoad n c k i, congrFun hr i⟩

@[simp] theorem endpointProjection_reduceCoordinates (n q : ℕ) [NeZero q]
    (c : Fin (n + 1) → ℤ) (hc : totalCharge c = (q : ℤ))
    (x : (Fin n → ℤ) × ℤ) (i : Fin (n + 1)) :
    (endpointProjection n q c hc (reduceCoordinates n q x)).val i =
      (roundingLoad n c x i : ZMod q) :=
  roundingLoad_reduce_congr n q c _ x (reduce_liftCoordinates n q _) i

/-- The endpoint projection recovers the input endpoint after canonical pullback. -/
theorem endpointProjection_zeroFiberPullback (n q : ℕ) [NeZero q]
    (c : Fin (n + 1) → ℤ) (hc : totalCharge c = (q : ℤ))
    (r : EndpointHyperplane n q) :
    endpointProjection n q c hc (zeroFiberPullback n q c hc r).val = r := by
  apply Subtype.ext
  funext i
  simp [zeroFiberPullback, endpointLift]

/-- Lifting the actual endpoint residue gives precisely the canonical remainder. -/
theorem endpointLift_projection (n q : ℕ) [NeZero q]
    (c : Fin (n + 1) → ℤ) (hc : totalCharge c = (q : ℤ))
    (x : (Fin n → ZMod q) × ZMod q) :
    endpointLift n q (endpointProjection n q c hc x) =
      canonicalEndpoint n q (roundingLoad n c (liftCoordinates n q x)) := by
  funext i
  exact ZMod.val_intCast _

/-- Every element of the actual zero fiber is recovered by the canonical endpoint
pullback. This uses the proved carry criterion, rather than assuming the bijection. -/
theorem zeroFiberPullback_endpointProjection (n q : ℕ) [NeZero q]
    (c : Fin (n + 1) → ℤ) (hc : totalCharge c = (q : ℤ))
    (x : ZeroFiber n q c) :
    zeroFiberPullback n q c hc (endpointProjection n q c hc x.val) = x := by
  apply Subtype.ext
  let z := liftCoordinates n q x.val
  have hcarry : (q : ℤ) ∣ totalCharge (canonicalCarry n q (roundingLoad n c z)) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).1 x.property
  have hcriterion := (canonical_carry_criterion n q (NeZero.ne q) c hc z).2 hcarry
  have heq : endpointIntegralPreimage n q c hc (endpointProjection n q c hc x.val) =
      canonicalPullback n q (NeZero.ne q) c hc (roundingLoad n c z)
        ((rounding_image_lattice n q c hc _).1 ⟨z, rfl⟩) := by
    apply roundingLoad_injective n q (by exact_mod_cast NeZero.ne q) c hc
    rw [roundingLoad_endpointIntegralPreimage, roundingLoad_canonicalPullback,
      endpointLift_projection]
  change reduceCoordinates n q (endpointIntegralPreimage n q c hc
    (endpointProjection n q c hc x.val)) = x.val
  rw [heq, ← hcriterion]
  exact reduce_liftCoordinates n q x.val

/-- V7's canonical endpoint parametrization, proved as an actual equivalence
between the zero-sum residue hyperplane and the carry-label zero fiber. -/
noncomputable def canonicalEndpointEquiv (n q : ℕ) [NeZero q]
    (c : Fin (n + 1) → ℤ) (hc : totalCharge c = (q : ℤ)) :
    EndpointHyperplane n q ≃ ZeroFiber n q c where
  toFun := zeroFiberPullback n q c hc
  invFun := fun x => endpointProjection n q c hc x.val
  left_inv := endpointProjection_zeroFiberPullback n q c hc
  right_inv := zeroFiberPullback_endpointProjection n q c hc

end AFT

namespace AFT

/-- Direct integration interface: agreement with the endpoint equivalence is
exactly membership in the actual zero fiber. -/
theorem canonical_endpoint_agreement_iff (n q : ℕ) [NeZero q]
    (c : Fin (n + 1) → ℤ) (hc : totalCharge c = (q : ℤ))
    (x : (Fin n → ZMod q) × ZMod q) :
    x = (canonicalEndpointEquiv n q c hc (endpointProjection n q c hc x)).val ↔
      fiberLabel n q c x = 0 := by
  constructor
  · intro h
    rw [h]
    exact (canonicalEndpointEquiv n q c hc (endpointProjection n q c hc x)).property
  · intro h
    exact (congrArg Subtype.val
      (zeroFiberPullback_endpointProjection n q c hc ⟨x, h⟩)).symm

/-- The carry condition with the actual endpoint equivalence, ready to use in
an endpoint-and-carry probability bound. -/
theorem canonical_endpoint_agreement_iff_carry (n q : ℕ) [NeZero q]
    (c : Fin (n + 1) → ℤ) (hc : totalCharge c = (q : ℤ))
    (x : (Fin n → ℤ) × ℤ) :
    reduceCoordinates n q x =
      (canonicalEndpointEquiv n q c hc
        (endpointProjection n q c hc (reduceCoordinates n q x))).val ↔
      (q : ℤ) ∣ totalCharge (canonicalCarry n q (roundingLoad n c x)) := by
  rw [canonical_endpoint_agreement_iff, fiberLabel_reduceCoordinates n q c hc]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd _ q

end AFT
