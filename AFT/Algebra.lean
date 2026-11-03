import Mathlib

/-!
# Integral algebra behind the V7 affine fiber transport construction

Vertices of the concrete path are `Fin (n + 1)` and its edges are `Fin n`.
All lattices and preimages in this file are over the integers. General tree
transport is stated in basis coordinates; the graph-to-basis bridge for an
arbitrary spanning tree is deliberately not asserted here.
-/

namespace AFT

open scoped BigOperators

/-- The signed path incidence map: each edge goes from vertex `i` to `i+1`. -/
def pathLoad : (n : ℕ) → (Fin n → ℤ) → (Fin (n + 1) → ℤ)
  | 0, _ => 0
  | n + 1, e => Fin.cons (e 0)
      (fun i => pathLoad n (Fin.tail e) i - if i = 0 then e 0 else 0)

@[simp] theorem pathLoad_zero (n : ℕ) : pathLoad n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [pathLoad]
      · have ht : Fin.tail (0 : Fin (n + 1) → ℤ) = 0 := rfl
        simp [pathLoad, ht, ih]

@[simp] theorem pathLoad_add (n : ℕ) (e f : Fin n → ℤ) :
    pathLoad n (e + f) = pathLoad n e + pathLoad n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have ht : Fin.tail (e + f) = Fin.tail e + Fin.tail f := rfl
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [pathLoad]
      · simp only [pathLoad, Fin.cons_succ, ht, ih, Pi.add_apply]
        split_ifs <;> ring

@[simp] theorem pathLoad_smul (n : ℕ) (a : ℤ) (e : Fin n → ℤ) :
    pathLoad n (a • e) = a • pathLoad n e := by
  induction n with
  | zero => simp [pathLoad]
  | succ n ih =>
      have ht : Fin.tail (a • e) = a • Fin.tail e := rfl
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [pathLoad]
      · simp only [pathLoad, Fin.cons_succ, ht, ih, Pi.smul_apply, smul_eq_mul]
        split_ifs <;> ring

/-- The integral linear map represented by the signed path incidence matrix. -/
def pathIncidence (n : ℕ) : (Fin n → ℤ) →ₗ[ℤ] (Fin (n + 1) → ℤ) where
  toFun := pathLoad n
  map_add' := pathLoad_add n
  map_smul' := pathLoad_smul n

/-- Coordinate sum, i.e. total integer charge. -/
def totalCharge {ι : Type*} [Fintype ι] (v : ι → ℤ) : ℤ := ∑ i, v i

@[simp] theorem totalCharge_add {ι : Type*} [Fintype ι] (u v : ι → ℤ) :
    totalCharge (u + v) = totalCharge u + totalCharge v := by
  simp [totalCharge, Finset.sum_add_distrib]

@[simp] theorem totalCharge_sub {ι : Type*} [Fintype ι] (u v : ι → ℤ) :
    totalCharge (u - v) = totalCharge u - totalCharge v := by
  simp [totalCharge, Finset.sum_sub_distrib]

@[simp] theorem totalCharge_smul {ι : Type*} [Fintype ι] (a : ℤ) (v : ι → ℤ) :
    totalCharge (a • v) = a * totalCharge v := by
  simp [totalCharge, Finset.mul_sum]

@[simp] theorem totalCharge_pathLoad (n : ℕ) (e : Fin n → ℤ) :
    totalCharge (pathLoad n e) = 0 := by
  induction n with
  | zero => simp [pathLoad, totalCharge]
  | succ n ih =>
      change (∑ i, Fin.cons (e 0)
        (fun j => pathLoad n (Fin.tail e) j - if j = 0 then e 0 else 0) i) = 0
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [Finset.sum_sub_distrib]
      change e 0 + ((totalCharge (pathLoad n (Fin.tail e))) - _) = 0
      simp [ih]

/-- The path edge coefficients are uniquely determined by their divergence. -/
theorem pathLoad_injective (n : ℕ) : Function.Injective (pathLoad n) := by
  induction n with
  | zero => intro e f h; exact Subsingleton.elim _ _
  | succ n ih =>
      intro e f h
      have h0 : e 0 = f 0 := congrFun h 0
      have ht : pathLoad n (Fin.tail e) = pathLoad n (Fin.tail f) := by
        funext i
        have hi := congrFun h i.succ
        simp only [pathLoad, Fin.cons_succ, h0] at hi
        exact sub_left_inj.mp hi
      have he := ih ht
      funext i
      exact Fin.cases h0 (fun j => congrFun he j) i

/-- Every zero-sum integer vertex load has integral path edge coefficients. -/
theorem exists_pathLoad (n : ℕ) (v : Fin (n + 1) → ℤ)
    (hv : totalCharge v = 0) : ∃ e, pathLoad n e = v := by
  induction n with
  | zero =>
      refine ⟨0, ?_⟩
      funext i
      have hi : i = 0 := Fin.ext (by omega)
      subst i
      simpa [pathLoad, totalCharge] using hv.symm
  | succ n ih =>
      let w : Fin (n + 1) → ℤ := fun i => v i.succ + if i = 0 then v 0 else 0
      have hw : totalCharge w = 0 := by
        have hv' : v 0 + (∑ i : Fin (n + 1), v i.succ) = 0 := by
          simpa [totalCharge, Fin.sum_univ_succ] using hv
        simp only [w, totalCharge, Finset.sum_add_distrib]
        simpa [add_comm] using hv'
      obtain ⟨e, he⟩ := ih w hw
      refine ⟨Fin.cons (v 0) e, ?_⟩
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [pathLoad]
      · simp [pathLoad, he, w]

/-- V7 Lemma `tree-incidence-basis`, proved for the actual fixed rounding path. -/
theorem path_integral_basis (n : ℕ) (v : Fin (n + 1) → ℤ) :
    (∃! e, pathLoad n e = v) ↔ totalCharge v = 0 := by
  constructor
  · rintro ⟨e, rfl, _⟩
    exact totalCharge_pathLoad n e
  · intro h
    obtain ⟨e, he⟩ := exists_pathLoad n v h
    exact ⟨e, he, fun f hf => pathLoad_injective n (hf.trans he.symm)⟩

/-- Simultaneous injection at the first `q` vertices, exactly as in V7. -/
def injectionColumn (n q : ℕ) : Fin (n + 1) → ℤ :=
  fun i => if i.val < q then 1 else 0

theorem totalCharge_injectionColumn (n q : ℕ) (hq : q ≤ n + 1) :
    totalCharge (injectionColumn n q) = (q : ℤ) := by
  simp [totalCharge, injectionColumn, Fin.card_filter_val_lt,
    Nat.min_eq_right hq]

/-- The fixed rounding matrix applied to path coordinates and the injection coordinate. -/
def roundingLoad (n : ℕ) (c : Fin (n + 1) → ℤ)
    (x : (Fin n → ℤ) × ℤ) : Fin (n + 1) → ℤ :=
  pathLoad n x.1 + x.2 • c

/-- V7's image lattice characterization, with any injection column of total charge `q`. -/
theorem rounding_image_lattice (n : ℕ) (q : ℤ) (c : Fin (n + 1) → ℤ)
    (hc : totalCharge c = q) (v : Fin (n + 1) → ℤ) :
    (∃ x, roundingLoad n c x = v) ↔ q ∣ totalCharge v := by
  constructor
  · rintro ⟨⟨e, a⟩, rfl⟩
    simp [roundingLoad, hc, dvd_mul_left]
  · rintro ⟨a, ha⟩
    have hw : totalCharge (v - a • c) = 0 := by
      simp [hc, ha, mul_comm]
    obtain ⟨e, he⟩ := exists_pathLoad n (v - a • c) hw
    refine ⟨(e, a), ?_⟩
    simp [roundingLoad, he]

/-- In particular this is the image lattice of the explicit V7 rounding matrix. -/
theorem explicit_rounding_image_lattice (n q : ℕ) (hq : q ≤ n + 1)
    (v : Fin (n + 1) → ℤ) :
    (∃ x, roundingLoad n (injectionColumn n q) x = v) ↔ (q : ℤ) ∣ totalCharge v :=
  rounding_image_lattice n q _ (totalCharge_injectionColumn n q hq) v

end AFT

namespace AFT

/-- The root lattice of integer zero-sum loads. -/
def zeroSumLattice (n : ℕ) : Submodule ℤ (Fin (n + 1) → ℤ) where
  carrier := {v | totalCharge v = 0}
  zero_mem' := by simp [totalCharge]
  add_mem' := by intro u v hu hv; simpa using (totalCharge_add u v).trans (by rw [hu, hv]; rfl)
  smul_mem' := by
    intro a v hv
    change totalCharge v = 0 at hv
    change totalCharge (a • v) = 0
    rw [totalCharge_smul, hv, mul_zero]

@[simp] theorem mem_zeroSumLattice (n : ℕ) (v : Fin (n + 1) → ℤ) :
    v ∈ zeroSumLattice n ↔ totalCharge v = 0 := Iff.rfl

/-- The path basis as an integral linear equivalence, with no graph hypothesis. -/
noncomputable def pathBasis (n : ℕ) : (Fin n → ℤ) ≃ₗ[ℤ] zeroSumLattice n :=
  LinearEquiv.ofBijective
    ((pathIncidence n).codRestrict (zeroSumLattice n) (totalCharge_pathLoad n)) (by
      constructor
      · intro e f h
        exact pathLoad_injective n (congrArg Subtype.val h)
      · rintro ⟨v, hv⟩
        obtain ⟨e, he⟩ := exists_pathLoad n v hv
        exact ⟨e, Subtype.ext he⟩)

@[simp] theorem pathBasis_apply (n : ℕ) (e : Fin n → ℤ) :
    (pathBasis n e : Fin (n + 1) → ℤ) = pathLoad n e := rfl

/-- Divisibility lattice; for V7 this is the image of the rounding matrix. -/
def chargeLattice (n : ℕ) (q : ℤ) : Submodule ℤ (Fin (n + 1) → ℤ) where
  carrier := {v | q ∣ totalCharge v}
  zero_mem' := by simp [totalCharge]
  add_mem' := by intro u v hu hv; simpa using dvd_add hu hv
  smul_mem' := by intro a v hv; simpa using dvd_mul_of_dvd_right hv a

@[simp] theorem mem_chargeLattice (n : ℕ) (q : ℤ) (v : Fin (n + 1) → ℤ) :
    v ∈ chargeLattice n q ↔ q ∣ totalCharge v := Iff.rfl

/-- Nonzero total injection makes the integer rounding map injective. -/
theorem roundingLoad_injective (n : ℕ) (q : ℤ) (hq : q ≠ 0)
    (c : Fin (n + 1) → ℤ) (hc : totalCharge c = q) :
    Function.Injective (roundingLoad n c) := by
  rintro ⟨e, a⟩ ⟨f, b⟩ h
  have hs := congrArg totalCharge h
  simp only [roundingLoad, totalCharge_add, totalCharge_pathLoad, totalCharge_smul,
    hc, zero_add] at hs
  have hab : a = b := mul_right_cancel₀ hq hs
  subst b
  have hef : pathLoad n e = pathLoad n f := add_right_cancel h
  exact Prod.ext (pathLoad_injective n hef) rfl

/-- The rounding map is an integral coordinate isomorphism onto its image lattice.
Its inverse supplies the integral preimage used in V7, without rational inverses. -/
noncomputable def roundingCoordinates (n : ℕ) (q : ℤ) (hq : q ≠ 0)
    (c : Fin (n + 1) → ℤ) (hc : totalCharge c = q) :
    ((Fin n → ℤ) × ℤ) ≃ₗ[ℤ] chargeLattice n q :=
  LinearEquiv.ofBijective
    ({ toFun := fun x => ⟨roundingLoad n c x, (rounding_image_lattice n q c hc _).1 ⟨x, rfl⟩⟩
       map_add' := by
         intro x y
         apply Subtype.ext
         change roundingLoad n c (x + y) = roundingLoad n c x + roundingLoad n c y
         simp only [roundingLoad, Prod.fst_add, Prod.snd_add, pathLoad_add, add_smul]
         abel
       map_smul' := by
         intro a x
         apply Subtype.ext
         simp [roundingLoad, pathLoad_smul, smul_add, smul_smul] } :
      ((Fin n → ℤ) × ℤ) →ₗ[ℤ] chargeLattice n q) (by
        constructor
        · intro x y h
          exact roundingLoad_injective n q hq c hc (congrArg Subtype.val h)
        · rintro ⟨v, hv⟩
          obtain ⟨x, hx⟩ := (rounding_image_lattice n q c hc v).2 hv
          exact ⟨x, Subtype.ext hx⟩)

@[simp] theorem roundingCoordinates_apply (n : ℕ) (q : ℤ) (hq : q ≠ 0)
    (c : Fin (n + 1) → ℤ) (hc : totalCharge c = q) (x : (Fin n → ℤ) × ℤ) :
    (roundingCoordinates n q hq c hc x : Fin (n + 1) → ℤ) = roundingLoad n c x := rfl

/-- Every admissible load has exactly one integral preimage. -/
theorem unique_integral_preimage (n : ℕ) (q : ℤ) (hq : q ≠ 0)
    (c : Fin (n + 1) → ℤ) (hc : totalCharge c = q)
    (v : Fin (n + 1) → ℤ) (hv : q ∣ totalCharge v) :
    ∃! x, roundingLoad n c x = v := by
  obtain ⟨x, hx⟩ := (rounding_image_lattice n q c hc v).2 hv
  exact ⟨x, hx, fun y hy => roundingLoad_injective n q hq c hc (hy.trans hx.symm)⟩

/-- Given a zero-sum basis `treeBasis`, change from those edge coordinates to path
coordinates. For a general tree, supplying `treeBasis` is the unproved graph bridge. -/
noncomputable def edgeBasisChange (n : ℕ)
    (treeBasis : (Fin n → ℤ) ≃ₗ[ℤ] zeroSumLattice n) :
    (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ) := treeBasis.trans (pathBasis n).symm

@[simp] theorem pathLoad_edgeBasisChange (n : ℕ)
    (treeBasis : (Fin n → ℤ) ≃ₗ[ℤ] zeroSumLattice n) (e : Fin n → ℤ) :
    pathLoad n (edgeBasisChange n treeBasis e) = (treeBasis e : Fin (n + 1) → ℤ) := by
  change ((pathBasis n) ((pathBasis n).symm (treeBasis e)) : Fin (n + 1) → ℤ) = _
  rw [LinearEquiv.apply_symm_apply]

/-- Explicit block-triangular transport. `B` is the edge-coordinate matrix, `U`
the integral basis change, and `a` the path preimage of the extension-column shift. -/
def blockTransport {R : Type*} [CommRing R] (n : ℕ)
    (U : (Fin n → R) ≃ₗ[R] (Fin n → R))
    (B : (Fin n → R) →ₗ[R] (Fin n → R)) (a : Fin n → R) :
    ((Fin n → R) × R) →ₗ[R] ((Fin n → R) × R) where
  toFun x := (U (B x.1) + x.2 • a, x.2)
  map_add' := by
    intro x y
    ext i <;> simp [add_smul, add_assoc, add_comm, add_left_comm]
  map_smul' := by
    intro r x
    ext i <;> simp [smul_add, smul_smul]

/-- If the edge-coordinate map is invertible over a coefficient ring, so is the
whole transport. Specializing `R` to `ZMod q` gives modular invertibility. -/
def blockTransportEquiv {R : Type*} [CommRing R] (n : ℕ)
    (U B : (Fin n → R) ≃ₗ[R] (Fin n → R)) (a : Fin n → R) :
    ((Fin n → R) × R) ≃ₗ[R] ((Fin n → R) × R) where
  toLinearMap := blockTransport n U B.toLinearMap a
  invFun y := (B.symm (U.symm (y.1 - y.2 • a)), y.2)
  left_inv := by
    intro x
    simp [blockTransport]
  right_inv := by
    intro y
    simp [blockTransport]

/-- The V7 tree-incidence formula holds as an exact integer identity for the
constructed transport. It simultaneously verifies integral coefficients and
compatibility with the fixed rounding matrix. -/
theorem tree_transport_identity (n : ℕ)
    (treeBasis : (Fin n → ℤ) ≃ₗ[ℤ] zeroSumLattice n)
    (B : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ))
    (c w : Fin (n + 1) → ℤ) (a : Fin n → ℤ)
    (ha : pathLoad n a = w - c) (x : (Fin n → ℤ) × ℤ) :
    roundingLoad n c (blockTransport n (edgeBasisChange n treeBasis) B a x) =
      (treeBasis (B x.1) : Fin (n + 1) → ℤ) + x.2 • w := by
  simp only [roundingLoad, blockTransport, LinearMap.coe_mk, AddHom.coe_mk,
    pathLoad_add, pathLoad_smul, pathLoad_edgeBasisChange, ha, smul_sub]
  abel

/-- Equal total charge of the original and extension columns provides the
integral correction vector used by `tree_transport_identity`. -/
theorem exists_extension_correction (n : ℕ) (c w : Fin (n + 1) → ℤ)
    (h : totalCharge w = totalCharge c) : ∃! a, pathLoad n a = w - c := by
  apply (path_integral_basis n (w - c)).2
  simp [h]

end AFT

namespace AFT

/-- Matrix of the triangular coordinate construction, indexed by edges plus one
injection coordinate. -/
def transportBlockMatrix {R : Type*} [CommRing R] (n : ℕ)
    (U B : Matrix (Fin n) (Fin n) R) (a : Fin n → R) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) R :=
  Matrix.fromBlocks (U * B) (fun i _ => a i) 0 1

/-- The extension-column correction does not change the transport determinant. -/
theorem det_transportBlockMatrix {R : Type*} [CommRing R] (n : ℕ)
    (U B : Matrix (Fin n) (Fin n) R) (a : Fin n → R) :
    (transportBlockMatrix n U B a).det = U.det * B.det := by
  simp [transportBlockMatrix, Matrix.det_mul]

/-- The matrix of an integral change of tree coordinates. -/
noncomputable def edgeBasisChangeMatrix (n : ℕ)
    (treeBasis : (Fin n → ℤ) ≃ₗ[ℤ] zeroSumLattice n) :
    Matrix (Fin n) (Fin n) ℤ :=
  LinearMap.toMatrix (Pi.basisFun ℤ (Fin n)) (Pi.basisFun ℤ (Fin n))
    (edgeBasisChange n treeBasis).toLinearMap

theorem edgeBasisChangeMatrix_det_unit (n : ℕ)
    (treeBasis : (Fin n → ℤ) ≃ₗ[ℤ] zeroSumLattice n) :
    IsUnit (edgeBasisChangeMatrix n treeBasis).det :=
  (edgeBasisChange n treeBasis).isUnit_det _ _

/-- V7's `det M = ± det B` for the actual integral coordinate construction. -/
theorem tree_transport_determinant (n : ℕ)
    (treeBasis : (Fin n → ℤ) ≃ₗ[ℤ] zeroSumLattice n)
    (B : Matrix (Fin n) (Fin n) ℤ) (a : Fin n → ℤ) :
    (transportBlockMatrix n (edgeBasisChangeMatrix n treeBasis) B a).det = B.det ∨
    (transportBlockMatrix n (edgeBasisChangeMatrix n treeBasis) B a).det = -B.det := by
  have hu := edgeBasisChangeMatrix_det_unit n treeBasis
  rcases Int.isUnit_iff.mp hu with h | h
  · left; simp [det_transportBlockMatrix, h]
  · right; simp [det_transportBlockMatrix, h]

/-- Reduction modulo a prime is invertible whenever the edge-coordinate
matrix has nonzero determinant modulo that prime. -/
theorem tree_transport_modular_invertible (n q : ℕ) [Fact q.Prime]
    (treeBasis : (Fin n → ℤ) ≃ₗ[ℤ] zeroSumLattice n)
    (B : Matrix (Fin n) (Fin n) ℤ) (a : Fin n → ℤ)
    (hB : (B.det : ZMod q) ≠ 0) :
    IsUnit ((transportBlockMatrix n (edgeBasisChangeMatrix n treeBasis) B a).map
      (Int.castRingHom (ZMod q))) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  change IsUnit ((Int.castRingHom (ZMod q)).mapMatrix
    (transportBlockMatrix n (edgeBasisChangeMatrix n treeBasis) B a)).det
  rw [← (Int.castRingHom (ZMod q)).map_det, det_transportBlockMatrix, map_mul]
  exact ((edgeBasisChangeMatrix_det_unit n treeBasis).map (Int.castRingHom (ZMod q))).mul
    (isUnit_iff_ne_zero.mpr hB)

/-- Transport plus an initial lattice load has a unique integral preimage, for
all integer inputs. This is the affine integrality part of V7's corollary. -/
theorem affine_load_unique_integral_preimage (n : ℕ) (q : ℤ) (hq : q ≠ 0)
    (c : Fin (n + 1) → ℤ) (hc : totalCharge c = q)
    (treeBasis : (Fin n → ℤ) ≃ₗ[ℤ] zeroSumLattice n)
    (B : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ))
    (w z : Fin (n + 1) → ℤ) (hw : totalCharge w = q)
    (hz : q ∣ totalCharge z) (x : (Fin n → ℤ) × ℤ) :
    ∃! y, roundingLoad n c y =
      (treeBasis (B x.1) : Fin (n + 1) → ℤ) + x.2 • w + z := by
  apply unique_integral_preimage n q hq c hc
  have ht : totalCharge (treeBasis (B x.1) : Fin (n + 1) → ℤ) = 0 :=
    (treeBasis (B x.1)).property
  simp only [totalCharge_add, totalCharge_smul, ht, hw, zero_add]
  exact dvd_add (dvd_mul_left q x.2) hz

end AFT

namespace AFT

/-- Explicit columns of the recursively defined path map are exactly
`e_i - e_(i+1)`, matching the fixed matrix in V7. -/
theorem pathLoad_standardBasis (n : ℕ) (j : Fin n) :
    pathLoad n (fun k => if k = j then 1 else 0) =
      fun i => (if i = j.castSucc then 1 else 0) - (if i = j.succ then 1 else 0) := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
      refine Fin.cases ?_ (fun k => ?_) j
      · have ht : Fin.tail (fun k : Fin (n + 1) => if k = 0 then (1 : ℤ) else 0) = 0 := by
          funext k
          change (if k.succ = 0 then (1 : ℤ) else 0) = 0
          simp
        funext i
        refine Fin.cases ?_ (fun l => ?_) i
        · simp [pathLoad]
        · simp [pathLoad, ht]
          change (if l = 0 then (1 : ℤ) else 0) =
            (if l.succ = (0 : Fin (n + 1)).succ then 1 else 0)
          simp only [Fin.succ_inj]
      · have ht : Fin.tail (fun l : Fin (n + 1) => if l = k.succ then (1 : ℤ) else 0) =
            (fun l : Fin n => if l = k then 1 else 0) := by
          funext l
          change (if l.succ = k.succ then (1 : ℤ) else 0) =
            (if l = k then 1 else 0)
          simp
        funext i
        refine Fin.cases ?_ (fun l => ?_) i
        · simp [pathLoad, eq_comm]
        · simp [pathLoad, ht, ih]
          intro _
          exact (Fin.succ_ne_zero k).symm

end AFT
