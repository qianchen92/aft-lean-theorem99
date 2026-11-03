import AFT.Algebra

/-!
# Constructive tree incidence bases and the lobster architecture

A `GrowingTree n` is built from one vertex by `n` operations, each adjoining a
new leaf and connecting it to an explicitly chosen existing vertex. The new
vertex and edge receive index zero; all old indices shift by one. This is a
concrete combinatorial construction, not a structure assuming a basis theorem.
The integral basis is proved by leaf elimination. In particular the explicit
lobster builder below closes the tree-to-basis bridge for V7's architecture.
-/

namespace AFT

open scoped BigOperators

/-- A tree with `n` edges and `n+1` vertices, encoded by successive leaf additions. -/
inductive GrowingTree : ℕ → Type
  | root : GrowingTree 0
  | attach {n : ℕ} (previous : GrowingTree n) (parent : Fin (n + 1)) : GrowingTree (n + 1)

namespace GrowingTree

/-- Actual directed edge tails. A newly added edge points from its leaf to its parent. -/
def tail : {n : ℕ} → GrowingTree n → Fin n → Fin (n + 1)
  | 0, .root, i => Fin.elim0 i
  | _ + 1, .attach t _, i => Fin.cases 0 (fun j => (tail t j).succ) i

/-- Actual directed edge heads. -/
def head : {n : ℕ} → GrowingTree n → Fin n → Fin (n + 1)
  | 0, .root, i => Fin.elim0 i
  | _ + 1, .attach t parent, i => Fin.cases parent.succ (fun j => (head t j).succ) i

/-- The recursively built graph has no loops. -/
theorem tail_ne_head {n : ℕ} (t : GrowingTree n) (i : Fin n) : tail t i ≠ head t i := by
  induction t with
  | root => exact Fin.elim0 i
  | @attach n t parent ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · exact (Fin.succ_ne_zero parent).symm
      · exact fun h => ih j (Fin.succ_inj.mp h)

/-- Signed incidence applied to integer edge coefficients. -/
def load : {n : ℕ} → GrowingTree n → (Fin n → ℤ) → (Fin (n + 1) → ℤ)
  | 0, .root, _ => 0
  | _ + 1, .attach t parent, e => Fin.cons (e 0)
      (fun i => load t (Fin.tail e) i - if i = parent then e 0 else 0)

@[simp] theorem load_zero {n : ℕ} (t : GrowingTree n) : load t 0 = 0 := by
  induction t with
  | root => rfl
  | @attach n t parent ih =>
      have ht : Fin.tail (0 : Fin (n + 1) → ℤ) = 0 := rfl
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [load]
      · simp [load, ht, ih]

@[simp] theorem load_add {n : ℕ} (t : GrowingTree n) (e f : Fin n → ℤ) :
    load t (e + f) = load t e + load t f := by
  induction t with
  | root => rfl
  | @attach n t parent ih =>
      have ht : Fin.tail (e + f) = Fin.tail e + Fin.tail f := rfl
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [load]
      · simp only [load, Fin.cons_succ, ht, ih, Pi.add_apply]
        split_ifs <;> ring

@[simp] theorem load_smul {n : ℕ} (t : GrowingTree n) (a : ℤ) (e : Fin n → ℤ) :
    load t (a • e) = a • load t e := by
  induction t with
  | root => simp [load]
  | @attach n t parent ih =>
      have ht : Fin.tail (a • e) = a • Fin.tail e := rfl
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [load]
      · simp only [load, Fin.cons_succ, ht, ih, Pi.smul_apply, smul_eq_mul]
        split_ifs <;> ring

/-- Integral signed incidence as a linear map. -/
def incidence {n : ℕ} (t : GrowingTree n) : (Fin n → ℤ) →ₗ[ℤ] (Fin (n + 1) → ℤ) where
  toFun := load t
  map_add' := load_add t
  map_smul' := load_smul t

@[simp] theorem totalCharge_load {n : ℕ} (t : GrowingTree n) (e : Fin n → ℤ) :
    totalCharge (load t e) = 0 := by
  induction t with
  | root => simp [load, totalCharge]
  | @attach n t parent ih =>
      change (∑ i, Fin.cons (e 0)
        (fun j => load t (Fin.tail e) j - if j = parent then e 0 else 0) i) = 0
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [Finset.sum_sub_distrib]
      change e 0 + (totalCharge (load t (Fin.tail e)) - _) = 0
      simp [ih]

/-- Uniqueness of edge coefficients follows by eliminating the newest leaf. -/
theorem load_injective {n : ℕ} (t : GrowingTree n) : Function.Injective (load t) := by
  induction t with
  | root => intro e f h; exact Subsingleton.elim _ _
  | @attach n t parent ih =>
      intro e f h
      have h0 : e 0 = f 0 := congrFun h 0
      have ht : load t (Fin.tail e) = load t (Fin.tail f) := by
        funext i
        have hi := congrFun h i.succ
        simp only [load, Fin.cons_succ, h0] at hi
        exact sub_left_inj.mp hi
      have he := ih ht
      funext i
      exact Fin.cases h0 (fun j => congrFun he j) i

/-- Existence of integral edge coefficients follows by the same leaf elimination. -/
theorem exists_load {n : ℕ} (t : GrowingTree n) (v : Fin (n + 1) → ℤ)
    (hv : totalCharge v = 0) : ∃ e, load t e = v := by
  induction t with
  | root =>
      refine ⟨0, ?_⟩
      funext i
      have hi : i = 0 := Fin.ext (by omega)
      subst i
      simpa [load, totalCharge] using hv.symm
  | @attach n t parent ih =>
      let w : Fin (n + 1) → ℤ := fun i => v i.succ + if i = parent then v 0 else 0
      have hw : totalCharge w = 0 := by
        have hv' : v 0 + (∑ i : Fin (n + 1), v i.succ) = 0 := by
          simpa [totalCharge, Fin.sum_univ_succ] using hv
        simp only [w, totalCharge, Finset.sum_add_distrib]
        simpa [add_comm] using hv'
      obtain ⟨e, he⟩ := ih w hw
      refine ⟨Fin.cons (v 0) e, ?_⟩
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [load]
      · simp [load, he, w]

/-- Constructive form of V7's tree incidence basis theorem. -/
theorem integral_basis {n : ℕ} (t : GrowingTree n) (v : Fin (n + 1) → ℤ) :
    (∃! e, load t e = v) ↔ totalCharge v = 0 := by
  constructor
  · rintro ⟨e, rfl, _⟩
    exact totalCharge_load t e
  · intro h
    obtain ⟨e, he⟩ := exists_load t v h
    exact ⟨e, he, fun f hf => load_injective t (hf.trans he.symm)⟩

/-- The basis interface consumed by the transport construction, now proved
from explicit leaf attachments rather than supplied as a hypothesis. -/
noncomputable def basis {n : ℕ} (t : GrowingTree n) :
    (Fin n → ℤ) ≃ₗ[ℤ] zeroSumLattice n :=
  LinearEquiv.ofBijective
    ((incidence t).codRestrict (zeroSumLattice n) (totalCharge_load t)) (by
      constructor
      · intro e f h
        exact load_injective t (congrArg Subtype.val h)
      · rintro ⟨v, hv⟩
        obtain ⟨e, he⟩ := exists_load t v hv
        exact ⟨e, Subtype.ext he⟩)

@[simp] theorem basis_apply {n : ℕ} (t : GrowingTree n) (e : Fin n → ℤ) :
    (basis t e : Fin (n + 1) → ℤ) = load t e := rfl

/-- A body path with `n+1` vertices, built by attaching at its current first vertex. -/
def path : (n : ℕ) → GrowingTree n
  | 0 => root
  | n + 1 => attach (path n) 0

/-- The body construction is exactly the path incidence used by the fixed rounding map. -/
@[simp] theorem load_path (n : ℕ) (e : Fin n → ℤ) : load (path n) e = pathLoad n e := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · simp [load, path, pathLoad, ih]

/-- Index of an original body vertex after `legs` two-edge leg attachments. -/
def bodyVertex (bodyEdges legs : ℕ) (i : Fin (bodyEdges + 1)) :
    Fin (bodyEdges + 2 * legs + 1) := ⟨i.val + 2 * legs, by omega⟩

/-- Explicit lobster: a nonempty path body and arbitrarily many disjoint
length-two legs attached to the supplied body vertices. Repeated body labels
allow any number of legs at a single body vertex. -/
def lobster (bodyEdges : ℕ) : (legs : ℕ) →
    (Fin legs → Fin (bodyEdges + 1)) → GrowingTree (bodyEdges + 2 * legs)
  | 0, _ => by simpa using path bodyEdges
  | legs + 1, attachments => by
      let previous := lobster bodyEdges legs (fun i => attachments i.castSucc)
      let middle := attach previous (bodyVertex bodyEdges legs (attachments (Fin.last legs)))
      let tip := attach middle 0
      simpa only [Nat.mul_succ, Nat.add_assoc] using tip

/-- Interface using the literal number of body vertices, with its positivity
condition explicit. The number of vertices is `bodyVertices + 2*legs`. -/
def lobsterOfVertices (bodyVertices legs : ℕ) (hbody : 1 ≤ bodyVertices)
    (attachments : Fin legs → Fin bodyVertices) :
    GrowingTree (bodyVertices - 1 + 2 * legs) :=
  lobster (bodyVertices - 1) legs (fun i => ⟨(attachments i).val, by omega⟩)

theorem lobster_vertex_count (bodyVertices legs : ℕ) (hbody : 1 ≤ bodyVertices) :
    bodyVertices - 1 + 2 * legs + 1 = bodyVertices + 2 * legs := by omega

/-- Integral incidence basis for every concrete lobster built above. -/
noncomputable def lobsterBasis (bodyEdges legs : ℕ)
    (attachments : Fin legs → Fin (bodyEdges + 1)) :
    (Fin (bodyEdges + 2 * legs) → ℤ) ≃ₗ[ℤ] zeroSumLattice (bodyEdges + 2 * legs) :=
  basis (lobster bodyEdges legs attachments)

/-- The modular invertibility conclusion now applies to the explicit lobster
without any assumed tree-basis equivalence. -/
theorem lobster_transport_modular_invertible (bodyEdges legs q : ℕ) [Fact q.Prime]
    (attachments : Fin legs → Fin (bodyEdges + 1))
    (B : Matrix (Fin (bodyEdges + 2 * legs)) (Fin (bodyEdges + 2 * legs)) ℤ)
    (a : Fin (bodyEdges + 2 * legs) → ℤ) (hB : (B.det : ZMod q) ≠ 0) :
    IsUnit ((transportBlockMatrix (bodyEdges + 2 * legs)
      (edgeBasisChangeMatrix _ (lobsterBasis bodyEdges legs attachments)) B a).map
        (Int.castRingHom (ZMod q))) :=
  tree_transport_modular_invertible _ q (lobsterBasis bodyEdges legs attachments) B a hB

end GrowingTree
end AFT

namespace AFT.GrowingTree

/-- Every load-map column is the actual signed incidence column of its
explicitly defined tail and head. -/
theorem load_standardBasis {n : ℕ} (t : GrowingTree n) (j : Fin n) :
    load t (fun k => if k = j then 1 else 0) =
      fun i => (if i = tail t j then 1 else 0) - (if i = head t j then 1 else 0) := by
  induction t with
  | root => exact Fin.elim0 j
  | @attach n t parent ih =>
      refine Fin.cases ?_ (fun k => ?_) j
      · have ht : Fin.tail (fun k : Fin (n + 1) => if k = 0 then (1 : ℤ) else 0) = 0 := by
          funext k
          change (if k.succ = 0 then (1 : ℤ) else 0) = 0
          simp
        funext i
        refine Fin.cases ?_ (fun l => ?_) i
        · simp [load, tail, head, eq_comm]
        · simp [load, tail, head, ht]
      · have ht : Fin.tail (fun l : Fin (n + 1) => if l = k.succ then (1 : ℤ) else 0) =
            (fun l : Fin n => if l = k then 1 else 0) := by
          funext l
          change (if l.succ = k.succ then (1 : ℤ) else 0) = (if l = k then 1 else 0)
          simp
        have h0 : (0 : Fin (n + 1)) ≠ k.succ := (Fin.succ_ne_zero k).symm
        funext i
        refine Fin.cases ?_ (fun l => ?_) i
        · simp [load, tail, head, h0, (Fin.succ_ne_zero (tail t k)).symm,
            (Fin.succ_ne_zero (head t k)).symm]
        · simp [load, tail, head, ht, ih, h0]

/-- The usual signed incidence matrix, defined directly from edge endpoints. -/
def signedIncidence {n : ℕ} (t : GrowingTree n) : Matrix (Fin (n + 1)) (Fin n) ℤ :=
  fun i j => (if i = tail t j then 1 else 0) - (if i = head t j then 1 else 0)

/-- The recursive linear map represents that concrete signed incidence matrix. -/
theorem toMatrix_incidence {n : ℕ} (t : GrowingTree n) :
    LinearMap.toMatrix' (incidence t) = signedIncidence t := by
  ext i j
  rw [LinearMap.toMatrix'_apply]
  change load t (Pi.single j 1) i = signedIncidence t i j
  have hs : (Pi.single j (1 : ℤ) : Fin n → ℤ) =
      (fun k : Fin n => if k = j then (1 : ℤ) else 0) := by
    funext k
    simp [Pi.single_apply, eq_comm]
  rw [hs, load_standardBasis]
  rfl

/-- The basis theorem applies to multiplication by the actual incidence matrix. -/
theorem signedIncidence_mulVec {n : ℕ} (t : GrowingTree n) (e : Fin n → ℤ) :
    (signedIncidence t).mulVec e = load t e := by
  rw [← toMatrix_incidence]
  exact LinearMap.toMatrix'_mulVec (incidence t) e

theorem signedIncidence_integral_basis {n : ℕ} (t : GrowingTree n)
    (v : Fin (n + 1) → ℤ) :
    (∃! e, (signedIncidence t).mulVec e = v) ↔ totalCharge v = 0 := by
  simpa only [signedIncidence_mulVec] using integral_basis t v

end AFT.GrowingTree
