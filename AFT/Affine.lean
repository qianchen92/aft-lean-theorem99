import AFT.FiniteProbability

/-!
# Affine evaluation and the exact AFT preservation interface

The linear part is an actual linear equivalence, so legality is represented
by invertibility, not by an arbitrary proposition named `legal`.
For the paper take `R = ZMod q` and `V = Fin d → ZMod q`.
This file does not construct the calibrated Gaussian sampler of Section 9.
-/

namespace AFT

open scoped Classical

variable (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V]

/-- The reduced affine data returned by a legal AFT sampler. The paper permits
returning residues rather than integer lifts (immediately after Definition 5.1). -/
structure AffinePair where
  linear : V ≃ₗ[R] V
  offset : V

namespace AffinePair

variable {R V}

/-- The deterministic evaluator, exactly `Q x + b`. -/
def eval (pair : AffinePair R V) (input : V) : V :=
  pair.linear input + pair.offset

/-- Every legal affine evaluator is a bijection. -/
def equiv (pair : AffinePair R V) : V ≃ V where
  toFun := pair.eval
  invFun output := pair.linear.symm (output - pair.offset)
  left_inv input := by simp [eval]
  right_inv output := by simp [eval]

@[simp] theorem equiv_apply (pair : AffinePair R V) (input : V) :
    pair.equiv input = pair.eval input := rfl

theorem eval_bijective (pair : AffinePair R V) : Function.Bijective pair.eval :=
  pair.equiv.bijective

/-- The always-legal fallback in Appendix A. -/
def fallback : AffinePair R V := ⟨LinearEquiv.refl R V, 0⟩

@[simp] theorem fallback_eval (input : V) :
    (fallback : AffinePair R V).eval input = input := by simp [eval, fallback]

/-- Left multiplication acts on each column of a public matrix. -/
def columnsEquiv (pair : AffinePair R V) (Column : Type*) :
    (Column → V) ≃ (Column → V) :=
  Equiv.piCongrRight (fun _ => pair.linear.toEquiv)

@[simp] theorem columnsEquiv_apply (pair : AffinePair R V) (Column : Type*)
    (matrix : Column → V) (column : Column) :
    pair.columnsEquiv Column matrix column = pair.linear (matrix column) := rfl

/-- Transforming a response preserves its secret and changes precisely its
public columns and error, the algebraic step in the LWE reduction. -/
theorem eval_response {Column : Type*} [Fintype Column]
    (pair : AffinePair R V) (matrix : Column → V) (secret : Column → R) (error : V) :
    pair.eval ((∑ column, secret column • matrix column) + error) =
      (∑ column, secret column • pair.columnsEquiv Column matrix column) +
        pair.eval error := by
  simp [eval, map_sum, add_assoc]

end AffinePair

section Probability

variable {R V} [Fintype V]
variable {Sample Column : Type*} [Fintype Sample] [Fintype Column]

/-- Sampling the affine data independently of the source is encoded by a
product distribution, rather than asserted in a comment. -/
noncomputable def transportedLaw (sampler : FiniteDist Sample)
    (pair : Sample → AffinePair R V) (source : FiniteDist V) : FiniteDist V :=
  (sampler.prod source).map (fun sample => (pair sample.1).eval sample.2)

/-- V7 Lemma 5.2: exact public-matrix preservation and independence of the
transformed error, for arbitrary source and arbitrarily correlated affine data. -/
theorem public_matrix_error_independent (sampler : FiniteDist Sample)
    (pair : Sample → AffinePair R V) (source : FiniteDist V) :
    (sampler.prod source).mix (fun sample =>
      (FiniteDist.uniform (Column → V)).map (fun matrix =>
        ((pair sample.1).columnsEquiv Column matrix, (pair sample.1).eval sample.2))) =
      (FiniteDist.uniform (Column → V)).prod (transportedLaw sampler pair source) :=
  FiniteDist.random_equiv_independent (sampler.prod source)
    (fun sample => (pair sample.1).columnsEquiv Column)
    (fun sample => (pair sample.1).eval sample.2)

/-- V7's ideal-response preservation, with the same sampled linear part on
the public matrix and the response. -/
theorem ideal_response_preserved (sampler : FiniteDist Sample)
    (pair : Sample → AffinePair R V) :
    sampler.mix (fun sample =>
      ((FiniteDist.uniform (Column → V)).prod (FiniteDist.uniform V)).map
        (((pair sample).columnsEquiv Column).prodCongr (pair sample).equiv)) =
      (FiniteDist.uniform (Column → V)).prod (FiniteDist.uniform V) :=
  FiniteDist.random_equiv_product_uniform sampler
    (fun sample => (pair sample).columnsEquiv Column) (fun sample => (pair sample).equiv)

end Probability
end AFT
