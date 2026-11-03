import AFT.Affine

/-!
# Exact public-matrix preservation for the current AFT interface

These theorems instantiate the generic finite affine algebra in `AFT.Affine`
at modular vector spaces. They formalize `lem:t-aft-properties` in the current
manuscript and do not depend on V7 parameters or its Gaussian construction.

Each supplied affine pair has an actual linear equivalence as its linear
part. This represents modular invertibility, not an assumed proposition
named legality. The law of the affine pair and an arbitrary error law are
sampled by a product distribution. A fresh uniform public matrix is then
drawn independently. The transformed matrix is exactly uniform and remains
independent of the transformed error, including correlated matrix/offset
choices. No uniformity hypothesis is imposed on the source error.

The manuscript permits returning affine data modulo the modulus. This file
uses that convention and proves no integer-lift assembly, construction of
the actual current sampler, or running-time bound.
-/

namespace CurrentAFT

open AFT
open scoped Classical

noncomputable section

set_option maxHeartbeats 600000

local instance columnClassicalDecidableEq (columns : ℕ) : DecidableEq (Fin columns) :=
  Classical.decEq _

/-- Modular coordinates of the error and every column of the public matrix. -/
abbrev ModularCoordinates (dimension modulus : ℕ) := Fin dimension → ZMod modulus

/-- A legal reduced affine pair has a genuinely invertible modular linear part. -/
abbrev ModularAffinePair (dimension modulus : ℕ) :=
  AffinePair (ZMod modulus) (ModularCoordinates dimension modulus)

/-- Exact joint law, for arbitrary errors and a source-independent affine
pair. The right-hand product proves both exact uniformity of the transformed
public matrix and its independence from the transformed error. -/
theorem modular_public_matrix_error_independent
    (dimension columns modulus : ℕ) [NeZero modulus]
    {RandomTape : Type*} [Fintype RandomTape]
    (sampler : FiniteDist RandomTape) (pair : RandomTape → ModularAffinePair dimension modulus)
    (source : FiniteDist (ModularCoordinates dimension modulus)) :
    (sampler.prod source).mix (fun draw =>
      (FiniteDist.uniform (Fin columns → ModularCoordinates dimension modulus)).map
        (fun matrix => ((pair draw.1).columnsEquiv (Fin columns) matrix,
          (pair draw.1).eval draw.2))) =
      (FiniteDist.uniform (Fin columns → ModularCoordinates dimension modulus)).prod
        (transportedLaw sampler pair source) :=
  AFT.public_matrix_error_independent (R := ZMod modulus)
    (V := ModularCoordinates dimension modulus) (Column := Fin columns) sampler pair source

/-- On an independent uniform response, the same public affine pair preserves
the exact product uniform law of public matrix and response. Matrix and offset
inside the sampled pair are allowed to be correlated. -/
theorem modular_ideal_response_preserved
    (dimension columns modulus : ℕ) [NeZero modulus]
    {RandomTape : Type*} [Fintype RandomTape]
    (sampler : FiniteDist RandomTape) (pair : RandomTape → ModularAffinePair dimension modulus) :
    sampler.mix (fun draw =>
      ((FiniteDist.uniform (Fin columns → ModularCoordinates dimension modulus)).prod
        (FiniteDist.uniform (ModularCoordinates dimension modulus))).map
          (((pair draw).columnsEquiv (Fin columns)).prodCongr (pair draw).equiv)) =
      (FiniteDist.uniform (Fin columns → ModularCoordinates dimension modulus)).prod
        (FiniteDist.uniform (ModularCoordinates dimension modulus)) :=
  AFT.ideal_response_preserved (R := ZMod modulus)
    (V := ModularCoordinates dimension modulus) (Column := Fin columns) sampler pair

end

end CurrentAFT
