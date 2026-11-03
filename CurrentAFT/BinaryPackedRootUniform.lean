import CurrentAFT.BinaryPackedRootResources
import CurrentAFT.BinaryFixedPointPrograms

/-! One actual packed entry program and one resource polynomial for the fixed
order. Source arities are dispatched from stored point programs; all bounded
kept/tag counts share a finite polynomial envelope. -/
namespace CurrentAFT.BinaryPackedRootUniform
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
open GradedControlAlgebra BinaryFamilyProduct BinaryPackedRootMetadata
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryReferenceTables.current


def current {kept tags : ℕ} (security bits order : ℕ) (programs : BinaryRootGroupProgram.Data order)
    (points : List (BinaryFixedPointPrograms.Entry order)) (queue : IntegerBits) (source : TruncatedArity order)
    (metadata : Data source.val.1.val source.val.2.val kept tags)
    (sourcePrimary : Vector (Color security) source.val.1.val) (sourceBody : Vector (Color security) source.val.2.val) :
    CoefficientProgram order := fun arity colors centers =>
  let selected := BinaryFixedPointPrograms.lookup order source points
  let result := BinaryPackedRootCurrent.current security bits order programs selected.value queue metadata sourcePrimary sourceBody arity colors centers
  ⟨result.value,selected.work+result.work+1⟩

 theorem current_value {kept tags : ℕ} (security bits order : ℕ) (programs : BinaryRootGroupProgram.Data order)
    (hprograms : BinaryRootGroupProgram.Correct programs) (points : List (BinaryFixedPointPrograms.Entry order))
    (hpoints : BinaryFixedPointPrograms.Correct order points) (hcomplete : BinaryFixedPointPrograms.Complete order points)
    (queue : IntegerBits) (source : TruncatedArity order) (metadata : Data source.val.1.val source.val.2.val kept tags)
    (sourcePrimary : Vector (Color security) source.val.1.val) (sourceBody : Vector (Color security) source.val.2.val)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i < (PublicParameterProgram.modulus security).count)
    (hb : ∀ i, centers.get i < (PublicParameterProgram.modulus security).count) :
    (current security bits order programs points queue source metadata sourcePrimary sourceBody arity colors centers).value.decode =
      RationalPackedRootProgram.current security bits order queue.decode metadata.metadata (fun index => (sourcePrimary.get index).val)
        (fun index => (sourceBody.get index).val) arity colors.get centers.get := by
  exact BinaryPackedRootCurrent.current_value security bits order programs hprograms (BinaryFixedPointPrograms.lookup order source points).value
    (BinaryFixedPointPrograms.lookup_meaning order source points hpoints (hcomplete source)) queue metadata sourcePrimary sourceBody arity colors centers hc hb

noncomputable section
open scoped Classical


def envelope (order limit : ℕ) (value : TruncatedArity order → ℕ → ℕ → Polynomial ℕ) : Polynomial ℕ :=
  ∑ source : TruncatedArity order, ∑ kept ∈ Finset.range (limit+1), ∑ tags ∈ Finset.range (limit+1), value source kept tags

 theorem component_le_envelope (security order limit : ℕ) (value : TruncatedArity order → ℕ → ℕ → Polynomial ℕ)
    (source : TruncatedArity order) (kept tags : ℕ) (hk : kept ≤ limit) (ht : tags ≤ limit) :
    (value source kept tags).eval security ≤ (envelope order limit value).eval security := by
  simp only [envelope,Polynomial.eval_finset_sum]
  have htags : (value source kept tags).eval security ≤
      ∑ tag ∈ Finset.range (limit+1), (value source kept tag).eval security :=
    Finset.single_le_sum (a := tags) (s := Finset.range (limit+1)) (f := fun tag => (value source kept tag).eval security)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
  have hkept : (∑ tag ∈ Finset.range (limit+1), (value source kept tag).eval security) ≤
      ∑ size ∈ Finset.range (limit+1), ∑ tag ∈ Finset.range (limit+1), (value source size tag).eval security :=
    Finset.single_le_sum (a := kept) (s := Finset.range (limit+1))
      (f := fun size => ∑ tag ∈ Finset.range (limit+1), (value source size tag).eval security)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
  exact (htags.trans hkept).trans (Finset.single_le_sum (a := source) (s := Finset.univ)
    (f := fun input => ∑ size ∈ Finset.range (limit+1), ∑ tag ∈ Finset.range (limit+1), (value input size tag).eval security)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ source))


def heightPolynomial (order limit : ℕ) (programs : BinaryRootGroupProgram.Data order)
    (points : List (BinaryFixedPointPrograms.Entry order)) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  envelope order limit (fun source kept tags => BinaryPackedRootResources.heightPolynomial order kept tags programs
    (BinaryFixedPointPrograms.lookup order source points).value precision queueBits)


def workPolynomial (order limit : ℕ) (programs : BinaryRootGroupProgram.Data order)
    (points : List (BinaryFixedPointPrograms.Entry order)) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (points.length*(12*order+7)+2)+
    envelope order limit (fun source kept tags => BinaryPackedRootResources.workPolynomial order kept tags programs
      (BinaryFixedPointPrograms.lookup order source points).value precision queueBits)

 theorem current_bounds {kept tags : ℕ} (security order limit : ℕ) (programs : BinaryRootGroupProgram.Data order)
    (points : List (BinaryFixedPointPrograms.Entry order)) (precision queueBits : Polynomial ℕ)
    (queue : IntegerBits) (hq : queue.digits.length ≤ queueBits.eval security) (source : TruncatedArity order)
    (metadata : Data source.val.1.val source.val.2.val kept tags) (hk : kept ≤ limit) (ht : tags ≤ limit)
    (sourcePrimary : Vector (Color security) source.val.1.val) (sourceBody : Vector (Color security) source.val.2.val)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i < (PublicParameterProgram.modulus security).count)
    (hb : ∀ i, centers.get i < (PublicParameterProgram.modulus security).count) :
    HeightBound (current security (precision.eval security) order programs points queue source metadata sourcePrimary sourceBody arity colors centers).value.decode
      ((heightPolynomial order limit programs points precision queueBits).eval security) ∧
    (current security (precision.eval security) order programs points queue source metadata sourcePrimary sourceBody arity colors centers).work ≤
      (workPolynomial order limit programs points precision queueBits).eval security := by
  have hp := BinaryPackedRootResources.current_bounds security order programs (BinaryFixedPointPrograms.lookup order source points).value
    precision queueBits queue hq metadata sourcePrimary sourceBody arity colors centers hc hb
  have wh := BinaryFixedPointPrograms.lookup_work order source points
  constructor
  · exact hp.1.mono (component_le_envelope security order limit
      (fun input kept tags => BinaryPackedRootResources.heightPolynomial order kept tags programs
        (BinaryFixedPointPrograms.lookup order input points).value precision queueBits) source kept tags hk ht)
  · have hw := hp.2.trans (component_le_envelope security order limit
      (fun input kept tags => BinaryPackedRootResources.workPolynomial order kept tags programs
        (BinaryFixedPointPrograms.lookup order input points).value precision queueBits) source kept tags hk ht)
    change (BinaryFixedPointPrograms.lookup order source points).work+
      (BinaryPackedRootCurrent.current _ _ _ _ _ _ _ _ _ _ _ _).work+1 ≤ _
    simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_C]
    omega

end
end CurrentAFT.BinaryPackedRootUniform
