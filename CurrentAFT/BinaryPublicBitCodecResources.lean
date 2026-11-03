import CurrentAFT.BinaryPublicBitCodec
import CurrentAFT.UniformPolynomialBound

/-! Compositional polynomial bounds for materialized bit-buffer codecs.
These lemmas follow the actual preparation and sequential-copy programs; no
runtime bound for a completed decoder is assumed. -/
namespace CurrentAFT.BinaryPublicBitCodec
open AFT BinaryArithmetic RationalRejectionProgram
noncomputable section
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] UniformPolynomialBound

structure UniformCodec {State : ℕ → Type*} (codec : ∀ security, Codec (State security)) : Prop where
  bits : UniformPolynomialBound (fun n => (codec n).encoding.bits)
  prepare : UniformPolynomialBound (fun n => (codec n).prepare.work)
  bound : ∀ total : ℕ → ℕ, UniformPolynomialBound total →
    UniformPolynomialBound (fun n => (codec n).bound (total n))

theorem bits_uniform (count : ℕ → ℕ) (hc : UniformPolynomialBound count) :
    UniformCodec (fun n => bits (count n)) := by
  refine ⟨hc,UniformPolynomialBound.constant 1,?_⟩
  intro total ht
  exact (hc.mul (((UniformPolynomialBound.constant 5).mul ht).add
    (UniformPolynomialBound.constant 8))).add (UniformPolynomialBound.constant 3)

theorem map_uniform {First Second : ℕ → Type*} (codec : ∀ n, Codec (First n))
    (equiv : ∀ n, First n ≃ Second n) (h : UniformCodec codec) :
    UniformCodec (fun n => map (codec n) (equiv n)) := by
  refine ⟨h.bits,h.prepare,?_⟩
  intro total ht
  exact (h.bound total ht).add (UniformPolynomialBound.constant 2)

theorem bitsCast_uniform (count other : ℕ → ℕ) (same : ∀ n, count n=other n)
    (hc : UniformPolynomialBound count) :
    UniformCodec (fun n => bitsCast (count n) (other n) (same n)) :=
  map_uniform _ _ (bits_uniform count hc)

theorem flag_uniform : UniformCodec (fun _ => flag) :=
  map_uniform _ _ (bits_uniform (fun _ => 1) (UniformPolynomialBound.constant 1))

theorem prod_uniform {First Second : ℕ → Type*} (first : ∀ n, Codec (First n))
    (second : ∀ n, Codec (Second n)) (hf : UniformCodec first) (hs : UniformCodec second) :
    UniformCodec (fun n => prod (first n) (second n)) := by
  refine ⟨hf.bits.add hs.bits,?_,?_⟩
  · have hp := ((hf.prepare.add hs.prepare).add
      (((UniformPolynomialBound.constant 2).mul hf.bits).add (UniformPolynomialBound.constant 1))).add
        (UniformPolynomialBound.constant 2)
    simpa only [prod,addCounter_work,Codec.prepare_value] using hp
  · intro total ht
    exact (((hf.bound total ht).add (hs.bound total ht)).add
      ((UniformPolynomialBound.constant 2).mul ht)).add (UniformPolynomialBound.constant 4)

theorem indexed_uniform {Index State : ℕ → Type*} (count : ℕ → ℕ)
    (ordering : ∀ n, Fin (count n) ≃ Index n) (codec : ∀ n, Codec (State n))
    (hc : UniformPolynomialBound count) (h : UniformCodec codec) :
    UniformCodec (fun n => indexed (ordering n) (codec n)) := by
  refine ⟨hc.mul h.bits,?_,?_⟩
  · have hp := (h.prepare.add ((hc.mul (((UniformPolynomialBound.constant 2).mul h.bits).add
      (UniformPolynomialBound.constant 3))).add (UniformPolynomialBound.constant 1))).add
        (UniformPolynomialBound.constant 2)
    simpa only [indexed,multiplyCounter_work,Codec.prepare_value] using hp
  · intro total ht
    exact (hc.mul (((((hc.mul (((UniformPolynomialBound.constant 2).mul h.bits).add
      (UniformPolynomialBound.constant 3))).add (UniformPolynomialBound.constant 1)).add
      (((UniformPolynomialBound.constant 2).mul ht).add (UniformPolynomialBound.constant 1))).add
      (h.bound total ht)).add (UniformPolynomialBound.constant 5))).add
        (UniformPolynomialBound.constant 3)

theorem decode_uniform {State : ℕ → Type*} (codec : ∀ n, Codec (State n)) (h : UniformCodec codec) :
    UniformPolynomialBound (fun n => decodeBound (codec n)) :=
  ((h.prepare.add ((UniformPolynomialBound.constant 3).mul h.bits)).add
    (h.bound _ h.bits)).add (UniformPolynomialBound.constant 4)

end
end CurrentAFT.BinaryPublicBitCodec
