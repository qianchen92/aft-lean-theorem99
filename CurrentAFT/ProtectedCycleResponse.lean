import CurrentAFT.ProtectedCycle

/-!
# Exact protected-cycle response with centers and body relabeling

The body permutation is drawn independently of the latent edges. Its Fourier
response is an average of complete cyclic products, not a product of root
marginal responses. Centers are fixed in the conditional response formula.
These identities define the physical response needed by the calibration
analysis; no response-norm bound is assumed or claimed.
-/

namespace CurrentAFT.ProtectedCycle

open AFT
open scoped BigOperators Classical

noncomputable section

/-- Relabeling pulls a coordinate frequency back by the same permutation. -/
theorem cycle_character_relabel {body modulus : ℕ} [NeZero modulus]
    (permutation : Equiv.Perm (Fin body)) (frequency root : Fin body → ZMod modulus) :
    coordinateCharacter frequency (fun vertex => root (permutation.symm vertex)) =
      coordinateCharacter (fun vertex => frequency (permutation vertex)) root := by
  rw [coordinateCharacter_dot, coordinateCharacter_dot]
  congr 1
  have hreindex := Equiv.sum_comp permutation
    (fun vertex => frequency vertex * root (permutation.symm vertex))
  simpa only [Equiv.symm_apply_apply] using hreindex.symm

/-- One independently selected body permutation relabels the complete cycle. -/
def relabeledCycleLaw {Scalar : Type*} [Fintype Scalar]
    (body modulus : ℕ) [NeZero modulus] (edgeLaw : FiniteDist Scalar)
    (value : Scalar → ZMod modulus) (permutation : Equiv.Perm (Fin body)) :
    FiniteDist (Fin body → ZMod modulus) :=
  (cycleLaw body modulus edgeLaw value).map
    (fun root vertex => root (permutation.symm vertex))

/-- The fixed-permutation response keeps every cycle edge in the product. -/
theorem relabeledCycleLaw_fourier {Scalar : Type*} [Fintype Scalar]
    (body modulus : ℕ) [NeZero modulus] (edgeLaw : FiniteDist Scalar)
    (value : Scalar → ZMod modulus) (permutation : Equiv.Perm (Fin body))
    (frequency : Fin body → ZMod modulus) :
    signedFourier (relabeledCycleLaw body modulus edgeLaw value permutation).weight
      (coordinateCharacter frequency) =
      ∏ vertex, scalarFourier edgeLaw value
        (frequency (permutation vertex) - frequency (permutation (finRotate body vertex))) := by
  unfold signedFourier characterFourier relabeledCycleLaw
  rw [complex_expectation_map]
  simp_rw [cycle_character_relabel]
  exact cycleLaw_fourier body modulus edgeLaw value (fun vertex => frequency (permutation vertex))

/-- The exact Fourier effect of adding a fixed body-center vector. -/
theorem shifted_law_fourier {body modulus : ℕ} [NeZero modulus]
    (law : FiniteDist (Fin body → ZMod modulus))
    (centers frequency : Fin body → ZMod modulus) :
    signedFourier (law.map (fun root => centers + root)).weight (coordinateCharacter frequency) =
      coordinateCharacter frequency centers * signedFourier law.weight (coordinateCharacter frequency) := by
  unfold signedFourier characterFourier
  rw [complex_expectation_map]
  simp_rw [AddChar.map_add_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro root _
  ring

/-- Fixed centers and a fixed independently drawn body permutation. -/
def centeredRelabeledCycleLaw {Scalar : Type*} [Fintype Scalar]
    (body modulus : ℕ) [NeZero modulus] (edgeLaw : FiniteDist Scalar)
    (value : Scalar → ZMod modulus) (permutation : Equiv.Perm (Fin body))
    (centers : Fin body → ZMod modulus) : FiniteDist (Fin body → ZMod modulus) :=
  (relabeledCycleLaw body modulus edgeLaw value permutation).map (fun root => centers + root)

/-- Conditional physical body response, before averaging the body permutation. -/
theorem centeredRelabeledCycleLaw_fourier {Scalar : Type*} [Fintype Scalar]
    (body modulus : ℕ) [NeZero modulus] (edgeLaw : FiniteDist Scalar)
    (value : Scalar → ZMod modulus) (permutation : Equiv.Perm (Fin body))
    (centers frequency : Fin body → ZMod modulus) :
    signedFourier (centeredRelabeledCycleLaw body modulus edgeLaw value permutation centers).weight
      (coordinateCharacter frequency) =
      coordinateCharacter frequency centers *
        ∏ vertex, scalarFourier edgeLaw value
          (frequency (permutation vertex) - frequency (permutation (finRotate body vertex))) := by
  rw [centeredRelabeledCycleLaw, shifted_law_fourier, relabeledCycleLaw_fourier]

/-- Complex Fubini for a genuinely sampled public mixture. -/
theorem complex_expectation_mix {Choice Output : Type*} [Fintype Choice] [Fintype Output]
    (choiceLaw : FiniteDist Choice) (channel : Choice → FiniteDist Output) (test : Output → ℂ) :
    (∑ output, ((choiceLaw.mix channel).weight output : ℂ) * test output) =
      ∑ choice, (choiceLaw.weight choice : ℂ) *
        (∑ output, ((channel choice).weight output : ℂ) * test output) := by
  simp only [FiniteDist.mix_weight, Complex.ofReal_sum, Complex.ofReal_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro choice _
  apply Finset.sum_congr rfl
  intro output _
  ring

/-- A sampled body permutation is independent of the complete latent product.
Uniform body relabeling is the specialization to `FiniteDist.uniform`. -/
def publicBodyCycleLaw {Scalar : Type*} [Fintype Scalar]
    (body modulus : ℕ) [NeZero modulus] (edgeLaw : FiniteDist Scalar)
    (value : Scalar → ZMod modulus) (permutationLaw : FiniteDist (Equiv.Perm (Fin body)))
    (centers : Fin body → ZMod modulus) : FiniteDist (Fin body → ZMod modulus) :=
  permutationLaw.mix (fun permutation =>
    centeredRelabeledCycleLaw body modulus edgeLaw value permutation centers)

/-- Exact permutation-averaged physical response. The cyclic product is
formed before averaging the permutation; no root independence is used. -/
theorem publicBodyCycleLaw_fourier {Scalar : Type*} [Fintype Scalar]
    (body modulus : ℕ) [NeZero modulus] (edgeLaw : FiniteDist Scalar)
    (value : Scalar → ZMod modulus) (permutationLaw : FiniteDist (Equiv.Perm (Fin body)))
    (centers frequency : Fin body → ZMod modulus) :
    signedFourier (publicBodyCycleLaw body modulus edgeLaw value permutationLaw centers).weight
      (coordinateCharacter frequency) =
      coordinateCharacter frequency centers *
        ∑ permutation, (permutationLaw.weight permutation : ℂ) *
          ∏ vertex, scalarFourier edgeLaw value
            (frequency (permutation vertex) - frequency (permutation (finRotate body vertex))) := by
  unfold publicBodyCycleLaw signedFourier characterFourier
  rw [complex_expectation_mix]
  change (∑ permutation, (permutationLaw.weight permutation : ℂ) *
    signedFourier (centeredRelabeledCycleLaw body modulus edgeLaw value permutation centers).weight
      (coordinateCharacter frequency)) = _
  simp_rw [centeredRelabeledCycleLaw_fourier]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro permutation _
  ring

end

end CurrentAFT.ProtectedCycle
