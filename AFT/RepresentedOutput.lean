import AFT.RepresentedRing
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Generating polynomials of literal input seed tables

Every channel is an actual signed finite transition table.  Substitution
into the seed polynomial is an algebra homomorphism; its product is the
joint generating polynomial on disjoint output slots.  Equal output
images do not identify distinct input representations.
-/

namespace AFT.RepresentedPolynomial

open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {Color Output Seed : Type*} [Fintype Color] [Fintype Output]

def channelForm (channel : Color → Output → ℝ) (input : Color) : MvPolynomial Output ℝ :=
  ∑ output, MvPolynomial.C (channel input output) * MvPolynomial.X output

def seedChannel (primaryChannel bodyChannel : Color → Output → ℝ) (seed : InputSeed Color) :
    Fin (seed.primaryOrder + seed.bodyOrder) → Color → Output → ℝ :=
  Fin.addCases (fun _ => primaryChannel) (fun _ => bodyChannel)

def seedOutput (primary body : FiniteDist Color) (primaryChannel bodyChannel : Color → Output → ℝ)
    (seed : InputSeed Color) : MvPolynomial Output ℝ :=
  ∑ word : Fin (seed.primaryOrder + seed.bodyOrder) → Color,
    MvPolynomial.C (seed.kernel word * ∏ slot, (inputReference primary body seed slot).weight (word slot)) *
      ∏ slot, channelForm (seedChannel primaryChannel bodyChannel seed slot) (word slot)

/-- The represented input map uses all joint kernel entries, with their
actual product-reference weights. It does not factor a joint kernel. -/
def outputHom (primary body : FiniteDist Color) (primaryChannel bodyChannel : Color → Output → ℝ) :
    Table (InputSeed Color) →ₐ[ℝ] MvPolynomial Output ℝ :=
  MvPolynomial.aeval (seedOutput primary body primaryChannel bodyChannel)

@[simp] theorem outputHom_X (primary body : FiniteDist Color)
    (primaryChannel bodyChannel : Color → Output → ℝ) (seed : InputSeed Color) :
    outputHom primary body primaryChannel bodyChannel (MvPolynomial.X seed) =
      seedOutput primary body primaryChannel bodyChannel seed := MvPolynomial.aeval_X _ _

omit [Fintype Color] in
theorem channelForm_homogeneous (channel : Color → Output → ℝ) (input : Color) :
    (channelForm channel input).IsHomogeneous 1 :=
  MvPolynomial.IsHomogeneous.sum _ _ _ (fun _ _ => MvPolynomial.isHomogeneous_C_mul_X _ _)

theorem seedOutput_homogeneous (primary body : FiniteDist Color)
    (primaryChannel bodyChannel : Color → Output → ℝ) (seed : InputSeed Color) :
    (seedOutput primary body primaryChannel bodyChannel seed).IsHomogeneous
      (seed.primaryOrder + seed.bodyOrder) := by
  apply MvPolynomial.IsHomogeneous.sum
  intro word _
  apply MvPolynomial.IsHomogeneous.C_mul
  convert MvPolynomial.IsHomogeneous.prod Finset.univ
    (fun slot => channelForm (seedChannel primaryChannel bodyChannel seed slot) (word slot))
    (fun _ => 1) (fun slot _ => channelForm_homogeneous _ _) using 1
  simp

def seedOutputMass (primary body : FiniteDist Color)
    (primaryChannel bodyChannel : Color → Output → ℝ) (seed : InputSeed Color)
    (outputs : Fin (seed.primaryOrder + seed.bodyOrder) → Output) : ℝ :=
  ∑ word : Fin (seed.primaryOrder + seed.bodyOrder) → Color,
    (seed.kernel word * ∏ slot, (inputReference primary body seed slot).weight (word slot)) *
      ∏ slot, seedChannel primaryChannel bodyChannel seed slot (word slot) (outputs slot)

/-- Expanding the actual channel product gives exactly the joint pushed
signed mass, including all correlations in the input kernel. -/
theorem seedOutput_eq_mass (primary body : FiniteDist Color)
    (primaryChannel bodyChannel : Color → Output → ℝ) (seed : InputSeed Color) :
    seedOutput primary body primaryChannel bodyChannel seed =
      ∑ outputs : Fin (seed.primaryOrder + seed.bodyOrder) → Output,
        MvPolynomial.C (seedOutputMass primary body primaryChannel bodyChannel seed outputs) *
          ∏ slot, MvPolynomial.X (outputs slot) := by
  classical
  simp only [seedOutput, channelForm, Fintype.prod_sum,
    Finset.prod_mul_distrib, ← map_prod]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro outputs _
  simp only [seedOutputMass, map_sum, Finset.sum_mul, ← mul_assoc, ← map_mul]

theorem seedOutput_evaluate (primary body : FiniteDist Color)
    (primaryChannel bodyChannel : Color → Output → ℝ) (seed : InputSeed Color)
    (point : Output → ℝ) :
    MvPolynomial.eval point (seedOutput primary body primaryChannel bodyChannel seed) =
      ∑ outputs : Fin (seed.primaryOrder + seed.bodyOrder) → Output,
        seedOutputMass primary body primaryChannel bodyChannel seed outputs * ∏ slot, point (outputs slot) := by
  rw [seedOutput_eq_mass]
  simp

omit [Fintype Color] [Fintype Output] in
theorem homogeneous_hasOrder (degree : ℕ) (table : Table Output)
    (h : table.IsHomogeneous degree) : HasOrder (fun _ => 1) degree table := by
  intro powers hp
  apply h.coeff_eq_zero
  change powers.sum (fun _ power => power) ≠ degree
  simpa only [weightedOrder, mul_one] using ne_of_lt hp

omit [Fintype Color] [Fintype Output] in
theorem aeval_monomial_homogeneous (order : Seed → ℕ)
    (images : Seed → MvPolynomial Output ℝ)
    (himages : ∀ seed, (images seed).IsHomogeneous (order seed))
    (powers : Seed →₀ ℕ) (coefficient : ℝ) :
    (MvPolynomial.aeval images (MvPolynomial.monomial powers coefficient)).IsHomogeneous
      (weightedOrder order powers) := by
  rw [MvPolynomial.aeval_monomial]
  change (MvPolynomial.C coefficient * _).IsHomogeneous _
  apply MvPolynomial.IsHomogeneous.C_mul
  unfold Finsupp.prod weightedOrder Finsupp.sum
  apply MvPolynomial.IsHomogeneous.prod
  intro seed _
  simpa only [mul_comm] using (himages seed).pow (powers seed)

omit [Fintype Color] [Fintype Output] in
theorem aeval_hasOrder (order : Seed → ℕ) (images : Seed → MvPolynomial Output ℝ)
    (himages : ∀ seed, (images seed).IsHomogeneous (order seed))
    (minimum : ℕ) (table : Table Seed) (h : HasOrder order minimum table) :
    HasOrder (fun _ => 1) minimum (MvPolynomial.aeval images table) := by
  conv in MvPolynomial.aeval images table => rw [MvPolynomial.as_sum table]
  rw [map_sum]
  apply hasOrder_sum
  intro powers hp
  have hmin : minimum ≤ weightedOrder order powers := by
    by_contra hlt
    exact (MvPolynomial.mem_support_iff.mp hp) (h powers (by omega))
  exact hasOrder_mono _ _ _ _
    (homogeneous_hasOrder _ _ (aeval_monomial_homogeneous order images himages powers _)) hmin

theorem outputHom_hasOrder (primary body : FiniteDist Color)
    (primaryChannel bodyChannel : Color → Output → ℝ)
    (minimum : ℕ) (table : Table (InputSeed Color))
    (h : HasOrder (fun seed => seed.primaryOrder + seed.bodyOrder) minimum table) :
    HasOrder (fun _ => 1) minimum (outputHom primary body primaryChannel bodyChannel table) :=
  aeval_hasOrder _ _ (seedOutput_homogeneous primary body primaryChannel bodyChannel) _ _ h

/-- Degree preservation makes the same map well-defined on the two actual
cutoff rings, while retaining all distinctions in the input ring. -/
def outputQuotient (primary body : FiniteDist Color)
    (primaryChannel bodyChannel : Color → Output → ℝ) (cutoff : ℕ) :
    CutoffRing (fun seed : InputSeed Color => seed.primaryOrder + seed.bodyOrder) cutoff →+*
      CutoffRing (fun _ : Output => 1) cutoff :=
  Ideal.Quotient.lift _
    ((quotientMap (fun _ : Output => 1) cutoff).comp
      (outputHom primary body primaryChannel bodyChannel).toRingHom)
    (fun table h => Ideal.Quotient.eq_zero_iff_mem.mpr
      (outputHom_hasOrder primary body primaryChannel bodyChannel (cutoff + 1) table h))

@[simp] theorem outputQuotient_mk (primary body : FiniteDist Color)
    (primaryChannel bodyChannel : Color → Output → ℝ) (cutoff : ℕ)
    (table : Table (InputSeed Color)) :
    outputQuotient primary body primaryChannel bodyChannel cutoff
      (quotientMap (fun seed : InputSeed Color => seed.primaryOrder + seed.bodyOrder) cutoff table) =
      quotientMap (fun _ : Output => 1) cutoff
        (outputHom primary body primaryChannel bodyChannel table) := rfl

theorem outputHom_truncation_respects (primary body : FiniteDist Color)
    (primaryChannel bodyChannel : Color → Output → ℝ) (cutoff : ℕ)
    (first second : Table (InputSeed Color))
    (h : truncate (fun seed : InputSeed Color => seed.primaryOrder + seed.bodyOrder) cutoff first =
      truncate (fun seed : InputSeed Color => seed.primaryOrder + seed.bodyOrder) cutoff second) :
    truncate (fun _ : Output => 1) cutoff (outputHom primary body primaryChannel bodyChannel first) =
      truncate (fun _ : Output => 1) cutoff (outputHom primary body primaryChannel bodyChannel second) := by
  apply (quotient_eq_iff_truncate _ cutoff _ _).mp
  exact congrArg (outputQuotient primary body primaryChannel bodyChannel cutoff)
    ((quotient_eq_iff_truncate _ cutoff first second).mpr h)

end

end AFT.RepresentedPolynomial
