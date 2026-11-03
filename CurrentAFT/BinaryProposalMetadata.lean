import CurrentAFT.BinaryDiffuseCurrent

/-! # Executed sizes used by the current proposal formula

The prime search and the two fixed powers are executed before their binary
encodings are produced.  None of these rational inputs is stored advice.
-/
namespace CurrentAFT.BinaryProposalMetadata
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] addCounter multiplyCounter powerCounter ofCounter PublicParameterProgram.modulus

private opaque checkedPower (base exponent : ℕ) :
    {result : UnaryCounterResult // result.count = base^exponent ∧ result.work ≤ powerCounterWork base exponent} :=
  ⟨powerCounter base exponent, powerCounter_value base exponent, powerCounter_work base exponent⟩

private opaque checkedProduct (first second : ℕ) :
    {result : UnaryCounterResult // result.count = first*second ∧ result.work = first*(2*second+3)+1} :=
  ⟨multiplyCounter first second, multiplyCounter_value first second, multiplyCounter_work first second⟩

structure Counts where
  colors : ℕ
  legs : ℕ
  population : ℕ
  work : ℕ

def counts (security : ℕ) : Counts :=
  let colors := PublicParameterProgram.modulus security
  let base := addCounter security 2
  let legs := (checkedPower base.count 128).val
  let factor := (checkedPower base.count 96).val
  let population := (checkedProduct colors.count factor.count).val
  ⟨colors.count, legs.count, population.count,
    colors.work + base.work + legs.work + factor.work + population.work + 5⟩

theorem counts_value (security : ℕ) :
    (counts security).colors = Parameters.modulus security ∧
    (counts security).legs = (security+2)^128 ∧
    (counts security).population = Parameters.modulus security*(security+2)^96 := by
  let colors := PublicParameterProgram.modulus security
  let base := addCounter security 2
  let factor := (checkedPower base.count 96).val
  have hq : colors.count = Parameters.modulus security := PublicParameterProgram.modulus_value security
  have hb : base.count = security+2 := addCounter_value security 2
  have hf : factor.count = (security+2)^96 :=
    (checkedPower base.count 96).property.1.trans (congrArg (·^96) hb)
  exact ⟨hq, (checkedPower base.count 128).property.1.trans (congrArg (·^128) hb),
    (checkedProduct colors.count factor.count).property.1.trans (by rw [hq, hf])⟩

def sizeBound (security : ℕ) : ℕ := 131072*(security+2)^160

theorem counts_bounds (security : ℕ) :
    (counts security).colors ≤ sizeBound security ∧
    (counts security).legs ≤ sizeBound security ∧
    (counts security).population ≤ sizeBound security := by
  rcases counts_value security with ⟨hq, hl, hp⟩
  have hb : 1 ≤ security+2 := by omega
  have hq' : Parameters.modulus security ≤ 131072*(security+2)^64 := by
    simpa only [Parameters.base] using (Parameters.modulus_bounds security).2
  have hc : Parameters.modulus security ≤ sizeBound security := hq'.trans
    (Nat.mul_le_mul_left 131072 (Nat.pow_le_pow_right hb (by decide : 64 ≤ 160)))
  have hlegs : (security+2)^128 ≤ sizeBound security :=
    (Nat.pow_le_pow_right hb (by decide : 128 ≤ 160)).trans (Nat.le_mul_of_pos_left _ (by decide))
  have hpop : Parameters.modulus security*(security+2)^96 ≤ sizeBound security := by
    apply (Nat.mul_le_mul_right ((security+2)^96) hq').trans_eq
    simp only [sizeBound, mul_assoc, ← pow_add]
  exact ⟨hq ▸ hc, hl ▸ hlegs, hp ▸ hpop⟩

def countsWork (security : ℕ) : ℕ := PublicParameterProgram.workBound security + 2*security+1 +
  powerCounterWork (security+2) 128 + powerCounterWork (security+2) 96 +
  (131072*(security+2)^64)*(2*(security+2)^96+3)+1 + 5

theorem counts_work (security : ℕ) : (counts security).work ≤ countsWork security := by
  let colors := PublicParameterProgram.modulus security
  let base := addCounter security 2
  let legs := (checkedPower base.count 128).val
  let factor := (checkedPower base.count 96).val
  let population := (checkedProduct colors.count factor.count).val
  have hb : base.count = security+2 := addCounter_value security 2
  have hf : factor.count = (security+2)^96 :=
    (checkedPower base.count 96).property.1.trans (congrArg (·^96) hb)
  have hq : colors.count ≤ 131072*(security+2)^64 := by
    rw [PublicParameterProgram.modulus_value]
    simpa only [Parameters.base] using (Parameters.modulus_bounds security).2
  have wc : colors.work ≤ PublicParameterProgram.workBound security := PublicParameterProgram.modulus_work security
  have wb : base.work = 2*security+1 := addCounter_work security 2
  have wl : legs.work ≤ powerCounterWork (security+2) 128 :=
    (checkedPower base.count 128).property.2.trans_eq (congrArg (fun b => powerCounterWork b 128) hb)
  have wf : factor.work ≤ powerCounterWork (security+2) 96 :=
    (checkedPower base.count 96).property.2.trans_eq (congrArg (fun b => powerCounterWork b 96) hb)
  have wp : population.work ≤ (131072*(security+2)^64)*(2*(security+2)^96+3)+1 := by
    rw [(checkedProduct colors.count factor.count).property.2, hf]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hq) 1
  change colors.work+base.work+legs.work+factor.work+population.work+5 ≤ _
  unfold countsWork
  omega

structure Encoded where
  colors : RationalBits
  legs : RationalBits
  population : RationalBits
  work : ℕ

def current (security : ℕ) : Encoded :=
  let sizes := counts security
  let colors := ofCounter sizes.colors
  let legs := ofCounter sizes.legs
  let population := ofCounter sizes.population
  ⟨colors.data, legs.data, population.data, sizes.work+colors.work+legs.work+population.work+4⟩

theorem current_value (security : ℕ) :
    (current security).colors.decode = (Parameters.modulus security:ℚ) ∧
    (current security).legs.decode = ((security+2:ℕ)^128:ℚ) ∧
    (current security).population.decode = (Parameters.modulus security*(security+2)^96:ℕ) := by
  rcases counts_value security with ⟨hq, hl, hp⟩
  simp only [current, ofCounter_value, hq, hl, hp, Nat.cast_pow, and_self]

theorem current_height (security : ℕ) :
    HeightBound (current security).colors.decode (sizeBound security) ∧
    HeightBound (current security).legs.decode (sizeBound security) ∧
    HeightBound (current security).population.decode (sizeBound security) := by
  rcases counts_bounds security with ⟨hq, hl, hp⟩
  exact ⟨by simpa only [current, ofCounter_value] using (HeightBound.nat_coarse (counts security).colors).mono hq,
    by simpa only [current, ofCounter_value] using (HeightBound.nat_coarse (counts security).legs).mono hl,
    by simpa only [current, ofCounter_value] using (HeightBound.nat_coarse (counts security).population).mono hp⟩

def currentWork (security : ℕ) : ℕ := countsWork security + 3*(60*(sizeBound security+1)^2)+4

theorem current_work (security : ℕ) : (current security).work ≤ currentWork security := by
  rcases counts_bounds security with ⟨hq, hl, hp⟩
  have wq := (ofCounter_work (counts security).colors).trans
    (Nat.mul_le_mul_left 60 (Nat.pow_le_pow_left (Nat.add_le_add_right hq 1) 2))
  have wl := (ofCounter_work (counts security).legs).trans
    (Nat.mul_le_mul_left 60 (Nat.pow_le_pow_left (Nat.add_le_add_right hl 1) 2))
  have wp := (ofCounter_work (counts security).population).trans
    (Nat.mul_le_mul_left 60 (Nat.pow_le_pow_left (Nat.add_le_add_right hp 1) 2))
  have wc := counts_work security
  change (counts security).work+(ofCounter (counts security).colors).work+
    (ofCounter (counts security).legs).work+(ofCounter (counts security).population).work+4 ≤ _
  unfold currentWork
  omega

noncomputable def sizePolynomial : Polynomial ℕ := 131072*(Polynomial.X+2)^160
noncomputable def countsWorkPolynomial : Polynomial ℕ := PublicParameterProgram.workPolynomial+2*Polynomial.X+1+
  129*(6*(Polynomial.X+3)^130+4)+97*(6*(Polynomial.X+3)^98+4)+
  (131072*(Polynomial.X+2)^64)*(2*(Polynomial.X+2)^96+3)+1+5
noncomputable def currentWorkPolynomial : Polynomial ℕ := countsWorkPolynomial+3*(60*(sizePolynomial+1)^2)+4

theorem sizePolynomial_eval (security : ℕ) : sizePolynomial.eval security = sizeBound security := by
  simp only [sizePolynomial, sizeBound, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_ofNat]

theorem countsWorkPolynomial_eval (security : ℕ) : countsWorkPolynomial.eval security = countsWork security := by
  simp only [countsWorkPolynomial, countsWork, PublicParameterProgram.workPolynomial_eval, powerCounterWork,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat]
  norm_num
  ring

theorem currentWorkPolynomial_eval (security : ℕ) : currentWorkPolynomial.eval security = currentWork security := by
  simp only [currentWorkPolynomial, currentWork, countsWorkPolynomial_eval, sizePolynomial_eval,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat, Polynomial.eval_one]

end CurrentAFT.BinaryProposalMetadata
