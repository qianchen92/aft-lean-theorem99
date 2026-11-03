import AFT.OrderedSeedFactors
import AFT.RepresentedLogarithm

/-! # Ordered polynomial programs with explicit numerical scalar leaves

Scalar expressions distinguish the real coefficients in the proved table from
rational approximations evaluated by the sampler. No equality test on real
kernels or real coefficients occurs in the executable syntax.
-/
namespace AFT.RationalNumerics

inductive ScalarProgram (Scalar : Type*) where
  | rational : ℚ → ScalarProgram Scalar
  | atom : Scalar → ScalarProgram Scalar
  | add : ScalarProgram Scalar → ScalarProgram Scalar → ScalarProgram Scalar
  | multiply : ScalarProgram Scalar → ScalarProgram Scalar → ScalarProgram Scalar
  | negate : ScalarProgram Scalar → ScalarProgram Scalar
  | inverse : ScalarProgram Scalar → ScalarProgram Scalar

def ScalarProgram.run {Scalar : Type*} (leaf : Scalar → ℚ) : ScalarProgram Scalar → ℚ
  | .rational value => value
  | .atom code => leaf code
  | .add first second => first.run leaf+second.run leaf
  | .multiply first second => first.run leaf*second.run leaf
  | .negate term => -(term.run leaf)
  | .inverse term => (term.run leaf)⁻¹

structure ParametricSeedTerm (Scalar Code : Type*) where
  coefficient : ScalarProgram Scalar
  factors : List Code

abbrev ParametricSeedTable (Scalar Code : Type*) := List (ParametricSeedTerm Scalar Code)

def ParametricSeedTerm.scale {Scalar Code : Type*} (scalar : ScalarProgram Scalar)
    (term : ParametricSeedTerm Scalar Code) : ParametricSeedTerm Scalar Code :=
  ⟨.multiply scalar term.coefficient,term.factors⟩

def ParametricSeedTerm.multiply {Scalar Code : Type*} (first second : ParametricSeedTerm Scalar Code) :
    ParametricSeedTerm Scalar Code := ⟨.multiply first.coefficient second.coefficient,first.factors++second.factors⟩

def ParametricSeedTable.one {Scalar Code : Type*} : ParametricSeedTable Scalar Code := [⟨.rational 1,[]⟩]
def ParametricSeedTable.seed {Scalar Code : Type*} (code : Code) : ParametricSeedTable Scalar Code := [⟨.rational 1,[code]⟩]
def ParametricSeedTable.constant {Scalar Code : Type*} (scalar : ScalarProgram Scalar) : ParametricSeedTable Scalar Code := [⟨scalar,[]⟩]

def ParametricSeedTable.scale {Scalar Code : Type*} (scalar : ScalarProgram Scalar)
    (table : ParametricSeedTable Scalar Code) : ParametricSeedTable Scalar Code := table.map (ParametricSeedTerm.scale scalar)

def ParametricSeedTable.multiply {Scalar Code : Type*} (first second : ParametricSeedTable Scalar Code) :
    ParametricSeedTable Scalar Code := first.flatMap (fun term => second.map term.multiply)

def ParametricSeedTable.power {Scalar Code : Type*} (table : ParametricSeedTable Scalar Code) : ℕ → ParametricSeedTable Scalar Code
  | 0 => .one
  | count+1 => (table.power count).multiply table

def ParametricSeedTable.truncate {Scalar Code : Type*} (order : Code → ℕ) (cutoff : ℕ)
    (table : ParametricSeedTable Scalar Code) : ParametricSeedTable Scalar Code :=
  table.filter (fun term => (term.factors.map order).sum≤cutoff)

def ParametricSeedTable.exponential {Scalar Code : Type*} (table : ParametricSeedTable Scalar Code) (cutoff : ℕ) :
    ParametricSeedTable Scalar Code :=
  (List.range (cutoff+1)).flatMap (fun count => (table.power count).scale (.rational ((count.factorial : ℚ)⁻¹)))

def ParametricSeedTable.logarithm {Scalar Code : Type*} (table : ParametricSeedTable Scalar Code) (cutoff : ℕ) :
    ParametricSeedTable Scalar Code :=
  (List.range cutoff).flatMap (fun count => (table.power (count+1)).scale (.rational ((-1 : ℚ)^count/(count+1))))

def ParametricSeedTable.finiteCorrection {Scalar Code : Type*} (table : ParametricSeedTable Scalar Code) (cutoff : ℕ) :
    ParametricSeedTable Scalar Code :=
  (List.range (cutoff+1)).flatMap (fun count => (table.power count).scale (.rational ((-1 : ℚ)^count)))

def ParametricSeedTable.compile {Scalar Code : Type*} (leaf : Scalar → ℚ)
    (table : ParametricSeedTable Scalar Code) : OrderedSeedTable Code :=
  table.map (fun term => ⟨term.coefficient.run leaf,term.factors⟩)

open RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
variable {Scalar Code Seed : Type*}

def ScalarProgram.denote (leaf : Scalar → ℝ) : ScalarProgram Scalar → ℝ
  | .rational value => value
  | .atom code => leaf code
  | .add first second => first.denote leaf+second.denote leaf
  | .multiply first second => first.denote leaf*second.denote leaf
  | .negate term => -(term.denote leaf)
  | .inverse term => (term.denote leaf)⁻¹

theorem ScalarProgram.run_cast (leaf : Scalar → ℚ) (program : ScalarProgram Scalar) :
    (program.run leaf : ℝ)=program.denote (fun code => (leaf code : ℝ)) := by
  induction program <;> simp_all [run,denote]

def ParametricSeedTerm.interpret (leaf : Scalar → ℝ) (decode : Code → Seed) (term : ParametricSeedTerm Scalar Code) : Table Seed :=
  term.coefficient.denote leaf • (term.factors.map (fun code => MvPolynomial.X (decode code))).prod

def ParametricSeedTable.interpret (leaf : Scalar → ℝ) (decode : Code → Seed) (table : ParametricSeedTable Scalar Code) : Table Seed :=
  (table.map (ParametricSeedTerm.interpret leaf decode)).sum

@[simp] theorem ParametricSeedTable.interpret_nil (leaf : Scalar → ℝ) (decode : Code → Seed) :
    ParametricSeedTable.interpret leaf decode []=0 := rfl
@[simp] theorem ParametricSeedTable.interpret_cons (leaf : Scalar → ℝ) (decode : Code → Seed)
    (term : ParametricSeedTerm Scalar Code) (rest : ParametricSeedTable Scalar Code) :
    ParametricSeedTable.interpret leaf decode (term::rest)=term.interpret leaf decode+rest.interpret leaf decode := rfl

theorem ParametricSeedTable.interpret_compile (leaf : Scalar → ℚ) (decode : Code → Seed)
    (table : ParametricSeedTable Scalar Code) :
    (table.compile leaf).interpret decode=table.interpret (fun code => (leaf code : ℝ)) decode := by
  induction table with
  | nil => rfl
  | cons term rest ih =>
    simp only [compile,List.map_cons,OrderedSeedTable.interpret_cons,interpret_cons]
    have hhead : OrderedSeedTerm.interpret decode
        (⟨term.coefficient.run leaf,term.factors⟩ : OrderedSeedTerm Code)=term.interpret (fun code => (leaf code : ℝ)) decode := by
      simp only [OrderedSeedTerm.interpret,ParametricSeedTerm.interpret,ScalarProgram.run_cast]
    exact congrArg₂ (·+·) hhead ih

theorem ParametricSeedTable.interpret_append (leaf : Scalar → ℝ) (decode : Code → Seed)
    (first second : ParametricSeedTable Scalar Code) :
    (first++second).interpret leaf decode=first.interpret leaf decode+second.interpret leaf decode := by
  simp only [interpret,List.map_append,List.sum_append]

@[simp] theorem ParametricSeedTable.interpret_one (leaf : Scalar → ℝ) (decode : Code → Seed) :
    (one : ParametricSeedTable Scalar Code).interpret leaf decode=1 := by simp [one,interpret,ParametricSeedTerm.interpret,ScalarProgram.denote]

@[simp] theorem ParametricSeedTable.interpret_variable (leaf : Scalar → ℝ) (decode : Code → Seed) (code : Code) :
    (seed code : ParametricSeedTable Scalar Code).interpret leaf decode=MvPolynomial.X (decode code) := by
  simp [seed,interpret,ParametricSeedTerm.interpret,ScalarProgram.denote]

@[simp] theorem ParametricSeedTable.interpret_constant (leaf : Scalar → ℝ) (decode : Code → Seed) (scalar : ScalarProgram Scalar) :
    (constant scalar : ParametricSeedTable Scalar Code).interpret leaf decode=MvPolynomial.C (scalar.denote leaf) := by
  simp [constant,interpret,ParametricSeedTerm.interpret,MvPolynomial.smul_eq_C_mul]

theorem ParametricSeedTable.interpret_scale (leaf : Scalar → ℝ) (decode : Code → Seed)
    (scalar : ScalarProgram Scalar) (table : ParametricSeedTable Scalar Code) :
    (table.scale scalar).interpret leaf decode=scalar.denote leaf • table.interpret leaf decode := by
  induction table with
  | nil => simp [scale]
  | cons term rest ih =>
    simp only [scale,List.map_cons,interpret_cons,ParametricSeedTerm.scale,ParametricSeedTerm.interpret,
      ScalarProgram.denote,mul_smul,smul_add]
    exact congrArg (fun value => scalar.denote leaf • term.interpret leaf decode+value) ih

theorem ParametricSeedTable.interpret_multiply (leaf : Scalar → ℝ) (decode : Code → Seed)
    (first second : ParametricSeedTable Scalar Code) :
    (first.multiply second).interpret leaf decode=first.interpret leaf decode*second.interpret leaf decode := by
  have hterm (term : ParametricSeedTerm Scalar Code) :
      ParametricSeedTable.interpret leaf decode (second.map term.multiply)=term.interpret leaf decode*second.interpret leaf decode := by
    induction second with
    | nil => simp
    | cons other rest ih =>
      simp only [List.map_cons,interpret_cons,mul_add,ih]
      congr 1
      simp only [ParametricSeedTerm.multiply,ParametricSeedTerm.interpret,ScalarProgram.denote,
        List.map_append,List.prod_append,MvPolynomial.smul_eq_C_mul,map_mul]
      ring
  induction first with
  | nil => simp [multiply]
  | cons term rest ih =>
    simp only [multiply,List.flatMap_cons,interpret_append,interpret_cons,add_mul,hterm]
    exact congrArg (fun value => term.interpret leaf decode*second.interpret leaf decode+value) ih

theorem ParametricSeedTable.interpret_power (leaf : Scalar → ℝ) (decode : Code → Seed)
    (table : ParametricSeedTable Scalar Code) (count : ℕ) :
    (table.power count).interpret leaf decode=(table.interpret leaf decode)^count := by
  induction count with
  | zero => simp [power]
  | succ count ih => rw [power,interpret_multiply,ih,pow_succ]

private theorem interpret_flatMap_range (leaf : Scalar → ℝ) (decode : Code → Seed)
    (tables : ℕ → ParametricSeedTable Scalar Code) (count : ℕ) :
    ParametricSeedTable.interpret leaf decode ((List.range count).flatMap tables)=∑ i∈Finset.range count,(tables i).interpret leaf decode := by
  induction count with
  | zero => simp
  | succ count ih => rw [List.range_succ,List.flatMap_append,List.flatMap_singleton,ParametricSeedTable.interpret_append,ih,Finset.sum_range_succ]

theorem ParametricSeedTable.interpret_exponential (leaf : Scalar → ℝ) (decode : Code → Seed)
    (table : ParametricSeedTable Scalar Code) (cutoff : ℕ) :
    (table.exponential cutoff).interpret leaf decode=RepresentedPolynomial.exponential (table.interpret leaf decode) cutoff := by
  simp only [exponential,interpret_flatMap_range,interpret_scale,interpret_power,ScalarProgram.denote,
    Rat.cast_inv,Rat.cast_natCast,RepresentedPolynomial.exponential,MvPolynomial.smul_eq_C_mul]

theorem ParametricSeedTable.interpret_logarithm (leaf : Scalar → ℝ) (decode : Code → Seed)
    (table : ParametricSeedTable Scalar Code) (cutoff : ℕ) :
    (table.logarithm cutoff).interpret leaf decode=RepresentedPolynomial.logarithm (table.interpret leaf decode) cutoff := by
  simp only [logarithm,interpret_flatMap_range,interpret_scale,interpret_power,ScalarProgram.denote,
    Rat.cast_div,Rat.cast_pow,Rat.cast_neg,Rat.cast_one,Rat.cast_add,Rat.cast_natCast,
    RepresentedPolynomial.logarithm,MvPolynomial.smul_eq_C_mul]

theorem ParametricSeedTable.interpret_finiteCorrection (leaf : Scalar → ℝ) (decode : Code → Seed)
    (table : ParametricSeedTable Scalar Code) (cutoff : ℕ) :
    (table.finiteCorrection cutoff).interpret leaf decode=AFT.finiteCorrection (table.interpret leaf decode) cutoff := by
  simp only [finiteCorrection,interpret_flatMap_range,interpret_scale,interpret_power,ScalarProgram.denote,
    Rat.cast_pow,Rat.cast_neg,Rat.cast_one,AFT.finiteCorrection,MvPolynomial.smul_eq_C_mul]
  apply Finset.sum_congr rfl
  intro count _
  conv_rhs => rw [neg_pow]
  simp only [map_pow,map_neg,map_one]

end
end AFT.RationalNumerics
