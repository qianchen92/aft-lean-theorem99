import AFT.CenteredGaussianResources

/-! # An arithmetic-counted evaluator of the actual Gaussian finite series

Rational operations and integer floor/ceiling are counted here; their
operand lengths are supplied by the separate height theorems. Powers and
factorials use displayed repeated multiplication, never a real oracle.
-/
namespace AFT.RationalNumerics
open scoped BigOperators

structure GaussianArithmetic where
  value : ℚ
  work : ℕ

namespace GaussianArithmetic

def literal (value : ℚ) : GaussianArithmetic := ⟨value,0⟩
def mul (first second : GaussianArithmetic) : GaussianArithmetic :=
  ⟨first.value*second.value,first.work+second.work+1⟩
def add (first second : GaussianArithmetic) : GaussianArithmetic :=
  ⟨first.value+second.value,first.work+second.work+1⟩
def sub (first second : GaussianArithmetic) : GaussianArithmetic :=
  ⟨first.value-second.value,first.work+second.work+1⟩
def div (first second : GaussianArithmetic) : GaussianArithmetic :=
  ⟨first.value/second.value,first.work+second.work+1⟩
def sum {Index : Type*} (indices : Finset Index) (term : Index → GaussianArithmetic) : GaussianArithmetic :=
  ⟨∑i∈indices,(term i).value,(∑i∈indices,(term i).work)+indices.card⟩

def power (value : ℚ) : ℕ → GaussianArithmetic
  | 0 => ⟨1,0⟩
  | exponent+1 => let previous := power value exponent;⟨previous.value*value,previous.work+1⟩

def factorial : ℕ → GaussianArithmetic
  | 0 => ⟨1,0⟩
  | count+1 => let previous := factorial count;⟨(count+1)*previous.value,previous.work+1⟩

@[simp] theorem power_value (value : ℚ) (exponent : ℕ) : (power value exponent).value=value^exponent := by
  induction exponent with
  | zero => simp only [power,pow_zero]
  | succ exponent ih => simp only [power,ih,pow_succ]
@[simp] theorem power_work (value : ℚ) (exponent : ℕ) : (power value exponent).work=exponent := by
  induction exponent with
  | zero => rfl
  | succ exponent ih => simp only [power,ih]
@[simp] theorem factorial_value (count : ℕ) : (factorial count).value=count.factorial := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [factorial,ih,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
@[simp] theorem factorial_work (count : ℕ) : (factorial count).work=count := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [factorial,ih]

def arctan (value : ℚ) (terms : ℕ) : GaussianArithmetic :=
  sum (Finset.range terms) (fun index =>
    let numerator := (power (-1) index).mul (power value (2*index+1))
    let result := numerator.div (literal (2*index+1))
    ⟨result.value,result.work+2⟩)

def pi (bits : ℕ) : GaussianArithmetic :=
  (literal 4).mul ((arctan (1/2) (bits+3)).add (arctan (1/3) (bits+3)))

def taylor (value : ℚ) (terms : ℕ) : GaussianArithmetic :=
  sum (Finset.range terms) (fun index => (power value index).div (factorial index))

def exponential (argument : ℚ) (bits : ℕ) : GaussianArithmetic :=
  let clipped := max argument 0
  let scale := expScale argument
  let polynomial := taylor (clipped/(scale : ℚ)) (bits+scale+1)
  let result := power polynomial.value⁻¹ scale
  ⟨result.value,polynomial.work+result.work+8⟩

def gaussian (squaredWidth : ℚ) (point : ℤ) (bits : ℕ) : GaussianArithmetic :=
  let ratio := gaussianRatio squaredWidth point
  let precision := bits+⌈ratio⌉₊+1
  let piValue := pi precision
  let exponentialValue := exponential (piValue.value*ratio) (bits+1)
  ⟨exponentialValue.value,piValue.work+exponentialValue.work+8⟩

/-- Denominator clearing and the translated integer point are exact finite
integer/rational operations before the same Gaussian evaluator is run. -/
def centered (squaredWidth center : ℚ) (point : ℤ) (bits : ℕ) : GaussianArithmetic :=
  let computed := gaussian (centeredGaussianSquaredWidth squaredWidth center)
    (centeredGaussianNumerator center point) bits
  ⟨computed.value,computed.work+6⟩

@[simp] theorem arctan_value (value : ℚ) (terms : ℕ) : (arctan value terms).value=arctanSum value terms := by
  simp only [arctan,sum,mul,div,literal,power_value,arctanSum,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
@[simp] theorem pi_value (bits : ℕ) : (pi bits).value=piApprox bits := by
  simp only [pi,mul,add,literal,arctan_value,piApprox]
@[simp] theorem taylor_value (value : ℚ) (terms : ℕ) : (taylor value terms).value=expSum value terms := by
  simp only [taylor,sum,div,power_value,factorial_value,expSum]
@[simp] theorem exponential_value (argument : ℚ) (bits : ℕ) : (exponential argument bits).value=expNegApprox argument bits := by
  simp only [exponential,power_value,taylor_value,expNegApprox,expNegScaled]
@[simp] theorem gaussian_value (squaredWidth : ℚ) (point : ℤ) (bits : ℕ) :
    (gaussian squaredWidth point bits).value=gaussianApprox squaredWidth point bits := by
  simp only [gaussian,exponential_value,pi_value,gaussianApprox,gaussianGuard]
@[simp] theorem centered_value (squaredWidth center : ℚ) (point : ℤ) (bits : ℕ) :
    (centered squaredWidth center point bits).value=centeredGaussianApprox squaredWidth center point bits := by
  simp only [centered,gaussian_value,centeredGaussianApprox]

theorem arctan_work (value : ℚ) (terms : ℕ) : (arctan value terms).work≤terms*(3*terms+6) := by
  simp only [arctan,sum,div,mul,literal,power_work,Finset.card_range,Nat.add_zero]
  have hh : (∑i∈Finset.range terms,(i+(2*i+1)+1+1+2))≤terms*(3*terms+5) := by
    calc
      _ ≤ ∑_i∈Finset.range terms,(3*terms+5) := by
        apply Finset.sum_le_sum
        intro i hi
        have := Finset.mem_range.mp hi
        omega
      _ = _ := by simp
  nlinarith

theorem pi_work (bits : ℕ) : (pi bits).work≤8*(bits+4)^2 := by
  have h1 := arctan_work (1/2) (bits+3)
  have h2 := arctan_work (1/3) (bits+3)
  simp only [pi,mul,add,literal,Nat.zero_add]
  nlinarith

theorem taylor_work (value : ℚ) (terms : ℕ) : (taylor value terms).work≤terms*(2*terms+2) := by
  simp only [taylor,sum,div,power_work,factorial_work,Finset.card_range]
  have hh : (∑i∈Finset.range terms,(i+i+1))≤terms*(2*terms+1) := by
    calc
      _ ≤ ∑_i∈Finset.range terms,(2*terms+1) := by
        apply Finset.sum_le_sum
        intro i hi
        have := Finset.mem_range.mp hi
        omega
      _ = _ := by simp
  nlinarith

theorem gaussian_work (squaredWidth : ℚ) (point : ℤ) (bits : ℕ) :
    (gaussian squaredWidth point bits).work≤
      8*(gaussianPiPrecision squaredWidth point bits+4)^2+
      gaussianTaylorTerms squaredWidth point bits*(2*gaussianTaylorTerms squaredWidth point bits+2)+
      gaussianExpScale squaredWidth point bits+16 := by
  have hp := pi_work (gaussianPiPrecision squaredWidth point bits)
  have ht := taylor_work
    (max (piApprox (gaussianPiPrecision squaredWidth point bits)*gaussianRatio squaredWidth point) 0 /
      (gaussianExpScale squaredWidth point bits : ℚ)) (gaussianTaylorTerms squaredWidth point bits)
  have hc (scale : ℕ) : bits+1+scale+1=bits+scale+2 := by omega
  simp only [gaussian,exponential,pi_value,power_work,gaussianPiPrecision,gaussianTaylorTerms,
    gaussianExpScale,gaussianGuard,hc] at hp ht ⊢
  omega

end GaussianArithmetic
end AFT.RationalNumerics
