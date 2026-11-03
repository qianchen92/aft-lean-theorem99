import CurrentAFT.BinaryRankOneFunctional
import CurrentAFT.BinaryMassLiftFormula
import CurrentAFT.BinaryRationalCompare

/-! # Guarded rank-one inversion and mass whitening on stored binary arrays -/
namespace CurrentAFT.BinaryMassLiftKernel
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryRankOneFunctional.current

def prepare {count : ℕ} (sign : Vector RationalBits count) (rate : RationalBits) : RationalResult :=
  let functional := BinaryRankOneFunctional.current sign
  let denominator := RationalBits.add rate functional.data
  let quarter := RationalBits.multiply half half
  let lower := RationalBits.multiply rate quarter.data
  let result := BinaryRationalCompare.maximum denominator.data lower.data
  ⟨result.data, functional.work+denominator.work+quarter.work+lower.work+result.work+6⟩

theorem prepare_value {count : ℕ} (sign : Vector RationalBits count) (rate : RationalBits) :
    (prepare sign rate).data.decode = max
      (rate.decode+∑ color : Fin count,
        (if 2*color.val<count-1 then (-1:ℚ) else if count-1<2*color.val then 1 else 0)*(sign.get color).decode)
      (rate.decode/4) := by
  simp only [prepare, BinaryRationalCompare.maximum_value, RationalBits.add_value,
    RationalBits.multiply_value, half_value, BinaryRankOneFunctional.current_value]
  congr 1
  ring

def prepareHeight (count bits : ℕ) := BinaryRankOneFunctional.height count bits+bits+5
def prepareWork (count bits : ℕ) := BinaryRankOneFunctional.work count bits+
  3*primitiveWorkBound (prepareHeight count bits)+BinaryRationalCompare.workBound (prepareHeight count bits)+9

theorem prepare_bounds {count : ℕ} (sign : Vector RationalBits count) (rate : RationalBits) (bits : ℕ)
    (hs : ∀ color, HeightBound (sign.get color).decode bits) (hr : HeightBound rate.decode bits) :
    HeightBound (prepare sign rate).data.decode (prepareHeight count bits) ∧
      (prepare sign rate).work ≤ prepareWork count bits := by
  let B := prepareHeight count bits
  have hb : bits ≤ B := by dsimp [B, prepareHeight]; omega
  have hfunc := (BinaryRankOneFunctional.current_bounds sign bits hs).1
  have wfunc := (BinaryRankOneFunctional.current_bounds sign bits hs).2
  have hhalf : HeightBound half.decode 2 := by rw [half_value]; norm_num [HeightBound]
  have hquarter : HeightBound (RationalBits.multiply half half).data.decode 4 := by
    rw [RationalBits.multiply_value]
    exact hhalf.mul hhalf
  have hd : HeightBound (RationalBits.add rate (BinaryRankOneFunctional.current sign).data).data.decode B := by
    rw [RationalBits.add_value]
    exact (hr.add hfunc).mono (by dsimp [B, prepareHeight]; omega)
  have hl : HeightBound (RationalBits.multiply rate (RationalBits.multiply half half).data).data.decode B := by
    rw [RationalBits.multiply_value]
    exact (hr.mul hquarter).mono (by dsimp [B, prepareHeight]; omega)
  have wd := RationalBits.add_work rate (BinaryRankOneFunctional.current sign).data B
    (hr.mono hb) (hfunc.mono (by dsimp [B, prepareHeight]; omega))
  have wq := RationalBits.multiply_work half half B (hhalf.mono (by dsimp [B, prepareHeight]; omega))
    (hhalf.mono (by dsimp [B, prepareHeight]; omega))
  have wl := RationalBits.multiply_work rate (RationalBits.multiply half half).data B
    (hr.mono hb) (hquarter.mono (by dsimp [B, prepareHeight]; omega))
  have wm := BinaryRationalCompare.maximum_work _ _ B hd hl
  constructor
  · exact BinaryRationalCompare.maximum_height _ _ B hd hl
  · change _+_+_+_+_+6 ≤ _
    dsimp only [prepareWork]
    dsimp only [B] at wd wq wl wm
    omega

def current {count : ℕ} (primary sign input : Vector RationalBits count)
    (rate denominator : RationalBits) (output : Fin count) : RationalResult :=
  let functional := BinaryRankOneFunctional.current input
  let point := readVector zero input output
  let direction := readVector zero sign output
  let atom := readVector zero primary output
  let result := BinaryMassLiftFormula.current point.value functional.data denominator direction.value rate atom.value
  ⟨result.data, functional.work+point.work+direction.work+atom.work+result.work+5⟩

theorem current_value {count : ℕ} (primary sign input : Vector RationalBits count)
    (rate denominator : RationalBits) (output : Fin count) :
    (current primary sign input rate denominator output).data.decode =
      ((input.get output).decode-
        (∑ color : Fin count, (if 2*color.val<count-1 then (-1:ℚ) else if count-1<2*color.val then 1 else 0)*
          (input.get color).decode)/denominator.decode*(sign.get output).decode)/
        (rate.decode*(primary.get output).decode) := by
  simp only [current, BinaryMassLiftFormula.current_value, BinaryRankOneFunctional.current_value, readVector_value]

def operandHeight (count bits : ℕ) := BinaryRankOneFunctional.height count bits+bits
def height (count bits : ℕ) := BinaryMassLiftFormula.height (operandHeight count bits)
def work (count bits : ℕ) := BinaryRankOneFunctional.work count bits+9*count+14+
  BinaryMassLiftFormula.work (operandHeight count bits)

theorem current_bounds {count : ℕ} (primary sign input : Vector RationalBits count)
    (rate denominator : RationalBits) (output : Fin count) (bits : ℕ)
    (hp : ∀ color, HeightBound (primary.get color).decode bits)
    (hs : ∀ color, HeightBound (sign.get color).decode bits)
    (hi : ∀ color, HeightBound (input.get color).decode bits)
    (hr : HeightBound rate.decode bits) (hd : HeightBound denominator.decode bits) :
    HeightBound (current primary sign input rate denominator output).data.decode (height count bits) ∧
      (current primary sign input rate denominator output).work ≤ work count bits := by
  let B := operandHeight count bits
  have hb : bits ≤ B := by dsimp [B, operandHeight]; omega
  have hf := BinaryRankOneFunctional.current_bounds input bits hi
  have hread (values : Vector RationalBits count) (hv : ∀ color, HeightBound (values.get color).decode bits) :
      HeightBound (readVector zero values output).value.decode B := by
    rw [readVector_value]
    exact (hv output).mono hb
  have hformula := BinaryMassLiftFormula.current_bounds _ _ _ _ _ _ B (hread input hi)
    (hf.1.mono (by dsimp [B, operandHeight]; omega)) (hd.mono hb) (hread sign hs) (hr.mono hb) (hread primary hp)
  dsimp only [B] at hformula
  constructor
  · exact hformula.1
  · have wi := readVector_work zero input output
    have ws := readVector_work zero sign output
    have wp := readVector_work zero primary output
    change _+_+_+_+_+5 ≤ _
    dsimp only [work]
    omega

end CurrentAFT.BinaryMassLiftKernel
