import AFT.CountedChartSupports

/-! # Explicit arithmetic for the chart coordinate and palette arrays

Index decoding uses division and remainder in the displayed finite
product equivalences. A modular addition or multiplication is charged for
both its integer operation and its reduction. Integer casts into the field
are charged for reduction as well. These are arithmetic-operation bounds;
they do not identify unit-cost modular operations with bit operations.
-/
namespace AFT.BoundaryCalibration
open RationalRejectionProgram
open scoped BigOperators

/-- Two finite-product decodings (four divisions/remainders), one dimension
product, and the three residue coordinates. -/
def countedChartCoordinates (modulus : ℕ) [NeZero modulus]
    (chart : Fin (modulus*(modulus*modulus))) : CountedValue (Chart (ZMod modulus)) :=
  let outer := finProdFinEquiv.symm chart
  let inner := finProdFinEquiv.symm outer.2
  ⟨((ZMod.finEquiv modulus) outer.1,
      (ZMod.finEquiv modulus) inner.1,(ZMod.finEquiv modulus) inner.2),8⟩

theorem countedChartCoordinates_value (modulus : ℕ) [NeZero modulus]
    (chart : Fin (modulus*(modulus*modulus))) :
    (countedChartCoordinates modulus chart).value=finiteChartEquiv modulus chart := rfl

/-- Width arithmetic, one finite-product decoding, and both integer
translations from the protected window's nonnegative addresses. -/
def countedProtectedInput (cutoff : ℕ) (index : Fin ((2*cutoff+1)*(2*cutoff+1))) :
    CountedValue (GaussianSource.Window cutoff×GaussianSource.Window cutoff) :=
  let pair := finProdFinEquiv.symm index
  ⟨(FiniteConvolutionProgram.windowIndexEquiv cutoff pair.1,
      FiniteConvolutionProgram.windowIndexEquiv cutoff pair.2),7⟩

theorem countedProtectedInput_value (cutoff : ℕ) (index : Fin ((2*cutoff+1)*(2*cutoff+1))) :
    (countedProtectedInput cutoff index).value=finiteInputEquiv cutoff index := rfl

/-- The formula evaluates exactly two modular products and two modular
sums after decoding its chart and protected input. -/
def countedProtectedFeature (cutoff modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]
    (index : Fin ((2*cutoff+1)*(2*cutoff+1)))
    (chart : Fin (modulus*(modulus*modulus))) : CountedValue (Fin modulus) :=
  let coordinates := countedChartCoordinates modulus chart
  let input := countedProtectedInput cutoff index
  let first : ZMod modulus := (input.value.1 : ℤ)
  let second : ZMod modulus := (input.value.2 : ℤ)
  let firstProduct := coordinates.value.2.1*first
  let secondProduct := coordinates.value.2.2*second
  let value := (coordinates.value.1+firstProduct)+secondProduct
  ⟨(ZMod.finEquiv modulus).symm value,coordinates.work+input.work+12⟩

theorem countedProtectedFeature_value (cutoff modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]
    (index : Fin ((2*cutoff+1)*(2*cutoff+1))) (chart : Fin (modulus*(modulus*modulus))) :
    (countedProtectedFeature cutoff modulus index chart).value=
      finiteProtectedFeatures cutoff modulus index chart := rfl

theorem countedProtectedFeature_work (cutoff modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]
    (index : Fin ((2*cutoff+1)*(2*cutoff+1))) (chart : Fin (modulus*(modulus*modulus))) :
    (countedProtectedFeature cutoff modulus index chart).work=27 := rfl

/-- Palette membership tests the two interval endpoints directly. It does
not construct an integer interval or linearly search a finite color set. -/
def countedProtectedPaletteTest (cutoff modulus : ℕ) (boundary baseline : ℤ)
    (index : Fin ((2*cutoff+1)*(2*cutoff+1))) (color : Fin modulus) : CountedValue Bool :=
  let input := countedProtectedInput cutoff index
  let shift := baseline-(input.value.2 : ℤ)
  let lower := boundary+max shift 0
  let upper := (modulus : ℤ)-boundary+min shift 0
  ⟨decide (lower≤ color.val) && decide ((color.val : ℤ)<upper),input.work+10⟩

theorem countedProtectedPaletteTest_value (cutoff modulus : ℕ) (boundary baseline : ℤ)
    (index : Fin ((2*cutoff+1)*(2*cutoff+1))) (color : Fin modulus) :
    (countedProtectedPaletteTest cutoff modulus boundary baseline index color).value=true ↔
      color∈finiteProtectedPalettes cutoff modulus boundary baseline index := by
  simp only [countedProtectedPaletteTest,countedProtectedInput_value,Bool.and_eq_true,
    decide_eq_true_eq,finiteProtectedPalettes,TrimmedSlice.paletteSlice,Finset.mem_filter,
    Finset.mem_univ,true_and,TrimmedSlice.slice,Finset.mem_Ico]

theorem countedProtectedPaletteTest_work (cutoff modulus : ℕ) (boundary baseline : ℤ)
    (index : Fin ((2*cutoff+1)*(2*cutoff+1))) (color : Fin modulus) :
    (countedProtectedPaletteTest cutoff modulus boundary baseline index color).work=17 := rfl

end AFT.BoundaryCalibration
