import CurrentAFT.BinaryFamilyReciprocal
import CurrentAFT.BinaryCoefficientScalarAverage

/-! Palette-valid semantic interfaces. Every multiplication leaf gathers
existing coordinates, so no identity outside the physical palette is needed. -/
namespace CurrentAFT.BinaryFamilyValidSemantics
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
  GradedControlAlgebra BinaryFamilyProduct FixedFamilyPrograms RationalFamilyProductProgram
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem leaf_value (order base : ℕ) (output : TruncatedArity order) (first second : CoefficientProgram order)
    (firstTable secondTable : Table ℚ ℕ ℕ order)
    (hfirst : ∀ arity colors centers, (∀ i, colors.get i<base) → (∀ i, centers.get i<base) →
      (first arity colors centers).value.decode=firstTable arity colors.get centers.get)
    (hsecond : ∀ arity colors centers, (∀ i, colors.get i<base) → (∀ i, centers.get i<base) →
      (second arity colors centers).value.decode=secondTable arity colors.get centers.get)
    (colors : Vector ℕ output.val.1.val) (centers : Vector ℕ output.val.2.val)
    (hc : ∀ i, colors.get i<base) (hb : ∀ i, centers.get i<base) (code : FamilyProductSyntax.Leaf order output) :
    (BinaryFamilyProduct.leaf order output first second colors centers code).value.decode=
      FamilyProductSyntax.value order output firstTable secondTable colors.get centers.get code := by
  have hpc : ∀ i, (gather colors code.primarySlots).value.get i<base := by intro i; rw [gather_get]; exact hc _
  have hbc : ∀ i, (gather centers code.bodySlots).value.get i<base := by intro i; rw [gather_get]; exact hb _
  unfold BinaryFamilyProduct.leaf FamilyProductSyntax.value
  cases code.second <;> simp only [Bool.false_eq_true, if_false, if_true,
    hfirst _ _ _ hpc hbc, hsecond _ _ _ hpc hbc]
  all_goals congr 1 <;> funext index <;> exact gather_get _ _ index

theorem multiply_value (order base : ℕ) (programs : List (Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs)
    (first second : CoefficientProgram order) (firstTable secondTable : Table ℚ ℕ ℕ order)
    (hfirst : ∀ arity colors centers, (∀ i, colors.get i<base) → (∀ i, centers.get i<base) →
      (first arity colors centers).value.decode=firstTable arity colors.get centers.get)
    (hsecond : ∀ arity colors centers, (∀ i, colors.get i<base) → (∀ i, centers.get i<base) →
      (second arity colors centers).value.decode=secondTable arity colors.get centers.get)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<base) (hb : ∀ i, centers.get i<base) :
    (BinaryFamilyArithmetic.multiply order programs first second arity colors centers).value.decode=
      product order firstTable secondTable arity colors.get centers.get := by
  simp only [BinaryFamilyArithmetic.multiply, BinaryFamilyProduct.run, StoredScalarProgram.binaryRun_value,
    lookup_meaning order arity programs hcorrect (hcomplete arity)]
  have he := funext (leaf_value order base arity first second firstTable secondTable hfirst hsecond colors centers hc hb)
  rw [he, FamilyProductSyntax.product_run]

theorem power_value (order base : ℕ) (programs : List (Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs)
    (table : CoefficientProgram order) (actual : Table ℚ ℕ ℕ order)
    (hvalue : ∀ arity colors centers, (∀ i, colors.get i<base) → (∀ i, centers.get i<base) →
      (table arity colors centers).value.decode=actual arity colors.get centers.get)
    (count : ℕ) (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<base) (hb : ∀ i, centers.get i<base) :
    (BinaryFamilyPower.power order programs table count arity colors centers).value.decode=
      power order actual count arity colors.get centers.get := by
  induction count generalizing arity colors centers with
  | zero => exact BinaryFamilyPower.unit_value order arity colors centers
  | succ count ih =>
    exact multiply_value order base programs hcorrect hcomplete
      (BinaryFamilyPower.power order programs table count) table (power order actual count) actual ih hvalue arity colors centers hc hb

theorem reciprocal_value (order base : ℕ) (programs : List (Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs)
    (table : CoefficientProgram order) (actual : Table ℚ ℕ ℕ order)
    (hvalue : ∀ arity colors centers, (∀ i, colors.get i<base) → (∀ i, centers.get i<base) →
      (table arity colors centers).value.decode=actual arity colors.get centers.get)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<base) (hb : ∀ i, centers.get i<base) :
    (BinaryFamilyReciprocal.current order programs table arity colors centers).value.decode=
      reciprocal order actual arity colors.get centers.get := by
  have hcomp : ∀ arity colors centers, (∀ i, colors.get i<base) → (∀ i, centers.get i<base) →
      (BinaryFamilyReciprocal.complement order table arity colors centers).value.decode=
        (unit order-actual : Table ℚ ℕ ℕ order) arity colors.get centers.get := by
    intro arity colors centers hcolors hcenters
    simp only [BinaryFamilyReciprocal.complement, difference_value, BinaryFamilyPower.unit_value,
      hvalue arity colors centers hcolors hcenters, Pi.sub_apply]
  simp only [BinaryFamilyReciprocal.current, sumFin_value]
  simp_rw [power_value order base programs hcorrect hcomplete (BinaryFamilyReciprocal.complement order table)
    (unit order-actual) hcomp _ arity colors centers hc hb]
  exact Fin.sum_univ_eq_sum_range (fun count => power order (unit order-actual) count arity colors.get centers.get) (order+1)

theorem scalarAverage_value (security bits order base : ℕ) (table : IntegerBits → CoefficientProgram order)
    (ideal : ℤ → Table ℚ ℕ ℕ order)
    (hvalue : ∀ scalar arity colors centers, (∀ i, colors.get i<base) → (∀ i, centers.get i<base) →
      (table scalar arity colors centers).value.decode=ideal scalar.decode arity colors.get centers.get)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<base) (hb : ∀ i, centers.get i<base) :
    (BinaryCoefficientScalarAverage.current security bits order table arity colors centers).value.decode=
      RationalScalarFamilyAverage.current security bits order ideal arity colors.get centers.get := by
  unfold BinaryCoefficientScalarAverage.current
  rw [BinaryWindowAverage.evaluate_value, BinaryActivationProgram.cutoff_value]
  simp only [BinaryCoefficientScalarAverage.term, hvalue _ _ _ _ hc hb, IntegerBits.decode, BinaryAnchorProgram.coordinate_value]
  unfold RationalScalarFamilyAverage.current
  have hc' : RationalBackgroundLinearProgram.cutoff security=(security+2)^2-1 := rfl
  rw [hc']
  have hreindex := (FiniteConvolutionProgram.windowIndexEquiv ((security+2)^2-1)).sum_comp
    (fun scalar : GaussianSource.Window ((security+2)^2-1) =>
      RationalProposalProgram.gaussianWeight security ((security+2)^2-1) bits scalar*ideal scalar.val arity colors.get centers.get)
  rw [← hreindex]
  apply Finset.sum_congr rfl
  intro index _
  rw [RationalProposalProgram.gaussianWeight_eq]
  rfl

end
end CurrentAFT.BinaryFamilyValidSemantics
