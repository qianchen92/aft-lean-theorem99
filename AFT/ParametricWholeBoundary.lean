import AFT.ParametricIndependentTable
import AFT.WholeBoundaryTablePolynomial
import AFT.ActualBoundaryComplementProgram

/-! # Ordered executable syntax for the entire legal input projection

A body-positive complementary factor has the zero joint kernel. Keeping it
as an explicit zero leaf avoids deciding equality of decoded real kernels.
-/
namespace AFT.RationalNumerics
open V7Calibration

abbrev WholeBoundaryCode (Leaf : Type*) := Bool × Leaf

def wholeBoundaryShape {Leaf : Type*} (shape : Leaf → KernelShape)
    (code : WholeBoundaryCode Leaf) : KernelShape := shape code.2

/-- The first copy is the identity and the second copy is the full
complementary product, with its original real scalar expression retained. -/
def parametricWholeBoundaryTable {Scalar Leaf : Type*} (table : ParametricSeedTable Scalar Leaf) :
    ParametricSeedTable Scalar (WholeBoundaryCode Leaf) :=
  table.rename (fun code => (true,code)) ++
    (table.rename (fun code => (false,code))).scale (.rational (-1))

theorem parametricWholeBoundaryTable_length {Scalar Leaf : Type*} (table : ParametricSeedTable Scalar Leaf) :
    (parametricWholeBoundaryTable table).length=2*table.length := by
  simp only [parametricWholeBoundaryTable,List.length_append,ParametricSeedTable.scale_length,
    ParametricSeedTable.rename,List.length_map]
  omega

noncomputable section
open RepresentedPolynomial
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
variable {Color Output Leaf Scalar : Type*} [Fintype Color] [DecidableEq Color]

/-- This transform acts on the original whole joint kernel. It does not
split the input into rank-one factors. -/
def complementaryKernelSeed (matrix : Color → Color → ℝ) (seed : InputSeed Color) : InputSeed Color :=
  ⟨seed.primaryOrder,seed.bodyOrder,
    if seed.bodyOrder=0 then MixedKernel.matrixApply (fun _ => matrix) seed.kernel else 0⟩

def wholeBoundaryDecode (primary : FiniteDist Color)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (interior : Finset Color)
    (decode : Leaf → InputSeed Color) (code : WholeBoundaryCode Leaf) : InputSeed Color :=
  if code.1 then decode code.2 else complementaryKernelSeed
    (fun input output => primary.weight input*
      LinearMap.toMatrix' (LinearMap.id-legalInputProjection operator
        (boundaryIdealProjection interior primary.weight)) output input/primary.weight output) (decode code.2)

omit [DecidableEq Color] in
theorem complementaryKernelSeed_polynomial (matrix : Color → Color → ℝ)
    (seed : InputSeed Color) (primary body : Color → Table Output) :
    inputKernelPolynomial primary body (complementaryKernelSeed matrix seed)=
      inputKernelPolynomial (matrixPolynomialForm matrix primary) 0 seed := by
  by_cases hb : seed.bodyOrder=0
  · rw [inputKernelPolynomial_all_primary primary body (complementaryKernelSeed matrix seed) hb,
      inputKernelPolynomial_all_primary (matrixPolynomialForm matrix primary) 0 seed hb]
    change kernelPolynomial (fun _ => primary)
      (if seed.bodyOrder=0 then MixedKernel.matrixApply (fun _ => matrix) seed.kernel else 0)=_
    rw [if_pos hb,kernelPolynomial_matrixApply]
  · rw [inputKernelPolynomial_body_zero _ seed hb]
    unfold inputKernelPolynomial complementaryKernelSeed kernelPolynomial
    simp only [if_neg hb,Pi.zero_apply,map_zero,zero_mul,Finset.sum_const_zero]

theorem wholeBoundaryDecode_polynomial (primary : FiniteDist Color)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (interior : Finset Color)
    (decode : Leaf → InputSeed Color) (primaryForm bodyForm : Color → Table Output) (code : Leaf) :
    inputKernelPolynomial primaryForm bodyForm
      (wholeBoundaryDecode primary operator interior decode (false,code))=
      inputKernelPolynomial (complementaryPrimaryForm primary operator interior primaryForm) 0 (decode code) := by
  simp only [wholeBoundaryDecode,Bool.false_eq_true,if_false]
  exact complementaryKernelSeed_polynomial _ _ _ _

/-- Scalar syntax may contain actual Gaussian source weights. The theorem
keeps their real denotation, independently of rational evaluation. -/
theorem parametricWholeBoundaryTable_polynomial (primary body : FiniteDist Color)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (interior : Finset Color)
    (scalar : Scalar → ℝ) (decode : Leaf → InputSeed Color)
    (table : ParametricSeedTable Scalar Leaf) (primaryForm bodyForm : Color → Table Output) :
    inputKernelPolynomialHom primaryForm bodyForm
      ((parametricWholeBoundaryTable table).interpret scalar (wholeBoundaryDecode primary operator interior decode))=
      inputKernelPolynomialHom primaryForm bodyForm
        (wholeBoundaryTable primary body operator interior (table.interpret scalar decode)) := by
  rw [wholeBoundaryTable_inputHom]
  simp only [parametricWholeBoundaryTable,ParametricSeedTable.interpret_append,
    ParametricSeedTable.interpret_scale,ParametricSeedTable.interpret_rename,
    ScalarProgram.denote,Rat.cast_neg,Rat.cast_one,neg_one_smul,map_add,map_neg]
  rw [←sub_eq_add_neg]
  congr 1
  induction table with
  | nil => simp
  | cons term rest ih =>
    simp only [ParametricSeedTable.interpret_cons,map_add,ih]
    congr 1
    simp only [ParametricSeedTerm.interpret,inputKernelPolynomialHom_smul,map_list_prod,
      List.map_map,Function.comp_def,inputKernelPolynomialHom_X]
    congr 1
    apply congrArg List.prod
    apply List.map_congr_left
    intro code _
    exact wholeBoundaryDecode_polynomial primary operator interior decode primaryForm bodyForm code

theorem wholeBoundaryDecode_shape (primary : FiniteDist Color)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (interior : Finset Color)
    (decode : Leaf → InputSeed Color) (shape : Leaf → KernelShape)
    (hshape : ∀ code,(decode code).primaryOrder=(shape code).primary ∧ (decode code).bodyOrder=(shape code).body)
    (code : WholeBoundaryCode Leaf) :
    (wholeBoundaryDecode primary operator interior decode code).primaryOrder=(wholeBoundaryShape shape code).primary ∧
      (wholeBoundaryDecode primary operator interior decode code).bodyOrder=(wholeBoundaryShape shape code).body := by
  unfold wholeBoundaryDecode wholeBoundaryShape
  split_ifs <;> exact hshape code.2

end
end AFT.RationalNumerics
