import AFT.IntegerCoordinateProgram
import AFT.VertexRelabelAffine

/-! # Materializing the final affine output from integer vertex loads

The output consists of a matrix (stored by columns) and an offset.  The
first coordinate is the charge coordinate, followed by the path edges.
Padding is folded into the offset before the vertex permutation.
-/
namespace AFT
open scoped BigOperators

structure IntegerAffineData (count : ℕ) where
  columns : Vector (Vector ℤ count × ℤ) (count+1)
  offset : Vector ℤ count × ℤ
  work : ℕ

/-- Matrix assembly uses only materialized integer loads and a permutation table. -/
def integerAffineAssembly (count : ℕ) (modulus : ℤ)
    (injection : Vector ℤ (count+1))
    (columns : Vector (Vector ℤ (count+1)) (count+1))
    (initial : Vector ℤ (count+1)) (padding : Vector ℤ (count+1))
    (permutation : Vector (Fin (count+1)) (count+1)) : IntegerAffineData count :=
  let inverseColumns := Vector.ofFn (fun column : Fin (count+1) =>
    roundingInverseProgram count modulus injection
      (Vector.ofFn (fun vertex => (columns.get column).get (permutation.get vertex))))
  let paddedLoad := Vector.ofFn (fun vertex : Fin (count+1) =>
    initial.get (permutation.get vertex)+
      ∑ column : Fin (count+1),padding.get column*(columns.get column).get (permutation.get vertex))
  let offset := roundingInverseProgram count modulus injection paddedLoad
  ⟨inverseColumns.map (fun result => result.value),offset.value,
    (∑ column : Fin (count+1),(inverseColumns.get column).work)+offset.work+
      10*(count+1)^2+10*(count+1)⟩

 theorem integerAffineAssembly_work (count : ℕ) (modulus : ℤ)
    (injection : Vector ℤ (count+1))
    (columns : Vector (Vector ℤ (count+1)) (count+1))
    (initial : Vector ℤ (count+1)) (padding : Vector ℤ (count+1))
    (permutation : Vector (Fin (count+1)) (count+1)) :
    (integerAffineAssembly count modulus injection columns initial padding permutation).work≤
      60*(count+1)^3 := by
  have hs : (∑ column : Fin (count+1),
      (roundingInverseProgram count modulus injection
        (Vector.ofFn (fun vertex => (columns.get column).get (permutation.get vertex)))).work)≤
      (count+1)*(20*(count+1)^2) := by
    calc
      _≤∑ _ : Fin (count+1),20*(count+1)^2 := Finset.sum_le_sum (fun column _ => roundingInverseProgram_work count modulus injection _)
      _=_ := by simp
  have ho := roundingInverseProgram_work count modulus injection
    (Vector.ofFn (fun vertex : Fin (count+1) => initial.get (permutation.get vertex)+
      ∑ column : Fin (count+1),padding.get column*(columns.get column).get (permutation.get vertex)))
  simp only [integerAffineAssembly,Vector.get_ofFn]
  nlinarith [Nat.one_le_pow 2 (count+1) (by omega),Nat.one_le_pow 3 (count+1) (by omega)]

/-- Charge first, then edge coordinates, is an explicit integral linear isomorphism. -/
def chargeFirstCoordinates (count : ℕ) : ((Fin count → ℤ) × ℤ) ≃ₗ[ℤ] (Fin (count+1) → ℤ) where
  toFun input := Fin.cons input.2 input.1
  invFun input := (Fin.tail input,input 0)
  left_inv input := by cases input;rfl
  right_inv input := by funext index;exact Fin.cases rfl (fun _ => rfl) index
  map_add' input other := by funext index;exact Fin.cases rfl (fun _ => rfl) index
  map_smul' scalar input := by funext index;exact Fin.cases rfl (fun _ => rfl) index

 def integerAffineBasis (count : ℕ) (column : Fin (count+1)) : (Fin count → ℤ) × ℤ :=
  (chargeFirstCoordinates count).symm (Pi.single column 1)

 theorem integerAffineBasis_zero (count : ℕ) : integerAffineBasis count 0=(0,1) := by
  apply Prod.ext
  · funext index
    simp [integerAffineBasis,chargeFirstCoordinates,Fin.tail,Pi.single_apply]
  · simp [integerAffineBasis,chargeFirstCoordinates,Pi.single_apply]

 theorem integerAffineBasis_succ (count : ℕ) (column : Fin count) :
    integerAffineBasis count column.succ=(Pi.single column 1,0) := by
  apply Prod.ext
  · funext index
    simp [integerAffineBasis,chargeFirstCoordinates,Fin.tail,Pi.single_apply]
  · simp [integerAffineBasis,chargeFirstCoordinates,Pi.single_apply]

 theorem integerAffineBasis_expansion (count : ℕ) (input : (Fin count → ℤ) × ℤ) :
    input=∑ column : Fin (count+1),chargeFirstCoordinates count input column • integerAffineBasis count column := by
  apply (chargeFirstCoordinates count).injective
  simp only [map_sum,map_smul,integerAffineBasis,LinearEquiv.apply_symm_apply]
  funext index
  simp [Pi.single_apply]

noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Exactness of every emitted matrix column and the padded offset. -/
 theorem integerAffineAssembly_exact (count q : ℕ) [NeZero q]
    (injection : Vector ℤ (count+1)) (hinjection : totalCharge injection.get=(q : ℤ))
    (linear : ((Fin count → ℤ) × ℤ) →ₗ[ℤ] ((Fin count → ℤ) × ℤ))
    (initialCoordinates paddingCoordinates : (Fin count → ℤ) × ℤ)
    (columns : Vector (Vector ℤ (count+1)) (count+1))
    (initial padding : Vector ℤ (count+1)) (permutation : Equiv.Perm (Fin (count+1)))
    (hcolumns : ∀ column,(columns.get column).get=
      roundingLoad count injection.get (linear (integerAffineBasis count column)))
    (hinitial : initial.get=roundingLoad count injection.get initialCoordinates)
    (hpadding : padding.get=chargeFirstCoordinates count paddingCoordinates) :
    let result := integerAffineAssembly count q injection columns initial padding (Vector.ofFn permutation)
    (∀ column,((result.columns.get column).1.get,(result.columns.get column).2)=
      vertexRelabelIntegerEquiv count q injection.get hinjection permutation (linear (integerAffineBasis count column))) ∧
    (result.offset.1.get,result.offset.2)=
      vertexRelabelIntegerEquiv count q injection.get hinjection permutation
        (initialCoordinates+linear paddingCoordinates) := by
  have hq : (q : ℤ)≠0 := by exact_mod_cast (NeZero.ne q)
  have exactLoad (load : Vector ℤ (count+1)) (target : (Fin count → ℤ) × ℤ)
      (hload : load.get=roundingLoad count injection.get target) :
      ((roundingInverseProgram count q injection load).value.1.get,
        (roundingInverseProgram count q injection load).value.2)=target := by
    apply roundingLoad_injective count q hq injection.get hinjection
    rw [roundingInverseProgram_load count q injection load hinjection]
    · exact hload
    · rw [hload]
      exact (rounding_image_lattice count q injection.get hinjection _).1 ⟨target,rfl⟩
  constructor
  · intro column
    simp only [integerAffineAssembly,Vector.get_map,Vector.get_ofFn]
    apply exactLoad
    rw [vertexRelabelIntegerEquiv_load,vectorGet_ofFn]
    funext vertex
    simpa only [Vector.get_ofFn] using congrFun (hcolumns column) (permutation vertex)
  · simp only [integerAffineAssembly]
    apply exactLoad
    rw [vertexRelabelIntegerEquiv_load,vectorGet_ofFn]
    have hsum : linear paddingCoordinates=
        ∑ column : Fin (count+1),padding.get column • linear (integerAffineBasis count column) := by
      conv_lhs => rw [integerAffineBasis_expansion count paddingCoordinates]
      simp only [map_sum,map_smul,hpadding]
    let loadMap : ((Fin count → ℤ) × ℤ) →ₗ[ℤ] (Fin (count+1) → ℤ) :=
      (chargeLattice count q).subtype.comp
        (roundingCoordinates count q hq injection.get hinjection).toLinearMap
    have hm (input : (Fin count → ℤ) × ℤ) :
        loadMap input=roundingLoad count injection.get input := rfl
    funext vertex
    simp only [Vector.get_ofFn]
    calc
      _=loadMap initialCoordinates (permutation vertex)+
          ∑ column : Fin (count+1),padding.get column*
            loadMap (linear (integerAffineBasis count column)) (permutation vertex) := by
        simp only [hm,hinitial,hcolumns]
      _=loadMap (initialCoordinates+linear paddingCoordinates) (permutation vertex) := by
        rw [hsum]
        simp only [map_add,map_sum,map_smul,Pi.add_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
      _=_ := rfl

end
end AFT
