import CurrentAFT.CurrentBinaryAffineEmitter
import CurrentAFT.CurrentBinaryEmitterPolynomial
import CurrentAFT.CurrentBinaryEmitterSemantic
import AFT.BinaryIntegerDivision

/-! Deterministic evaluation of the emitted integral affine arrays. Matrix
entries, input coordinates and offsets are read from stored buffers; all
products, sums and Euclidean residues use Boolean-list algorithms. -/
namespace CurrentAFT.ActualAffineEvaluator
open AFT BinaryArithmetic RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

abbrev Coordinate (count : ℕ) := Vector IntegerBits count × IntegerBits


def nativeCoordinate {count : ℕ} (point : Coordinate count) (index : Fin (count+1)) : IntegerBits :=
  Fin.lastCases point.2 point.1.get index


def coordinateEntry {count : ℕ} (point : Coordinate count) (index : Fin (count+1)) : CountedValue IntegerBits :=
  let inside := lessCounter index.val count
  if h : inside.value=true then
    let found := readVector IntegerBits.zero point.1 ⟨index.val,(lessCounter_value _ _).mp h⟩
    ⟨found.value,inside.work+found.work+2⟩
  else ⟨point.2,inside.work+2⟩

 theorem coordinateEntry_value {count : ℕ} (point : Coordinate count) (index : Fin (count+1)) :
    (coordinateEntry point index).value=nativeCoordinate point index := by
  refine Fin.lastCases ?_ (fun edge => ?_) index
  · have hn : ¬(lessCounter (Fin.last count).val count).value=true := by rw [lessCounter_value];simp
    simp only [coordinateEntry,dif_neg hn,nativeCoordinate,Fin.lastCases_last]
  · have hy : (lessCounter edge.castSucc.val count).value=true := (lessCounter_value _ _).mpr edge.isLt
    simp only [coordinateEntry,dif_pos hy,readVector_value,nativeCoordinate,Fin.lastCases_castSucc]
    congr 1

 theorem coordinateEntry_work {count : ℕ} (point : Coordinate count) (index : Fin (count+1)) :
    (coordinateEntry point index).work ≤ 10*count+20 := by
  have hi := lessCounter_work_left index.val count
  have hx := index.isLt
  unfold coordinateEntry
  dsimp only
  split_ifs with h
  · have hr := readVector_work IntegerBits.zero point.1 (⟨index.val,(lessCounter_value _ _).mp h⟩ : Fin count)
    dsimp only
    omega
  · dsimp only
    omega


def zeroCoordinate (count : ℕ) : CountedValue (Coordinate count) :=
  let edges := storeData count (fun _ => (⟨IntegerBits.zero,1⟩ : CountedValue IntegerBits))
  ⟨(edges.value,IntegerBits.zero),edges.work+1⟩

 theorem zeroCoordinate_work (count : ℕ) : (zeroCoordinate count).work ≤ 3*count+3 := by
  have h := storeData_work count 1 (fun _ => (⟨IntegerBits.zero,1⟩ : CountedValue IntegerBits)) (fun _ => le_rfl)
  change _+1≤_
  omega


def productEntry {count : ℕ} (data : BinaryAffineData count) (input : Vector IntegerBits (count+1))
    (row column : Fin (count+1)) : CountedValue IntegerBits :=
  let fallback := zeroCoordinate count
  let point := readVector fallback.value data.columns column
  let coefficient := coordinateEntry point.value row
  let argument := readVector IntegerBits.zero input column
  let result := IntegerBits.multiply coefficient.value argument.value
  ⟨result.value,fallback.work+point.work+coefficient.work+argument.work+result.work+5⟩

 theorem productEntry_value {count : ℕ} (data : BinaryAffineData count) (input : Vector IntegerBits (count+1))
    (row column : Fin (count+1)) :
    (productEntry data input row column).value.decode=
      (nativeCoordinate (data.columns.get column) row).decode*(input.get column).decode := by
  simp only [productEntry,IntegerBits.multiply_value,coordinateEntry_value,readVector_value]


def row {count : ℕ} (modulus : List Bool) (data : BinaryAffineData count)
    (input : Vector IntegerBits (count+1)) (index : Fin (count+1)) : CountedValue (List Bool) :=
  let dot := IntegerBits.sumFin (count+1) (productEntry data input index)
  let offset := coordinateEntry data.offset index
  let total := IntegerBits.add dot.value offset.value
  let result := IntegerBits.residue total.value modulus
  ⟨result.digits,dot.work+offset.work+total.work+result.work+4⟩


def evaluate {count : ℕ} (modulus : List Bool) (data : BinaryAffineData count)
    (input : Vector IntegerBits (count+1)) : CountedValue (Vector (List Bool) (count+1)) :=
  storeData (count+1) (row modulus data input)

 theorem evaluate_integer_value {count : ℕ} (modulus : List Bool) (hq : 0<value modulus)
    (data : BinaryAffineData count) (input : Vector IntegerBits (count+1)) (index : Fin (count+1)) :
    ((value ((evaluate modulus data input).value.get index)):ℤ)=
      ((∑ column, (nativeCoordinate (data.columns.get column) index).decode*(input.get column).decode)+
        (nativeCoordinate data.offset index).decode)%(value modulus:ℤ) := by
  simp only [evaluate,storeData_get,row]
  rw [IntegerBits.residue_value _ _ hq,IntegerBits.add_value,IntegerBits.sumFin_value,coordinateEntry_value]
  simp only [productEntry_value]


def Bounded {count : ℕ} (data : BinaryAffineData count) (input : Vector IntegerBits (count+1)) (bits : ℕ) : Prop :=
  (∀ column index,(nativeCoordinate (data.columns.get column) index).digits.length≤bits) ∧
    (∀ index,(nativeCoordinate data.offset index).digits.length≤bits) ∧
    ∀ index,(input.get index).digits.length≤bits


def productWork (count bits : ℕ) : ℕ := 20*(count+1)+50+20*(2*bits+1)^2

def dotWork (count bits : ℕ) : ℕ :=
  (count+1)*(productWork count bits+20*((count+1)+3*bits)+11)+2

def rowWork (count modulusBits bits : ℕ) : ℕ :=
  dotWork count bits+(10*count+20)+(20*((count+1)+3*bits)+9)+60*((count+1)+3*bits+modulusBits+2)^2+14

def workBound (count modulusBits bits : ℕ) : ℕ := (count+1)*(rowWork count modulusBits bits+2)+2

 theorem productEntry_bounds {count : ℕ} (data : BinaryAffineData count) (input : Vector IntegerBits (count+1))
    (bits : ℕ) (hb : Bounded data input bits) (row column : Fin (count+1)) :
    (productEntry data input row column).value.digits.length≤3*bits ∧
      (productEntry data input row column).work≤productWork count bits := by
  let fallback := zeroCoordinate count
  let point := readVector fallback.value data.columns column
  let coefficient := coordinateEntry point.value row
  let argument := readVector IntegerBits.zero input column
  have hc : coefficient.value.digits.length≤bits := by rw [coordinateEntry_value,readVector_value];exact hb.1 column row
  have ha : argument.value.digits.length≤bits := by rw [readVector_value];exact hb.2.2 column
  have hm := IntegerBits.multiply_length coefficient.value argument.value
  have wm := IntegerBits.multiply_work coefficient.value argument.value
  have wm' : (IntegerBits.multiply coefficient.value argument.value).work≤20*(2*bits+1)^2+2 :=
    wm.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left (by omega) 2)) 2)
  constructor
  · change (IntegerBits.multiply coefficient.value argument.value).value.digits.length≤_
    omega
  · have wf := zeroCoordinate_work count
    have wp := readVector_work fallback.value data.columns column
    have wc := coordinateEntry_work point.value row
    have wa := readVector_work IntegerBits.zero input column
    change fallback.work+point.work+coefficient.work+argument.work+(IntegerBits.multiply coefficient.value argument.value).work+5≤_
    change fallback.work≤_ at wf
    change point.work≤_ at wp
    change coefficient.work≤_ at wc
    change argument.work≤_ at wa
    unfold productWork
    omega

 theorem row_work {count : ℕ} (modulus : List Bool) (data : BinaryAffineData count) (input : Vector IntegerBits (count+1))
    (bits : ℕ) (hb : Bounded data input bits) (index : Fin (count+1)) :
    (row modulus data input index).work≤rowWork count modulus.length bits := by
  let dot := IntegerBits.sumFin (count+1) (productEntry data input index)
  let offset := coordinateEntry data.offset index
  let total := IntegerBits.add dot.value offset.value
  have he (column) := productEntry_bounds data input bits hb index column
  have hd : dot.value.digits.length≤(count+1)+3*bits :=
    IntegerBits.sumFin_length (count+1) (3*bits) _ (fun column => (he column).1)
  have wd : dot.work≤dotWork count bits :=
    IntegerBits.sumFin_work (count+1) (3*bits) (productWork count bits) _ (fun column => (he column).1) (fun column => (he column).2)
  have ho : offset.value.digits.length≤bits := by rw [coordinateEntry_value];exact hb.2.1 index
  have ht := IntegerBits.add_length dot.value offset.value
  change total.value.digits.length≤_ at ht
  have wt := IntegerBits.add_work dot.value offset.value
  have wr := IntegerBits.residue_work total.value modulus
  have wr' : (IntegerBits.residue total.value modulus).work≤60*((count+1)+3*bits+modulus.length+2)^2+10 := by
    apply wr.trans
    apply Nat.add_le_add_right
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    omega
  have wo := coordinateEntry_work data.offset index
  change dot.work+offset.work+total.work+(IntegerBits.residue total.value modulus).work+4≤_
  change offset.work≤_ at wo
  change total.work≤_ at wt
  unfold rowWork
  omega

 theorem evaluate_work {count : ℕ} (modulus : List Bool) (data : BinaryAffineData count) (input : Vector IntegerBits (count+1))
    (bits : ℕ) (hb : Bounded data input bits) : (evaluate modulus data input).work≤workBound count modulus.length bits :=
  storeData_work _ _ _ (fun index => row_work modulus data input bits hb index)


def bitSize {count : ℕ} (data : BinaryAffineData count) (input : Vector IntegerBits (count+1)) : ℕ :=
  (∑ column : Fin (count+1),∑ index : Fin (count+1),(nativeCoordinate (data.columns.get column) index).digits.length)+
    (∑ index : Fin (count+1),(nativeCoordinate data.offset index).digits.length)+
    ∑ index : Fin (count+1),(input.get index).digits.length

 theorem bounded_bitSize {count : ℕ} (data : BinaryAffineData count) (input : Vector IntegerBits (count+1)) :
    Bounded data input (bitSize data input) := by
  constructor
  · intro column index
    have hi := Finset.single_le_sum (a:=index) (s:=Finset.univ)
      (f:=fun index : Fin (count+1) => (nativeCoordinate (data.columns.get column) index).digits.length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    have hc := Finset.single_le_sum (a:=column) (s:=Finset.univ)
      (f:=fun column : Fin (count+1) => ∑ index : Fin (count+1),(nativeCoordinate (data.columns.get column) index).digits.length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    dsimp only at hi hc
    unfold bitSize
    omega
  · constructor
    · intro index
      have hi := Finset.single_le_sum (a:=index) (s:=Finset.univ)
        (f:=fun index : Fin (count+1) => (nativeCoordinate data.offset index).digits.length)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
      dsimp only at hi
      unfold bitSize
      omega
    · intro index
      have hi := Finset.single_le_sum (a:=index) (s:=Finset.univ)
        (f:=fun index : Fin (count+1) => (input.get index).digits.length)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
      dsimp only at hi
      unfold bitSize
      omega

 theorem evaluate_work_size {count : ℕ} (modulus : List Bool) (data : BinaryAffineData count) (input : Vector IntegerBits (count+1)) :
    (evaluate modulus data input).work≤workBound count modulus.length (bitSize data input) :=
  evaluate_work modulus data input _ (bounded_bitSize data input)


def current (security : ℕ) (data : CurrentBinaryAffineEmitter.Data security)
    (input : Vector IntegerBits (CurrentBinaryAffinePrimitives.Size security)) :
    CountedValue (Vector (List Bool) (CurrentBinaryAffinePrimitives.Size security)) :=
  let metadata := CurrentEmissionMetadata.current security
  let modulus := PublicParameterProgram.modulus security
  let code := canonicalCounter modulus.count
  let result := evaluate code.digits data input
  ⟨result.value,metadata.work+modulus.work+code.work+result.work+4⟩

noncomputable section
open scoped Classical
attribute [local irreducible] CurrentEmissionMetadata.current CurrentProposalDimensions.current PublicParameterProgram.modulus
  Parameters.dimension Parameters.bodySize Parameters.legCount Parameters.base


def decodeInput (security : ℕ) (input : Vector IntegerBits (CurrentBinaryAffinePrimitives.Size security)) :
    Fin (Parameters.dimension security) → ℤ :=
  fun index => (input.get ((CurrentEmissionMetadata.vertexEquiv security).symm index)).decode


def decodeOutput (security : ℕ) (output : Vector (List Bool) (CurrentBinaryAffinePrimitives.Size security)) : CurrentZeroFiber.Word security :=
  fun index => (value (output.get ((CurrentEmissionMetadata.vertexEquiv security).symm index)) : ZMod (Parameters.modulus security))

 theorem nativeCoordinate_current (security : ℕ) (point : CurrentBinaryAffineEmitter.Coordinate security)
    (index : Fin (CurrentBinaryAffinePrimitives.Size security)) :
    (nativeCoordinate point index).decode=
      CurrentBinaryAffineEmitter.decodeCoordinate security point (CurrentEmissionMetadata.vertexEquiv security index) := by
  refine Fin.lastCases ?_ (fun edge => ?_) index
  · have hv : CurrentEmissionMetadata.vertexEquiv security (Fin.last (CurrentEmissionMetadata.current security).edges)=
        CurrentAffineGeometry.coordinateNumbering security (.inr ()) := by
      apply Fin.ext
      change (CurrentEmissionMetadata.current security).edges=CurrentAffineGeometry.edgeCount security
      exact (CurrentEmissionMetadata.current_values security).2.1
    rw [hv]
    simp only [nativeCoordinate,Fin.lastCases_last,CurrentBinaryAffineEmitter.decodeCoordinate,CurrentAffineLoad.packSource,Equiv.symm_apply_apply,Sum.elim_inr]
  · have hv : CurrentEmissionMetadata.vertexEquiv security edge.castSucc=
        CurrentAffineGeometry.coordinateNumbering security (.inl (edge.cast (CurrentEmissionMetadata.current_values security).2.1)) := by
      apply Fin.ext
      rfl
    rw [hv]
    simp only [nativeCoordinate,Fin.lastCases_castSucc,CurrentBinaryAffineEmitter.decodeCoordinate,CurrentAffineLoad.packSource,
      Equiv.symm_apply_apply,Sum.elim_inl,Fin.cast_cast,Fin.cast_eq_self]

 theorem current_value (security : ℕ) (data : CurrentBinaryAffineEmitter.Data security)
    (input : Vector IntegerBits (CurrentBinaryAffinePrimitives.Size security)) :
    decodeOutput security (current security data input).value=
      fun index => (((CurrentBinaryAffineEmitter.matrix security data).mulVec (decodeInput security input) index+
        CurrentBinaryAffineEmitter.offset security data index:ℤ):ZMod (Parameters.modulus security)) := by
  funext index
  let native := (CurrentEmissionMetadata.vertexEquiv security).symm index
  have hq : 0<value (canonicalCounter (PublicParameterProgram.modulus security).count).digits := by
    rw [canonicalCounter_value,PublicParameterProgram.modulus_value]
    exact (Parameters.modulus_spec security).2.pos
  have hv := evaluate_integer_value (canonicalCounter (PublicParameterProgram.modulus security).count).digits hq data input native
  rw [canonicalCounter_value,PublicParameterProgram.modulus_value] at hv
  have hm : (∑ column,(nativeCoordinate (data.columns.get column) native).decode*(input.get column).decode)=
      (CurrentBinaryAffineEmitter.matrix security data).mulVec (decodeInput security input) index := by
    rw [Matrix.mulVec,dotProduct,← Equiv.sum_comp (CurrentEmissionMetadata.vertexEquiv security)]
    apply Finset.sum_congr rfl
    intro column _
    rw [nativeCoordinate_current]
    simp only [CurrentBinaryAffineEmitter.matrix,decodeInput,native,Equiv.symm_apply_apply,Equiv.apply_symm_apply]
  have ho : (nativeCoordinate data.offset native).decode=CurrentBinaryAffineEmitter.offset security data index := by
    rw [nativeCoordinate_current]
    simp only [native,Equiv.apply_symm_apply]
    rfl
  change ((value ((evaluate _ data input).value.get native)):ZMod (Parameters.modulus security))=_
  rw [PublicParameterProgram.modulus_value]
  rw [← Int.cast_natCast,hv,hm,ho]
  simp

/-- Affine evaluation on residue inputs, independently of the chosen signed
integer representatives of those inputs. This holds for every stored matrix
and offset, rather than only the values returned by the sampler. -/
 theorem affine_value (security : ℕ) (data : CurrentBinaryAffineEmitter.Data security)
    (input : Vector IntegerBits (CurrentBinaryAffinePrimitives.Size security)) :
    decodeOutput security (current security data input).value=
      ((CurrentBinaryAffineEmitter.matrix security data).map (Int.castRingHom (ZMod (Parameters.modulus security)))).mulVec
        (fun index => (decodeInput security input index:ZMod (Parameters.modulus security))) +
      fun index => (CurrentBinaryAffineEmitter.offset security data index:ZMod (Parameters.modulus security)) := by
  rw [current_value]
  funext index
  simp only [Matrix.mulVec,dotProduct,Matrix.map_apply,Pi.add_apply,Int.cast_add,Int.cast_mul,Int.cast_sum]
  rfl

 theorem emitted_value (security : ℕ) (layout : CurrentLayoutDraw.Cache security)
    (sample : Option (CurrentMaterializedCompletion.Result security))
    (input : Vector IntegerBits (CurrentBinaryAffinePrimitives.Size security)) :
    decodeOutput security (current security (CurrentBinaryAffineEmitter.emit security layout sample) input).value=
      fun index => (((NumericalAffineTransport.realizeResult security layout.layout
          (sample.map CurrentMaterializedCompletion.Result.sample)).matrix.mulVec (decodeInput security input) index+
        (NumericalAffineTransport.realizeResult security layout.layout
          (sample.map CurrentMaterializedCompletion.Result.sample)).offset index:ℤ):ZMod (Parameters.modulus security)) := by
  rw [current_value,CurrentBinaryEmitterSemantic.emit_matrix,CurrentBinaryEmitterSemantic.emit_offset]

 theorem workBound_mono {count count' modulusBits modulusBits' bits bits' : ℕ}
    (hc : count ≤ count') (hq : modulusBits ≤ modulusBits') (hb : bits ≤ bits') :
    workBound count modulusBits bits≤workBound count' modulusBits' bits' := by
  unfold workBound rowWork dotWork productWork
  gcongr

/-- A polynomial for the actual multiplication, sequential reads, signed
summation and binary division, with polynomial bounds for its three sizes. -/
def budgetPolynomial (count modulusBits bits : Polynomial ℕ) : Polynomial ℕ :=
  let product := 20*(count+1)+50+20*(2*bits+1)^2
  let dot := (count+1)*(product+20*((count+1)+3*bits)+11)+2
  let row := dot+(10*count+20)+(20*((count+1)+3*bits)+9)+
    60*((count+1)+3*bits+modulusBits+2)^2+14
  (count+1)*(row+2)+2

 theorem budgetPolynomial_eval (count modulusBits bits : Polynomial ℕ) (size : ℕ) :
    (budgetPolynomial count modulusBits bits).eval size=
      workBound (count.eval size) (modulusBits.eval size) (bits.eval size) := by
  simp only [budgetPolynomial,workBound,rowWork,dotWork,productWork,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat,
    Polynomial.eval_one]

 theorem naturalPolynomial_mono (polynomial : Polynomial ℕ) {first second : ℕ} (h : first≤second) :
    polynomial.eval first≤polynomial.eval second := by
  simp only [Polynomial.eval_eq_sum,Polynomial.sum_def]
  exact Finset.sum_le_sum (fun exponent _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h exponent))

/-- The parameter preparation is performed by `current`; matrix and input
digit lengths are measured from the actual arrays by `bitSize`. -/
def workPolynomial : Polynomial ℕ :=
  (CurrentProposalResources.metadataWorkPolynomial+8*CurrentProposalResources.countPolynomial+13)+
    PublicParameterProgram.workPolynomial+
    50*(CurrentProposalResources.countPolynomial+1)^2+
    budgetPolynomial CurrentProposalResources.countPolynomial CurrentProposalResources.countPolynomial Polynomial.X+4

/-- No height or runtime hypothesis is needed. The bound is polynomial in the
unary security parameter plus the actual integer-array encoding length. -/
 theorem polynomial_work (security : ℕ) (data : CurrentBinaryAffineEmitter.Data security)
    (input : Vector IntegerBits (CurrentBinaryAffinePrimitives.Size security)) :
    (current security data input).work≤(workPolynomial.eval (security+bitSize data input)) := by
  let size := security+bitSize data input
  let bound := CurrentProposalResources.countPolynomial.eval size
  have hs : security≤size := Nat.le_add_right _ _
  have hb : bitSize data input≤size := Nat.le_add_left _ _
  have hmono := naturalPolynomial_mono CurrentProposalResources.countPolynomial hs
  have hc : (CurrentEmissionMetadata.current security).edges≤bound := by
    have he := (CurrentEmissionMetadata.current_counts security).2.1
    have hd := (CurrentProposalResources.count_bounds security).2.2.2.2
    dsimp only [bound]
    omega
  have hq : (PublicParameterProgram.modulus security).count≤bound := by
    have h := (CurrentProposalResources.count_bounds security).2.2.1
    rw [(CurrentProposalDimensions.current_values security).1] at h
    rw [PublicParameterProgram.modulus_value]
    exact h.trans hmono
  have hl : (canonicalCounter (PublicParameterProgram.modulus security).count).digits.length≤bound := by
    rw [canonicalCounter_length]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=(PublicParameterProgram.modulus security).count))).trans hq
  have hm := (CurrentBinaryEmitterPolynomial.metadata_work security).trans
    (naturalPolynomial_mono (CurrentProposalResources.metadataWorkPolynomial+8*CurrentProposalResources.countPolynomial+13) hs)
  have hp := (PublicParameterProgram.modulus_work security).trans_eq
    (PublicParameterProgram.workPolynomial_eval security).symm
  have hp' := hp.trans (naturalPolynomial_mono PublicParameterProgram.workPolynomial hs)
  have hw := (canonicalCounter_work (PublicParameterProgram.modulus security).count).trans
    (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right hq 1) 2))
  have he := (evaluate_work_size (canonicalCounter (PublicParameterProgram.modulus security).count).digits data input).trans
    (workBound_mono hc hl hb)
  unfold current
  change (CurrentEmissionMetadata.current security).work+(PublicParameterProgram.modulus security).work+
    (canonicalCounter (PublicParameterProgram.modulus security).count).work+
    (evaluate (canonicalCounter (PublicParameterProgram.modulus security).count).digits data input).work+4≤_
  unfold workPolynomial
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat,
    Polynomial.eval_one,budgetPolynomial_eval,Polynomial.eval_X]
  dsimp only [bound,size] at hm hp' hw he
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat] at hm
  omega

/-- A polynomially bounded input encoding gives a security-polynomial
specialization of the unconditional encoding-length bound. -/
 theorem polynomial_work_of_size (inputBound : Polynomial ℕ) (security : ℕ)
    (data : CurrentBinaryAffineEmitter.Data security)
    (input : Vector IntegerBits (CurrentBinaryAffinePrimitives.Size security))
    (hsize : bitSize data input ≤ inputBound.eval security) :
    (current security data input).work≤(workPolynomial.comp (Polynomial.X+inputBound)).eval security := by
  apply (polynomial_work security data input).trans
  rw [Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_X]
  exact naturalPolynomial_mono workPolynomial (Nat.add_le_add_left hsize security)

end
end CurrentAFT.ActualAffineEvaluator
