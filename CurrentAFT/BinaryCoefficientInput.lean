import CurrentAFT.BinaryCoefficientFiber
import CurrentAFT.BinaryFirstInverseResources

/-! # Charged conversion of natural coefficient coordinates to the palette -/
namespace CurrentAFT.BinaryCoefficientInput
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus lessCounter
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def first (security : ℕ) : Fin (colors security) := BinaryFirstFamily.first security

def entry {count : ℕ} (security : ℕ) (modulus : ℕ) (hmodulus : modulus=colors security)
    (input : Vector ℕ count) (index : Fin count) : CountedValue (Fin (colors security)) :=
  let value := readVector 0 input index
  let checked := lessCounter value.value modulus
  if h : checked.value=true then
    ⟨⟨value.value,by rw [← hmodulus]; exact (lessCounter_value value.value modulus).mp h⟩,value.work+checked.work+2⟩
  else ⟨first security,value.work+checked.work+2⟩

theorem entry_value {count : ℕ} (security : ℕ) (modulus : ℕ) (hmodulus : modulus=colors security)
    (input : Vector ℕ count) (index : Fin count) (hi : input.get index<colors security) :
    (entry security modulus hmodulus input index).value=⟨input.get index,hi⟩ := by
  have ht : (lessCounter (readVector 0 input index).value modulus).value=true := by
    rw [lessCounter_value,readVector_value,hmodulus]; exact hi
  unfold entry
  dsimp only
  rw [dif_pos ht]
  apply Fin.ext
  exact readVector_value 0 input index

def convert {count : ℕ} (security : ℕ) (modulus : ℕ) (hmodulus : modulus=colors security)
    (input : Vector ℕ count) : CountedValue (Vector (Fin (colors security)) count) :=
  storeData count (entry security modulus hmodulus input)

theorem convert_value {count : ℕ} (security : ℕ) (modulus : ℕ) (hmodulus : modulus=colors security)
    (input : Vector ℕ count) (hi : ∀ index, input.get index<colors security) :
    (convert security modulus hmodulus input).value=Vector.ofFn (fun index => ⟨input.get index,hi index⟩) := by
  apply Vector.ext
  intro index hindex
  change (storeData count (entry security modulus hmodulus input)).value.get ⟨index,hindex⟩=
    (Vector.ofFn (fun i => (⟨input.get i,hi i⟩ : Fin (colors security)))).get ⟨index,hindex⟩
  rw [storeData_get,Vector.get_ofFn]
  exact entry_value security modulus hmodulus input ⟨index,hindex⟩ (hi ⟨index,hindex⟩)

def current (security r s : ℕ) (inputs : Vector ℕ r) (centers : Vector ℕ s)
    (kernel : Vector (Fin (colors security)) r → Vector (Fin (colors security)) s → RationalResult) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let primary := convert security modulus.count rfl inputs
  let body := convert security modulus.count rfl centers
  let result := kernel primary.value body.value
  ⟨result.data,modulus.work+primary.work+body.work+result.work+4⟩

theorem current_value (security r s : ℕ) (inputs : Vector ℕ r) (centers : Vector ℕ s)
    (kernel : Vector (Fin (colors security)) r → Vector (Fin (colors security)) s → RationalResult)
    (hi : ∀ index, inputs.get index<colors security) (hb : ∀ index, centers.get index<colors security) :
    (current security r s inputs centers kernel).data.decode=
      (kernel (Vector.ofFn (fun index => ⟨inputs.get index,hi index⟩))
        (Vector.ofFn (fun index => ⟨centers.get index,hb index⟩))).data.decode := by
  simp only [current,convert_value security _ rfl inputs hi,convert_value security _ rfl centers hb]

theorem convert_work {count : ℕ} (security : ℕ) (modulus : ℕ) (hmodulus : modulus=colors security)
    (input : Vector ℕ count) (hi : ∀ index, input.get index<colors security) (limit : ℕ) (hq : modulus ≤ limit) :
    (convert security modulus hmodulus input).work ≤ count*(3*count+6*limit+9)+2 := by
  apply storeData_work
  intro index
  have hv := readVector_work 0 input index
  have hc := lessCounter_work (readVector 0 input index).value modulus
  have hx : (readVector 0 input index).value ≤ limit := by
    rw [readVector_value]; exact (hi index).le.trans (by rw [← hmodulus]; exact hq)
  unfold entry
  dsimp only
  split <;> dsimp only <;> omega

noncomputable section
noncomputable def workPolynomial (order : ℕ) (kernelWork : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+
    2*Polynomial.C order*(Polynomial.C (3*order)+6*BinaryFirstInverseProgram.colorsPolynomial+9)+kernelWork+8

theorem current_bounds (security order : ℕ) (kernelBits kernelWork : Polynomial ℕ) (arity : TruncatedArity order)
    (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (kernel : Vector (Fin (colors security)) arity.val.1.val → Vector (Fin (colors security)) arity.val.2.val → RationalResult)
    (hi : ∀ index, inputs.get index<colors security) (hb : ∀ index, centers.get index<colors security)
    (hh : ∀ inputs centers, HeightBound (kernel inputs centers).data.decode (kernelBits.eval security))
    (hw : ∀ inputs centers, (kernel inputs centers).work ≤ kernelWork.eval security) :
    HeightBound (current security _ _ inputs centers kernel).data.decode (kernelBits.eval security) ∧
    (current security _ _ inputs centers kernel).work ≤ (workPolynomial order kernelWork).eval security := by
  let modulus := PublicParameterProgram.modulus security
  let primary := convert security modulus.count rfl inputs
  let body := convert security modulus.count rfl centers
  have wq := PublicParameterProgram.modulus_work security
  have hq := BinaryFirstInverseProgram.colors_bound security
  have wp := convert_work security modulus.count rfl inputs hi _ hq
  have wb := convert_work security modulus.count rfl centers hb _ hq
  have wk := hw primary.value body.value
  have hd := arity.property
  have wp' : primary.work ≤ order*(3*order+6*BinaryFirstInverseProgram.colorsPolynomial.eval security+9)+2 :=
    wp.trans (by gcongr <;> omega)
  have wb' : body.work ≤ order*(3*order+6*BinaryFirstInverseProgram.colorsPolynomial.eval security+9)+2 :=
    wb.trans (by gcongr <;> omega)
  refine ⟨hh primary.value body.value,?_⟩
  change modulus.work+primary.work+body.work+(kernel primary.value body.value).work+4 ≤ _
  change modulus.work ≤ _ at wq
  simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_ofNat,
    PublicParameterProgram.workPolynomial_eval]
  calc
    _ ≤ PublicParameterProgram.workBound security+
        (order*(3*order+6*BinaryFirstInverseProgram.colorsPolynomial.eval security+9)+2)+
        (order*(3*order+6*BinaryFirstInverseProgram.colorsPolynomial.eval security+9)+2)+kernelWork.eval security+4 := by omega
    _ = _ := by ring

end
end CurrentAFT.BinaryCoefficientInput
