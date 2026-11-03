import CurrentAFT.PublicBitTapes
import AFT.BinaryDataArrays
import AFT.BinaryLoopControl

/-! Counted materialization of nested finite bit buffers. Every leaf is copied
from the stored flat input by sequential reads. Product offsets and row-major
addresses are computed by the actual unary counter programs. -/
namespace CurrentAFT.BinaryPublicBitCodec
open AFT BinaryArithmetic RationalRejectionProgram PublicBitTapes
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false

structure Codec (State : Type*) where
  encoding : Encoding State
  prepare : UnaryCounterResult
  prepare_value : prepare.count = encoding.bits
  read : {total : ℕ} → Vector (Fin 2) total → (offset : ℕ) →
    offset + encoding.bits ≤ total → CountedValue State
  bound : ℕ → ℕ
  read_value : ∀ {total} (input : Vector (Fin 2) total) offset room,
    (read input offset room).value = encoding.equiv
      (fun index => input.get ⟨offset+index.val, by omega⟩)
  read_work : ∀ {total} (input : Vector (Fin 2) total) offset room,
    (read input offset room).work ≤ bound total

def copy {total : ℕ} (input : Vector (Fin 2) total) (offset count : ℕ)
    (room : offset+count≤total) : CountedValue (Vector (Fin 2) count) :=
  storeData count (fun index =>
    let address := addCounter offset index.val
    let entry := readVector 0 input ⟨address.count, by rw [addCounter_value]; omega⟩
    ⟨entry.value,address.work+entry.work+2⟩)

theorem copy_get {total} (input : Vector (Fin 2) total) offset count room (index : Fin count) :
    (copy input offset count room).value.get index = input.get ⟨offset+index.val, by omega⟩ := by
  simp only [copy,storeData_get,readVector_value,addCounter_value]

theorem copy_work {total} (input : Vector (Fin 2) total) offset count room :
    (copy input offset count room).work ≤ count*(5*total+8)+2 := by
  apply storeData_work count (5*total+6)
  intro index
  have h := readVector_work (0:Fin 2) input
    (⟨(addCounter offset index.val).count, by rw [addCounter_value]; omega⟩:Fin total)
  have ho : offset≤total := by omega
  simp only [addCounter_work]
  omega

def bits (count : ℕ) : Codec (Fin count → Fin 2) where
  encoding := PublicBitTapes.bits count
  prepare := ⟨count,1⟩
  prepare_value := rfl
  read := fun input offset room =>
    let result := copy input offset count room
    ⟨result.value.get,result.work+1⟩
  bound := fun total => count*(5*total+8)+3
  read_value := by
    intro total input offset room
    funext index
    exact copy_get input offset count room index
  read_work := by
    intro total input offset room
    have h := copy_work input offset count room
    change _+1≤_
    omega

def map {First Second : Type*} (codec : Codec First) (equiv : First ≃ Second) : Codec Second where
  encoding := ⟨codec.encoding.bits,codec.encoding.equiv.trans equiv⟩
  prepare := codec.prepare
  prepare_value := codec.prepare_value
  read := fun input offset room =>
    let result := codec.read input offset room
    ⟨equiv result.value,result.work+2⟩
  bound := fun total => codec.bound total+2
  read_value := by
    intro total input offset room
    simp only [codec.read_value,Equiv.trans_apply]
  read_work := by
    intro total input offset room
    exact Nat.add_le_add_right (codec.read_work input offset room) 2

def bitsCast (count other : ℕ) (same : count=other) : Codec (Fin other → Fin 2) :=
  map (bits count) (Equiv.arrowCongr (finCongr same) (Equiv.refl _))

theorem bitsCast_encoding (count other : ℕ) (same : count=other) :
    (bitsCast count other same).encoding = PublicBitTapes.bits other := by
  subst other
  rfl

def flag : Codec Bool := map (bits 1)
  { toFun := fun word => finTwoEquiv (word 0)
    invFun := fun value _ => finTwoEquiv.symm value
    left_inv := by intro word; funext index; have h : index=0 := Subsingleton.elim _ _; subst index; simp
    right_inv := fun _ => finTwoEquiv.apply_symm_apply _ }

theorem flag_encoding : flag.encoding = PublicBitTapes.flag := rfl

def prod {First Second : Type*} (first : Codec First) (second : Codec Second) : Codec (First×Second) where
  encoding := first.encoding.prod second.encoding
  prepare :=
    let left := first.prepare
    let right := second.prepare
    let result := addCounter left.count right.count
    ⟨result.count,left.work+right.work+result.work+2⟩
  prepare_value := by simp only [addCounter_value,first.prepare_value,second.prepare_value,Encoding.prod]
  read := fun input offset room =>
    let address := addCounter offset first.encoding.bits
    let left := first.read input offset (by change offset+(first.encoding.bits+second.encoding.bits)≤_ at room; omega)
    let right := second.read input address.count (by rw [addCounter_value]; change offset+(first.encoding.bits+second.encoding.bits)≤_ at room; omega)
    ⟨(left.value,right.value),address.work+left.work+right.work+3⟩
  bound := fun total => first.bound total+second.bound total+2*total+4
  read_value := by
    intro total input offset room
    simp only [first.read_value,second.read_value,addCounter_value,Encoding.prod,
      Equiv.trans_apply,Equiv.prodCongr_apply,PublicBitTapes.split,Equiv.coe_fn_mk]
    congr 1
    apply congrArg
    funext index
    congr 1
    apply Fin.ext
    simp only [finSumFinEquiv_apply_right, Fin.val_natAdd]
    omega
  read_work := by
    intro total input offset room
    have hl := first.read_work input offset (by change offset+(first.encoding.bits+second.encoding.bits)≤_ at room; omega)
    have hr := second.read_work input (addCounter offset first.encoding.bits).count (by rw [addCounter_value]; change offset+(first.encoding.bits+second.encoding.bits)≤_ at room; omega)
    have ho : offset≤total := by change offset+(first.encoding.bits+second.encoding.bits)≤_ at room; omega
    change (addCounter offset first.encoding.bits).work+_+_+3≤_
    rw [addCounter_work]
    omega

def indexed {Index State : Type*} {count : ℕ} (ordering : Fin count ≃ Index)
    (codec : Codec State) : Codec (Index → State) where
  encoding := codec.encoding.indexed ordering
  prepare :=
    let inner := codec.prepare
    let result := multiplyCounter count inner.count
    ⟨result.count,inner.work+result.work+2⟩
  prepare_value := by simp only [multiplyCounter_value,codec.prepare_value,Encoding.indexed]
  read := fun {total} input offset room =>
    let stored := storeData count (fun row =>
      let product := multiplyCounter row.val codec.encoding.bits
      let address := addCounter offset product.count
      let result := codec.read input address.count (by
        rw [addCounter_value,multiplyCounter_value]
        change offset+count*codec.encoding.bits≤total at room
        have hm := Nat.mul_le_mul_right codec.encoding.bits (show row.val+1≤count by omega)
        nlinarith)
      ⟨result.value,product.work+address.work+result.work+3⟩)
    ⟨fun index => stored.value.get (ordering.symm index),stored.work+1⟩
  bound := fun total =>
    count*(count*(2*codec.encoding.bits+3)+1+(2*total+1)+codec.bound total+5)+3
  read_value := by
    intro total input offset room
    funext index
    simp only [storeData_get,codec.read_value,addCounter_value,multiplyCounter_value,
      Encoding.indexed,Equiv.trans_apply,Equiv.arrowCongr_apply,
      AFT.FiniteConditionProgram.groupBits,Equiv.coe_fn_mk]
    apply congrArg
    funext bit
    congr 1
    apply Fin.ext
    simp only [finProdFinEquiv, Equiv.coe_fn_mk]
    ring
  read_work := by
    intro total input offset room
    have hs := storeData_work count
      (count*(2*codec.encoding.bits+3)+1+(2*total+1)+codec.bound total+3)
      (fun row =>
        let product := multiplyCounter row.val codec.encoding.bits
        let address := addCounter offset product.count
        let result := codec.read input address.count (by
          rw [addCounter_value,multiplyCounter_value]
          change offset+count*codec.encoding.bits≤total at room
          have hm := Nat.mul_le_mul_right codec.encoding.bits (show row.val+1≤count by omega)
          nlinarith)
        (⟨result.value,product.work+address.work+result.work+3⟩:CountedValue State)) (by
        intro row
        have hh := codec.read_work input (addCounter offset (multiplyCounter row.val codec.encoding.bits).count).count (by
          rw [addCounter_value,multiplyCounter_value]
          change offset+count*codec.encoding.bits≤total at room
          have hm := Nat.mul_le_mul_right codec.encoding.bits (show row.val+1≤count by omega)
          nlinarith)
        have hm := Nat.mul_le_mul_right (2*codec.encoding.bits+3) (show row.val≤count by omega)
        have ho : offset≤total := by change offset+count*codec.encoding.bits≤total at room; omega
        simp only [multiplyCounter_work,addCounter_work]
        omega)
    change _+1≤_
    have heq : count*(count*(2*codec.encoding.bits+3)+1+(2*total+1)+codec.bound total+3+2) =
        count*(count*(2*codec.encoding.bits+3)+1+(2*total+1)+codec.bound total+5) := by ring
    rw [heq] at hs
    omega

/-- Read the input tape once into an actual stored flat buffer, then build all
nested output buffers with the counted codec. -/
def decode {State : Type*} (codec : Codec State)
    (word : Fin codec.encoding.bits → Fin 2) : CountedValue State :=
  let preparation := codec.prepare
  let input := storeData preparation.count
    (fun index => ⟨word (Fin.cast codec.prepare_value index),1⟩)
  let stored := input.value.cast codec.prepare_value
  let result := codec.read stored 0 (by omega)
  ⟨result.value,preparation.work+input.work+result.work+2⟩

def decodeBound {State : Type*} (codec : Codec State) : ℕ :=
  codec.prepare.work+3*codec.encoding.bits+codec.bound codec.encoding.bits+4

theorem decode_value {State : Type*} (codec : Codec State)
    (word : Fin codec.encoding.bits → Fin 2) :
    (decode codec word).value = codec.encoding.equiv word := by
  simp only [decode,codec.read_value,Vector.get_cast,storeData_get,Nat.zero_add]
  apply congrArg
  funext index
  congr 1

theorem decode_work {State : Type*} (codec : Codec State)
    (word : Fin codec.encoding.bits → Fin 2) :
    (decode codec word).work ≤ decodeBound codec := by
  let input := storeData codec.prepare.count
    (fun index => (⟨word (Fin.cast codec.prepare_value index),1⟩:CountedValue (Fin 2)))
  have hi := storeData_work codec.prepare.count 1
    (fun index => (⟨word (Fin.cast codec.prepare_value index),1⟩:CountedValue (Fin 2))) (fun _ => le_rfl)
  have hr := codec.read_work (input.value.cast codec.prepare_value) 0 (by omega)
  change codec.prepare.work+input.work+_+2≤_
  change input.work≤_ at hi
  have hi' : input.work≤codec.encoding.bits*3+2 := calc
    input.work≤codec.prepare.count*(1+2)+2 := hi
    _=codec.encoding.bits*3+2 := by rw [codec.prepare_value]
  unfold decodeBound
  dsimp only [input] at hr hi' ⊢
  omega

/-- Type casts only identify the native computed lengths with their specified
lengths. They do not evaluate a separate semantic parameter search. -/
def decodeAs {State : Type*} (codec : Codec State) (target : Encoding State)
    (same : codec.encoding=target) (word : Fin target.bits → Fin 2) : CountedValue State :=
  decode codec (fun index => word (Fin.cast (congrArg Encoding.bits same) index))

theorem decodeAs_value {State : Type*} (codec : Codec State) (target : Encoding State)
    (same : codec.encoding=target) (word : Fin target.bits → Fin 2) :
    (decodeAs codec target same word).value = target.equiv word := by
  subst target
  exact decode_value codec word

theorem decodeAs_work {State : Type*} (codec : Codec State) (target : Encoding State)
    (same : codec.encoding=target) (word : Fin target.bits → Fin 2) :
    (decodeAs codec target same word).work ≤ decodeBound codec :=
  decode_work codec _

end CurrentAFT.BinaryPublicBitCodec
