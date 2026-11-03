import AFT.BinaryPermutationTape
import AFT.BinaryChartMetadata

/-! Executed insertion permutations with both directions stored as finite arrays.
The inverse is found by an explicit scan of the generated forward rows.  All
array reads and integer comparisons are charged. No inverse oracle is used. -/
namespace CurrentAFT.CurrentPermutationDraw

open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 700000

/-- An initial-segment scan, with an arbitrary valid fallback before a hit. -/
def inverseScan {count : ℕ} (rows : Vector (Fin count) count) (target : Fin count) :
    (length : ℕ) → length ≤ count → CountedValue (Fin count)
  | 0, _ => ⟨target, 1⟩
  | length + 1, h =>
    let previous := inverseScan rows target length (by omega)
    let index : Fin count := ⟨length, by omega⟩
    let entry := readVector target rows index
    let equal := equalCounter entry.value.val target.val
    ⟨if equal.value then index else previous.value,
      previous.work + entry.work + equal.work + 3⟩

theorem inverseScan_value {count : ℕ} (rows : Vector (Fin count) count)
    (permutation : Equiv.Perm (Fin count)) (hrows : ∀ index, rows.get index = permutation index)
    (target : Fin count) (length : ℕ) (h : length ≤ count)
    (hhit : (permutation.symm target).val < length) :
    (inverseScan rows target length h).value = permutation.symm target := by
  induction length with
  | zero => omega
  | succ length ih =>
    let index : Fin count := ⟨length, by omega⟩
    have he : (equalCounter (readVector target rows index).value.val target.val).value = true ↔
        permutation index = target := by
      rw [equalCounter_value, readVector_value, hrows]
      exact ⟨fun hh => Fin.ext hh, fun hh => congrArg Fin.val hh⟩
    change (if (equalCounter (readVector target rows index).value.val target.val).value then index
      else (inverseScan rows target length _).value) = _
    by_cases hit : permutation index = target
    · rw [if_pos (he.mpr hit)]
      exact (permutation.apply_eq_iff_eq_symm_apply).mp hit
    · rw [if_neg (by simpa only [he] using hit)]
      apply ih (by omega)
      have hne : permutation.symm target ≠ index := by
        intro hi
        apply hit
        rw [← hi, permutation.apply_symm_apply]
      have hv : (permutation.symm target).val ≠ length := by
        intro hi
        exact hne (Fin.ext hi)
      omega

def inverseScanWork (count length : ℕ) : ℕ := length * (9 * count + 8) + 1

theorem inverseScan_work {count : ℕ} (rows : Vector (Fin count) count)
    (target : Fin count) (length : ℕ) (h : length ≤ count) :
    (inverseScan rows target length h).work ≤ inverseScanWork count length := by
  induction length with
  | zero => simp only [inverseScan, inverseScanWork, Nat.zero_mul, Nat.zero_add, le_refl]
  | succ length ih =>
    let index : Fin count := ⟨length, by omega⟩
    have hp := ih (by omega)
    have hr := readVector_work target rows index
    have he := equalCounter_work (readVector target rows index).value.val target.val
    have hi := (readVector target rows index).value.isLt
    have ht := target.isLt
    change (inverseScan rows target length _).work + (readVector target rows index).work +
      (equalCounter (readVector target rows index).value.val target.val).work + 3 ≤ _
    unfold inverseScanWork at hp ⊢
    nlinarith

structure CachedPermutation (count : ℕ) where
  forward : Vector (Fin count) count
  inverse : Vector (Fin count) count
  left_inv : ∀ index, inverse.get (forward.get index) = index
  right_inv : ∀ index, forward.get (inverse.get index) = index

def CachedPermutation.toEquiv {count : ℕ} (cached : CachedPermutation count) : Equiv.Perm (Fin count) where
  toFun := cached.forward.get
  invFun := cached.inverse.get
  left_inv := cached.left_inv
  right_inv := cached.right_inv

def draw (count bits : ℕ) (tape : Vector (Fin 2) (count * bits)) : CountedValue (CachedPermutation count) :=
  let forward := binaryPermutationFromTape count bits tape
  let inverse := storeData count (fun target => inverseScan forward.value target count le_rfl)
  have he (target : Fin count) : inverse.value.get target = (PermutationProgram.draw count bits tape.get).symm target := by
    rw [storeData_get]
    exact inverseScan_value forward.value (PermutationProgram.draw count bits tape.get)
      (binaryPermutationFromTape_value count bits tape) target count le_rfl (Fin.isLt _)
  ⟨⟨forward.value, inverse.value,
      fun index => by rw [he, binaryPermutationFromTape_value, Equiv.symm_apply_apply],
      fun index => by rw [he, binaryPermutationFromTape_value, Equiv.apply_symm_apply]⟩,
    forward.work + inverse.work + 3⟩

theorem draw_forward (count bits : ℕ) (tape : Vector (Fin 2) (count * bits)) (index : Fin count) :
    (draw count bits tape).value.forward.get index = PermutationProgram.draw count bits tape.get index :=
  binaryPermutationFromTape_value count bits tape index

theorem draw_equiv (count bits : ℕ) (tape : Vector (Fin 2) (count * bits)) :
    (draw count bits tape).value.toEquiv = PermutationProgram.draw count bits tape.get := by
  apply Equiv.ext
  exact draw_forward count bits tape

theorem draw_inverse (count bits : ℕ) (tape : Vector (Fin 2) (count * bits)) (index : Fin count) :
    (draw count bits tape).value.inverse.get index = (PermutationProgram.draw count bits tape.get).symm index := by
  change (draw count bits tape).value.toEquiv.symm index = _
  rw [draw_equiv]

def workBound (count bits : ℕ) : ℕ := binaryPermutationFromTapeWork count bits +
  count * (inverseScanWork count count + 2) + 5

theorem draw_work (count bits : ℕ) (tape : Vector (Fin 2) (count * bits)) :
    (draw count bits tape).work ≤ workBound count bits := by
  have hf := binaryPermutationFromTape_work count bits tape
  have hi := storeData_work count (inverseScanWork count count)
    (fun target => inverseScan (binaryPermutationFromTape count bits tape).value target count le_rfl)
    (fun target => inverseScan_work _ target count le_rfl)
  change (binaryPermutationFromTape count bits tape).work + (storeData count _).work + 3 ≤ _
  unfold workBound
  omega

noncomputable section
open scoped Classical

def law (count bits : ℕ) : FiniteDist (Equiv.Perm (Fin count)) :=
  (FiniteDist.uniform (Fin (count * bits) → Fin 2)).map
    (fun word => (draw count bits (Vector.ofFn word)).value.toEquiv)

theorem law_eq (count bits : ℕ) : law count bits = PermutationProgram.permutationLaw count bits := by
  unfold law
  simp only [draw_equiv]
  convert PermutationProgram.draw_law count bits using 1
  congr 1
  funext word
  congr 1
  funext index
  exact Vector.get_ofFn word index

theorem law_tv (count bits : ℕ) :
    FiniteDist.TVBound (law count bits) (FiniteDist.uniform (Equiv.Perm (Fin count)))
      ((count : ℝ) ^ 2 / (2 : ℝ) ^ bits) := by
  rw [law_eq]
  exact PermutationProgram.permutationLaw_tv count bits

theorem law_l1 (count bits : ℕ) :
    (∑ permutation, |(law count bits).weight permutation -
      (FiniteDist.uniform (Equiv.Perm (Fin count))).weight permutation|) ≤
      2 * (count : ℝ) ^ 2 / (2 : ℝ) ^ bits := by
  have h := law_tv count bits
  rw [FiniteDist.tvBound_iff_totalVariation_le, FiniteDist.totalVariation_eq_half_l1] at h
  calc
    _ ≤ 2 * ((count : ℝ) ^ 2 / (2 : ℝ) ^ bits) := by linarith
    _ = _ := by ring

end
end CurrentAFT.CurrentPermutationDraw
