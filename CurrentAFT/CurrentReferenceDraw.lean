import CurrentAFT.BinaryReferenceTables
import CurrentAFT.CurrentProbabilityArrayDraw
import CurrentAFT.CurrentSafePaletteIndex
import AFT.UnaryPolynomialCounters

/-! Certified primary/body sampling arrays prepared from the same executed
reference cache used by the weight evaluator. The center array is explicitly
restricted to native interval coordinates, so ticket rounding always returns a
safe control, even for tapes assigned to the first bucket. -/
namespace CurrentAFT.CurrentReferenceDraw

open AFT AFT.BinaryArithmetic AFT.BinaryArithmetic.RationalBits AFT.RationalRejectionProgram
open CurrentProbabilityArrayDraw
open scoped BigOperators
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryReferenceTables.current
noncomputable local instance safeFintype (security : ℕ) : Fintype (ActualControls.SafePalette security) := by
  classical
  exact Subtype.fintype _

structure Counts where
  colors : ℕ
  margin : ℕ
  safe : ℕ
  work : ℕ

def counts (security : ℕ) : Counts :=
  let colors := PublicParameterProgram.modulus security
  let window := BinaryActivationProgram.cutoff security
  let square := addCounter window.count 1
  let margin := multiplyCounter 3 square.count
  let double := doubleCounter margin.count
  let safe := subtractCounter colors.count double.count
  ⟨colors.count, margin.count, safe.count,
    colors.work + window.work + square.work + margin.work + double.work + safe.work + 6⟩

theorem counts_values (security : ℕ) :
    (counts security).colors = Parameters.modulus security ∧
    (counts security).margin = Parameters.safeMargin security ∧
    (counts security).safe = CurrentSafePaletteIndex.count security := by
  have hm : (multiplyCounter 3 (addCounter (BinaryActivationProgram.cutoff security).count 1).count).count =
      Parameters.safeMargin security := by
    rw [BinaryBodyProgram.margin_value]
    rfl
  exact ⟨PublicParameterProgram.modulus_value security, hm, by
    simp only [counts, subtractCounter_value, doubleCounter_value, hm,
      PublicParameterProgram.modulus_value]⟩

theorem colors_positive (security : ℕ) : 0 < (PublicParameterProgram.modulus security).count := by
  rw [PublicParameterProgram.modulus_value]
  exact (Parameters.modulus_spec security).2.pos

theorem safe_positive (security : ℕ) : 0 < (counts security).safe := by
  rw [(counts_values security).2.2]
  exact CurrentSafePaletteIndex.count_positive security

def primaryEquiv (security : ℕ) : Fin (PublicParameterProgram.modulus security).count ≃ FirstHistogram.Palette security :=
  finCongr (PublicParameterProgram.modulus_value security)

def bodyEquiv (security : ℕ) : Fin (counts security).safe ≃ ActualControls.SafePalette security :=
  (finCongr (counts_values security).2.2).trans (CurrentSafePaletteIndex.equiv security)

@[simp] theorem bodyEquiv_value (security : ℕ) (index : Fin (counts security).safe) :
    (bodyEquiv security index).val.val = (counts security).margin + index.val := by
  rw [(counts_values security).2.1]
  rfl

def centerData (security : ℕ) (input : BinaryReferenceTables.Result security) :
    CountedValue (Vector RationalBits (counts security).safe) :=
  storeData (counts security).safe (fun index =>
    let added := addCounter (counts security).margin index.val
    have hi : added.count < (PublicParameterProgram.modulus security).count := by
      rw [addCounter_value, ← bodyEquiv_value, PublicParameterProgram.modulus_value]
      exact (bodyEquiv security index).val.isLt
    let entry := readVector zero input.center ⟨added.count, hi⟩
    ⟨entry.value, added.work + entry.work + 2⟩)

theorem centerData_get (security : ℕ) (input : BinaryReferenceTables.Result security)
    (index : Fin (counts security).safe) :
    (centerData security input).value.get index = input.center.get
      ((primaryEquiv security).symm (bodyEquiv security index).val) := by
  simp only [centerData, storeData_get, readVector_value]
  congr 1
  apply Fin.ext
  change (addCounter (counts security).margin index.val).count = (bodyEquiv security index).val.val
  rw [addCounter_value, bodyEquiv_value]

def centerDataWork (security : ℕ) : ℕ :=
  (counts security).safe * (2 * (counts security).margin +
    3 * (PublicParameterProgram.modulus security).count + 8) + 2

theorem centerData_work (security : ℕ) (input : BinaryReferenceTables.Result security) :
    (centerData security input).work ≤ centerDataWork security := by
  apply storeData_work
  intro index
  have hr := readVector_work zero input.center
    (⟨(addCounter (counts security).margin index.val).count, by
      rw [addCounter_value, ← bodyEquiv_value, PublicParameterProgram.modulus_value]
      exact (bodyEquiv security index).val.isLt⟩ : Fin (PublicParameterProgram.modulus security).count)
  simp only [addCounter_work]
  omega

structure Cache (security bits : ℕ) where
  primary : ProbabilityArray (PublicParameterProgram.modulus security).count
  body : ProbabilityArray (counts security).safe
  activation : RationalBits
  primary_value : ∀ index, (primary.data.get index).decode = RationalProposalProgram.primary security bits index.val
  body_value : ∀ index, (body.data.get index).decode = RationalProposalProgram.center security bits (bodyEquiv security index).val.val
  activation_value : activation.decode = LocalPairProgram.activationApprox security bits

private theorem body_mass (security bits : ℕ) :
    (∑ color : ActualControls.SafePalette security, RationalProposalProgram.center security bits color.val.val) = 1 := by
  have h := (RationalProposalProgram.approximateBodyReference security bits).sum_one
  change (∑ color : ActualControls.SafePalette security,
    (RationalProposalProgram.center security bits color.val.val : ℝ)) = 1 at h
  exact_mod_cast h

/-- Only the safe restriction is generated here; the already generated q by q
reference cache is reused without regenerating any Gaussian or anchor table. -/
def prepare (security bits : ℕ) (input : BinaryReferenceTables.Result security)
    (hinput : input = BinaryReferenceTables.current security bits) : CountedValue (Cache security bits) :=
  let center := centerData security input
  have hp (index) : (input.primary.get index).decode = RationalProposalProgram.primary security bits index.val := by
    rw [hinput]
    exact BinaryReferenceTables.primary_value security bits index
  have hb (index) : (center.value.get index).decode = RationalProposalProgram.center security bits (bodyEquiv security index).val.val := by
    rw [centerData_get, hinput, BinaryReferenceTables.center_value]
    rfl
  have hpn (index) : 0 ≤ (input.primary.get index).decode := by
    rw [hp]
    have h := (RationalProposalProgram.approximatePrimaryLaw security bits).nonneg (primaryEquiv security index)
    change (0 : ℝ) ≤ (RationalProposalProgram.primary security bits index.val : ℝ) at h
    exact_mod_cast h
  have hpm : (∑ index, (input.primary.get index).decode) = 1 := by
    simp_rw [hp]
    exact (Equiv.sum_comp (primaryEquiv security)
      (fun color => RationalProposalProgram.primary security bits color.val)).trans
      (RationalProposalProgram.primary_mass security bits)
  have hbn (index) : 0 ≤ (center.value.get index).decode := by
    rw [hb]
    exact RationalProposalProgram.center_nonneg security bits (bodyEquiv security index).val
  have hbm : (∑ index, (center.value.get index).decode) = 1 := by
    simp_rw [hb]
    exact (Equiv.sum_comp (bodyEquiv security)
      (fun color => RationalProposalProgram.center security bits color.val.val)).trans (body_mass security bits)
  ⟨⟨⟨input.primary, hpn, hpm⟩, ⟨center.value, hbn, hbm⟩, input.activation, hp, hb, by
      rw [hinput]; exact BinaryReferenceTables.activation_value security bits⟩,
    (counts security).work + center.work + 3⟩

@[simp] theorem prepare_primary (security bits : ℕ) (input : BinaryReferenceTables.Result security)
    (hinput : input = BinaryReferenceTables.current security bits) :
    (prepare security bits input hinput).value.primary.data = input.primary := rfl

@[simp] theorem prepare_body (security bits : ℕ) (input : BinaryReferenceTables.Result security)
    (hinput : input = BinaryReferenceTables.current security bits) :
    (prepare security bits input hinput).value.body.data = (centerData security input).value := rfl


def primaryDraw (security tableBits drawBits : ℕ) (cache : Cache security tableBits)
    (word : Fin (drawBits + (PublicParameterProgram.modulus security).count + 1) → Fin 2) :
    CountedValue (FirstHistogram.Palette security) :=
  let selected := positiveDraw _ (colors_positive security) cache.primary drawBits word
  ⟨primaryEquiv security selected.value, (PublicParameterProgram.modulus security).work + selected.work + 1⟩

def bodyDraw (security tableBits drawBits : ℕ) (cache : Cache security tableBits)
    (word : Fin (drawBits + (counts security).safe + 1) → Fin 2) :
    CountedValue (ActualControls.SafePalette security) :=
  let selected := positiveDraw _ (safe_positive security) cache.body drawBits word
  let added := addCounter (counts security).margin selected.value.val
  have he : added.count = (bodyEquiv security selected.value).val.val := by
    rw [addCounter_value, bodyEquiv_value]
  ⟨⟨⟨added.count, by rw [he]; exact (bodyEquiv security selected.value).val.isLt⟩, by
      simpa only [he] using (bodyEquiv security selected.value).property⟩,
    (counts security).work + selected.work + added.work + 2⟩

theorem primaryDraw_value (security tableBits drawBits : ℕ) (cache : Cache security tableBits)
    (word : Fin (drawBits + (PublicParameterProgram.modulus security).count + 1) → Fin 2) :
    (primaryDraw security tableBits drawBits cache word).value =
      primaryEquiv security (positiveDraw _ (colors_positive security) cache.primary drawBits word).value := rfl

theorem bodyDraw_value (security tableBits drawBits : ℕ) (cache : Cache security tableBits)
    (word : Fin (drawBits + (counts security).safe + 1) → Fin 2) :
    (bodyDraw security tableBits drawBits cache word).value =
      bodyEquiv security (positiveDraw _ (safe_positive security) cache.body drawBits word).value := by
  apply Subtype.ext
  apply Fin.ext
  change (addCounter (counts security).margin _).count = _
  rw [addCounter_value, bodyEquiv_value]

theorem primaryDraw_work (security tableBits drawBits height : ℕ) (cache : Cache security tableBits)
    (hh : ∀ index, AFT.RationalNumerics.HeightBound (cache.primary.data.get index).decode height)
    (word : Fin (drawBits + (PublicParameterProgram.modulus security).count + 1) → Fin 2) :
    (primaryDraw security tableBits drawBits cache word).work ≤
      (PublicParameterProgram.modulus security).work + workBound (PublicParameterProgram.modulus security).count height drawBits + 1 := by
  exact Nat.add_le_add_right (Nat.add_le_add_left (positiveDraw_work _ (colors_positive security) _ _ _ hh word) _) 1

theorem bodyDraw_work (security tableBits drawBits height : ℕ) (cache : Cache security tableBits)
    (hh : ∀ index, AFT.RationalNumerics.HeightBound (cache.body.data.get index).decode height)
    (word : Fin (drawBits + (counts security).safe + 1) → Fin 2) :
    (bodyDraw security tableBits drawBits cache word).work ≤
      (counts security).work + workBound (counts security).safe height drawBits + 2 * (counts security).margin + 3 := by
  have h := positiveDraw_work _ (safe_positive security) cache.body height drawBits hh word
  simp only [bodyDraw, addCounter_work]
  omega

noncomputable section
open scoped Classical

theorem primary_law (security bits : ℕ) (cache : Cache security bits) :
    (law cache.primary).map (primaryEquiv security) = RationalProposalProgram.approximatePrimaryLaw security bits := by
  ext color
  rw [FiniteDist.map_equiv_weight]
  change ((cache.primary.data.get ((primaryEquiv security).symm color)).decode : ℝ) = _
  rw [cache.primary_value]
  rfl

theorem body_law (security bits : ℕ) (cache : Cache security bits) :
    (law cache.body).map (bodyEquiv security) = RationalProposalProgram.approximateBodyReference security bits := by
  ext color
  rw [FiniteDist.map_equiv_weight]
  change ((cache.body.data.get ((bodyEquiv security).symm color)).decode : ℝ) = _
  rw [cache.body_value, Equiv.apply_symm_apply]
  rfl


def primaryDrawLaw (security tableBits drawBits : ℕ) (cache : Cache security tableBits) :
    FiniteDist (FirstHistogram.Palette security) :=
  (FiniteDist.uniform (Fin (drawBits + (PublicParameterProgram.modulus security).count + 1) → Fin 2)).map
    (fun word => (primaryDraw security tableBits drawBits cache word).value)

def bodyDrawLaw (security tableBits drawBits : ℕ) (cache : Cache security tableBits) :
    FiniteDist (ActualControls.SafePalette security) :=
  (FiniteDist.uniform (Fin (drawBits + (counts security).safe + 1) → Fin 2)).map
    (fun word => (bodyDraw security tableBits drawBits cache word).value)

theorem primaryDraw_rounding (security tableBits drawBits : ℕ) (cache : Cache security tableBits) :
    (∑ color, |(primaryDrawLaw security tableBits drawBits cache).weight color -
      (RationalProposalProgram.approximatePrimaryLaw security tableBits).weight color|) ≤ 1 / (2 : ℝ) ^ drawBits := by
  have h := FiniteDist.l1_map_le
    ((FiniteDist.uniform (Fin (drawBits + (PublicParameterProgram.modulus security).count + 1) → Fin 2)).map
      (fun word => (positiveDraw _ (colors_positive security) cache.primary drawBits word).value))
    (law cache.primary) (primaryEquiv security)
  rw [primary_law] at h
  simp only [FiniteDist.map_map] at h
  exact h.trans (positiveDraw_l1 _ (colors_positive security) cache.primary drawBits)

theorem bodyDraw_rounding (security tableBits drawBits : ℕ) (cache : Cache security tableBits) :
    (∑ color, |(bodyDrawLaw security tableBits drawBits cache).weight color -
      (RationalProposalProgram.approximateBodyReference security tableBits).weight color|) ≤ 1 / (2 : ℝ) ^ drawBits := by
  have h := FiniteDist.l1_map_le
    ((FiniteDist.uniform (Fin (drawBits + (counts security).safe + 1) → Fin 2)).map
      (fun word => (positiveDraw _ (safe_positive security) cache.body drawBits word).value))
    (law cache.body) (bodyEquiv security)
  rw [body_law] at h
  simp only [FiniteDist.map_map] at h
  have he : bodyDrawLaw security tableBits drawBits cache =
      ((FiniteDist.uniform (Fin (drawBits + (counts security).safe + 1) → Fin 2)).map
        (fun word => bodyEquiv security (positiveDraw _ (safe_positive security) cache.body drawBits word).value)) := by
    simp only [bodyDrawLaw, bodyDraw_value]
  rw [he]
  exact h.trans (positiveDraw_l1 _ (safe_positive security) cache.body drawBits)

end
end CurrentAFT.CurrentReferenceDraw
