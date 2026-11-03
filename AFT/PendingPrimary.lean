import AFT.IndependentJointTable
import AFT.FiniteSeedOutput

/-! # A distinguished old primary with every other input retained literally -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
local instance pendingSplitFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {Color : Type*} [Fintype Color]

def primarySplitEquiv {Primary : Type*} (point : Primary) : Unit ⊕ {other : Primary // other ≠ point} ≃ Primary where
  toFun := Sum.elim (fun _ => point) Subtype.val
  invFun other := if h : other=point then Sum.inl () else Sum.inr ⟨other,h⟩
  left_inv input := by
    cases input with
    | inl token => cases token; simp
    | inr other => simp [other.property]
  right_inv other := by by_cases h : other=point <;> simp [h]

def splitPrimaryIndex (seed : InputSeed Color) (point : Fin seed.primaryOrder) :
    Unit ⊕ ({other : Fin seed.primaryOrder // other ≠ point} ⊕ Fin seed.bodyOrder) ≃
      Fin (seed.primaryOrder+seed.bodyOrder) :=
  (Equiv.sumAssoc Unit {other : Fin seed.primaryOrder // other ≠ point} (Fin seed.bodyOrder)).symm |>.trans
    ((Equiv.sumCongr (primarySplitEquiv point) (Equiv.refl (Fin seed.bodyOrder))).trans finSumFinEquiv)

def splitPrimaryKernel (seed : InputSeed Color) (point : Fin seed.primaryOrder)
    (color : Color) (rest : {other : Fin seed.primaryOrder // other ≠ point} ⊕ Fin seed.bodyOrder → Color) : ℝ :=
  seed.kernel (fun index => Sum.elim (fun _ : Unit => color) rest ((splitPrimaryIndex seed point).symm index))

omit [Fintype Color] in
theorem splitPrimaryKernel_join (seed : InputSeed Color) (point : Fin seed.primaryOrder) :
    MixedKernel.singletonJoin (splitPrimaryKernel seed point) =
      fun word => seed.kernel (word ∘ (splitPrimaryIndex seed point).symm) := by
  funext word
  unfold MixedKernel.singletonJoin splitPrimaryKernel
  congr 1
  funext index
  simp only [Function.comp_apply]
  cases (splitPrimaryIndex seed point).symm index with
  | inl token => cases token; rfl
  | inr other => rfl

theorem splitPrimaryIndex_reference (primary body : FiniteDist Color)
    (seed : InputSeed Color) (point : Fin seed.primaryOrder) :
    (fun slot => inputReference primary body seed (splitPrimaryIndex seed point slot)) =
      Sum.elim (fun _ : Unit => primary)
        (Sum.elim (fun _ : {other : Fin seed.primaryOrder // other ≠ point} => primary) (fun _ : Fin seed.bodyOrder => body)) := by
  funext slot
  rcases slot with token|(other|other)
  · cases token; simp [splitPrimaryIndex,primarySplitEquiv,inputReference]
  · simp [splitPrimaryIndex,primarySplitEquiv,inputReference]
  · simp [splitPrimaryIndex,primarySplitEquiv,inputReference]

omit [Fintype Color] in
theorem splitPrimaryIndex_rate (primaryPool bodyPool : ℝ)
    (seed : InputSeed Color) (point : Fin seed.primaryOrder) :
    (fun slot => inputRate primaryPool bodyPool seed (splitPrimaryIndex seed point slot)) =
      Sum.elim (fun _ : Unit => (Real.sqrt primaryPool)⁻¹)
        (Sum.elim (fun _ : {other : Fin seed.primaryOrder // other ≠ point} => (Real.sqrt primaryPool)⁻¹)
          (fun _ : Fin seed.bodyOrder => (Real.sqrt bodyPool)⁻¹)) := by
  funext slot
  rcases slot with token|(other|other)
  · cases token; simp [splitPrimaryIndex,primarySplitEquiv,inputRate]
  · simp [splitPrimaryIndex,primarySplitEquiv,inputRate]
  · simp [splitPrimaryIndex,primarySplitEquiv,inputRate]

omit [Fintype Color] in
theorem splitPrimaryIndex_channel {Output : Type*} (primaryChannel bodyChannel : Color → Output → ℝ)
    (seed : InputSeed Color) (point : Fin seed.primaryOrder) :
    (fun slot => seedChannel primaryChannel bodyChannel seed (splitPrimaryIndex seed point slot)) =
      Sum.elim (fun _ : Unit => primaryChannel)
        (Sum.elim (fun _ : {other : Fin seed.primaryOrder // other ≠ point} => primaryChannel)
          (fun _ : Fin seed.bodyOrder => bodyChannel)) := by
  funext slot
  rcases slot with token|(other|other)
  · cases token; simp [splitPrimaryIndex,primarySplitEquiv,seedChannel]
  · simp [splitPrimaryIndex,primarySplitEquiv,seedChannel]
  · simp [splitPrimaryIndex,primarySplitEquiv,seedChannel]

/-- No renaming changes any mixed fiber or either original pool power. -/
theorem splitPrimaryKernel_weight (primary body : FiniteDist Color) (primaryPool bodyPool radius : ℝ)
    (seed : InputSeed Color) (point : Fin seed.primaryOrder) :
    inputWeight primary body primaryPool bodyPool radius
      (V7Calibration.independentOriginalJointSeed (splitPrimaryKernel seed point)) =
      inputWeight primary body primaryPool bodyPool radius seed := by
  rw [V7Calibration.independentOriginalJointSeed,groupedFiniteSeed_weight,Fintype.card_fin,splitPrimaryKernel_join]
  simp only [inputWeight,MixedKernel.analyticActivity]
  congr 1
  have hh := @MixedKernel.CoordinateTransport.activity_equiv _ _ _ _ _ _ (instDecidableEqFin _) _
    (splitPrimaryIndex seed point).symm
    (inputRate primaryPool bodyPool seed) (inputReference primary body seed) seed.kernel
  simpa only [Equiv.symm_symm,splitPrimaryIndex_reference,splitPrimaryIndex_rate] using hh

theorem splitPrimaryKernel_output {Output : Type*} [Fintype Output]
    (primary body : FiniteDist Color) (primaryChannel bodyChannel : Color → Output → ℝ)
    (seed : InputSeed Color) (point : Fin seed.primaryOrder) :
    seedOutput primary body primaryChannel bodyChannel
      (V7Calibration.independentOriginalJointSeed (splitPrimaryKernel seed point)) =
      seedOutput primary body primaryChannel bodyChannel seed := by
  rw [V7Calibration.independentOriginalJointSeed,groupedFiniteSeed_output,splitPrimaryKernel_join,seedOutput_indexed]
  have hh := indexedOutput_equiv (splitPrimaryIndex seed point).symm
    (inputReference primary body seed) (seedChannel primaryChannel bodyChannel seed) seed.kernel
  simpa only [Equiv.symm_symm,splitPrimaryIndex_reference,splitPrimaryIndex_channel] using hh

theorem splitPrimaryKernel_canonical (primary body : FiniteDist Color)
    (seed : InputSeed Color) (point : Fin seed.primaryOrder)
    (hc : Hoeffding.Canonical (inputReference primary body seed) Finset.univ seed.kernel) :
    Hoeffding.Canonical (Sum.elim (fun _ : Unit => primary)
      (Sum.elim (fun _ : {other : Fin seed.primaryOrder // other ≠ point} => primary)
        (fun _ : Fin seed.bodyOrder => body))) Finset.univ
      (MixedKernel.singletonJoin (splitPrimaryKernel seed point)) := by
  rw [splitPrimaryKernel_join]
  have hh := MixedKernel.CoordinateTransport.canonical_equiv (splitPrimaryIndex seed point).symm
    (inputReference primary body seed) seed.kernel hc
  simpa only [Equiv.symm_symm,splitPrimaryIndex_reference] using hh

local instance pendingSplitSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _

theorem singletonJoin_primary_mean {Rest : Type*} [Fintype Rest] [Nonempty Color]
    (primary : FiniteDist Color) (other : Rest → FiniteDist Color)
    (kernel : Color → (Rest → Color) → ℝ)
    (hc : Hoeffding.Canonical (Sum.elim (fun _ : Unit => primary) other) Finset.univ
      (MixedKernel.singletonJoin kernel)) (rest : Rest → Color) :
    (∑ color,primary.weight color*kernel color rest)=0 := by
  let old : Color := Classical.choice inferInstance
  have hh := hc.2 (Sum.inl ()) (Finset.mem_univ _) (Sum.elim (fun _ : Unit => old) rest)
  have he (color) : MixedKernel.singletonJoin kernel
      (Function.update (Sum.elim (fun _ : Unit => old) rest) (Sum.inl ()) color)=kernel color rest := by
    unfold MixedKernel.singletonJoin
    simp only [Function.update_self]
    congr 1
    funext slot
    simp only [Function.comp_apply,Function.update_of_ne (Sum.inr_ne_inl),Sum.elim_inr]
  simpa only [Sum.elim_inl,he] using hh

theorem splitPrimaryKernel_primary_mean [Nonempty Color] (primary body : FiniteDist Color)
    (seed : InputSeed Color) (point : Fin seed.primaryOrder)
    (hc : Hoeffding.Canonical (inputReference primary body seed) Finset.univ seed.kernel)
    (rest : {other : Fin seed.primaryOrder // other ≠ point} ⊕ Fin seed.bodyOrder → Color) :
    (∑ color,primary.weight color*splitPrimaryKernel seed point color rest)=0 :=
  singletonJoin_primary_mean primary _ _ (splitPrimaryKernel_canonical primary body seed point hc) rest

end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance pendingPrimaryFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

def pendingPrimaryHigherSeed (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (seed : InputSeed (Fin (Parameters.modulus n))) (point : Fin seed.primaryOrder)
    (selected : Finset (Fin 4)) : InputSeed (Fin (Parameters.modulus n)) :=
  independentJointHigherSeed C n beta operator charts (splitPrimaryKernel seed point) selected

def pendingPrimaryHigherTable (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (seed : InputSeed (Fin (Parameters.modulus n))) (point : Fin seed.primaryOrder) :
    Table (InputSeed (Fin (Parameters.modulus n))) :=
  independentJointHigherTable C n beta operator charts (splitPrimaryKernel seed point)

/-- One parameter threshold works for every literal finite input seed. -/
theorem pendingPrimaryHigherTable_activity_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n ∧
      Parameters.legs n ≤ 2*pool n ∧ pool n ≤ Parameters.legs n) :
    ∀ᶠ n in atTop,
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n →
    ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    (∀ mark first second,publicChartRaw C n mark (charts mark) (fun _ => 1) first second=
      conditionalJointOutput C n mark (fun _ => 1) first second) →
    ∀ seed : InputSeed (Fin (Parameters.modulus n)),∀ point : Fin seed.primaryOrder,
    Hoeffding.Canonical (inputReference (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) seed)
      Finset.univ seed.kernel → ∀ bodyPool radius : ℝ,0 ≤ radius →
    activity (inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (pool n) bodyPool radius)
      (pendingPrimaryHigherTable C n (beta n) operator charts seed point) ≤
      independentJointHigherConstant C/(n : ℝ)^(5/2 : ℝ)*
        inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (pool n) bodyPool radius seed := by
  filter_upwards [independentJointHigherTable_activity_uniform_eventually C hC beta pool htypical]
    with n hh operator hop charts hcharts seed point hseed bodyPool radius hradius
  have he := hh {other : Fin seed.primaryOrder // other ≠ point} (Fin seed.bodyOrder)
    operator hop charts hcharts (splitPrimaryKernel seed point)
    (splitPrimaryKernel_primary_mean _ _ seed point hseed) bodyPool radius hradius
  rw [splitPrimaryKernel_weight] at he
  exact he

end
end AFT.V7Calibration
