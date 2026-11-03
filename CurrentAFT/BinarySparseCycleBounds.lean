import CurrentAFT.BinarySparseCycleTermResources
import CurrentAFT.BinaryPackedRootSum

/-! Uniform summand and loop budgets for bounded-order sparse cycle evaluation.
The dynamic touched-edge count is at most twice the selected-root order. -/
namespace CurrentAFT.BinarySparseCycleBounds
open AFT GaussianSource RationalNumerics BinaryArithmetic RationalRejectionProgram
open BinaryTouchedCycle BinaryTouchedCycleBuffer BinaryTouchedCycleRanks
open BinarySparseCycleEvaluation
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

 theorem termHeight_mono {edges larger gh gh' th th' : ℕ} (he : edges ≤ larger) (hg : gh ≤ gh') (ht : th ≤ th') :
    BinarySparseCycleTermResources.termHeight edges gh th ≤ BinarySparseCycleTermResources.termHeight larger gh' th' := by
  unfold BinarySparseCycleTermResources.termHeight
  gcongr

 theorem termWork_mono {edges larger count limit cutoff upper gh gh' th th' tw tw' : ℕ}
    (he : edges ≤ larger) (hc : count ≤ limit) (hcut : cutoff ≤ upper) (hg : gh ≤ gh') (ht : th ≤ th') (hw : tw ≤ tw') :
    BinarySparseCycleTermResources.termWork edges count cutoff gh th tw ≤
      BinarySparseCycleTermResources.termWork larger limit upper gh' th' tw' := by
  unfold BinarySparseCycleTermResources.termWork BinarySparseCycleTermResources.rootsWork
    BinarySparseCycleTermResources.rootEntryWork BinarySparseCycleTermResources.weightEntryWork
    BinarySparseCycleTermResources.termHeight BinaryFiniteProduct.work RationalBits.primitiveWorkBound
  gcongr

 theorem prepareWork_mono {body larger count limit : ℕ} (hb : body ≤ larger) (hc : count ≤ limit) :
    prepareWork body count ≤ prepareWork larger limit := by
  unfold prepareWork
  gcongr

 theorem positionsWork_mono {body larger count limit : ℕ} (hb : body ≤ larger) (hc : count ≤ limit) :
    positionsWork body count ≤ positionsWork larger limit := by
  unfold positionsWork bufferWork prepareWork
  gcongr


def heightLimit (security bits limit cutoff testHeight : ℕ) : ℕ :=
  ∑ edges ∈ Finset.range (2*limit+1), BinaryTupleSum.height (2*cutoff+1) edges
    (BinarySparseCycleTermResources.termHeight (2*limit) (BinaryGaussianAverage.gaussianHeight security bits) testHeight)


def workLimit (security bits body limit cutoff testHeight testWork : ℕ) : ℕ :=
  prepareWork body limit+2*limit+positionsWork body limit+CurrentGaussianBits.tableWork security bits+
    (∑ edges ∈ Finset.range (2*limit+1), BinaryTupleSum.work (2*cutoff+1) edges
      (BinarySparseCycleTermResources.termHeight (2*limit) (BinaryGaussianAverage.gaussianHeight security bits) testHeight)
      (BinarySparseCycleTermResources.termWork (2*limit) limit cutoff (BinaryGaussianAverage.gaussianHeight security bits) testHeight testWork))+5

 theorem current_bounds {body count : ℕ} (security cutoff bits limit upper th tw : ℕ) (hb : 0 < body)
    (sites : Vector (Fin body) count) (hcount : count ≤ limit) (hcutoff : cutoff ≤ (security+2)^2)
    (hupper : cutoff ≤ upper) (test : Vector IntegerBits count → RationalResult)
    (htest : ∀ roots, (∀ slot, (roots.get slot).digits.length ≤ 2*cutoff+2) →
      HeightBound (test roots).data.decode th ∧ (test roots).work ≤ tw) :
    HeightBound (current security cutoff bits hb sites test).data.decode (heightLimit security bits limit upper th) ∧
      (current security cutoff bits hb sites test).work ≤ workLimit security bits body limit upper th tw := by
  let edges := (prepare hb sites).value.length
  let weights := CurrentGaussianBits.table security cutoff bits
  let ranks := positions hb sites
  let gh := BinaryGaussianAverage.gaussianHeight security bits
  let H := BinarySparseCycleTermResources.termHeight (2*limit) gh th
  let W := BinarySparseCycleTermResources.termWork (2*limit) limit upper gh th tw
  have he : edges ≤ 2*limit := (prepare_length hb sites).trans (Nat.mul_le_mul_left 2 hcount)
  have hs (word : Vector (Fin (2*cutoff+1)) edges) :=
    BinarySparseCycleTermResources.term_bounds weights.data ranks.value test gh th tw
      (CurrentGaussianBits.table_height security cutoff bits hcutoff) htest word
  have hh (word : Vector (Fin (2*cutoff+1)) edges) :
      HeightBound (term weights.data ranks.value test word).data.decode H :=
    (hs word).1.mono (termHeight_mono he le_rfl le_rfl)
  have hw (word : Vector (Fin (2*cutoff+1)) edges) :
      (term weights.data ranks.value test word).work ≤ W :=
    (hs word).2.trans (termWork_mono he hcount hupper le_rfl le_rfl le_rfl)
  have hsum := BinaryTupleSum.current_bounds (2*cutoff+1) edges _ H W hh hw
  have hp : 2*cutoff+1 ≤ 2*upper+1 := by omega
  have hsh := hsum.1.mono (BinaryPackedRootSum.height_mono hp le_rfl)
  have hsw := hsum.2.trans (BinaryPackedRootSum.work_mono hp le_rfl le_rfl)
  have hheight : BinaryTupleSum.height (2*upper+1) edges H ≤ heightLimit security bits limit upper th := by
    unfold heightLimit
    exact Finset.single_le_sum (a := edges) (s := Finset.range (2*limit+1))
      (f := fun e => BinaryTupleSum.height (2*upper+1) e H) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
  have hwork : BinaryTupleSum.work (2*upper+1) edges H W ≤
      ∑ e ∈ Finset.range (2*limit+1), BinaryTupleSum.work (2*upper+1) e H W :=
    Finset.single_le_sum (a := edges) (s := Finset.range (2*limit+1))
      (f := fun e => BinaryTupleSum.work (2*upper+1) e H W) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
  have hprepare := (BinaryTouchedCycleBuffer.prepare_work hb sites).trans (prepareWork_mono le_rfl hcount)
  have hpositions := (positions_work hb sites).trans (positionsWork_mono le_rfl hcount)
  have hgaussian := CurrentGaussianBits.table_work security cutoff bits hcutoff
  refine ⟨hsh.mono hheight,?_⟩
  change (prepare hb sites).work+(prepare hb sites).value.length+(positions hb sites).work+
    (CurrentGaussianBits.table security cutoff bits).work+(BinaryTupleSum.current _ _ _).work+5 ≤ _
  unfold workLimit
  dsimp only [H,W,gh,edges,weights,ranks] at *
  omega

 theorem workLimit_mono_body {security bits body larger limit cutoff th tw : ℕ} (hb : body ≤ larger) :
    workLimit security bits body limit cutoff th tw ≤ workLimit security bits larger limit cutoff th tw := by
  have hp := prepareWork_mono (count := limit) hb le_rfl
  have hs := positionsWork_mono (count := limit) hb le_rfl
  unfold workLimit
  omega

end CurrentAFT.BinarySparseCycleBounds
