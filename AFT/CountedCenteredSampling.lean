import AFT.CountedGaussianArithmetic
import AFT.PermutationProgramCost

/-! # Cached rational scalar windows and an actual counted fair-bit draw -/
namespace AFT.RationalNumerics
open GaussianSource FiniteConvolutionProgram
open scoped BigOperators

structure CountedGaussianWeights (size : ℕ) where
  value : Vector ℚ size
  work : ℕ

/-- Raw weights and their normalizer are each computed once. -/
def countedCenteredWeights (squaredWidth center : ℚ) (cutoff bits : ℕ) :
    CountedGaussianWeights (2*cutoff+1) :=
  let raw := Vector.ofFn (fun i : Fin (2*cutoff+1) =>
    GaussianArithmetic.centered squaredWidth center (centeredGaussianAnchor center+windowIndexEquiv cutoff i)
      (centeredWindowPrecision cutoff bits))
  let normalizer := ∑ i,(raw.get i).value
  ⟨Vector.ofFn (fun i => (raw.get i).value/normalizer),
    (∑ i,(raw.get i).work)+2*(2*cutoff+1)⟩

theorem countedCenteredWeights_value (squaredWidth center : ℚ) (cutoff bits : ℕ) (i : Fin (2*cutoff+1)) :
    (countedCenteredWeights squaredWidth center cutoff bits).value.get i=
      centeredGaussianWeights squaredWidth center cutoff bits i := by
  simp only [countedCenteredWeights,Vector.get_ofFn,GaussianArithmetic.centered_value,
    centeredGaussianWeights,centeredWindowWeight]
  congr 1
  change (∑ i : Fin (2*cutoff+1),centeredWindowRaw squaredWidth center cutoff bits (windowIndexEquiv cutoff i))=_
  exact (windowIndexEquiv cutoff).sum_comp _

/-- The floor table, deficit and binary ticket are stored; the final scan
uses the same proved bucket routine as the public permutation program. -/
def countedCenteredIndex (squaredWidth center : ℚ) (cutoff bits : ℕ)
    (word : Fin (windowTicketBits cutoff bits) → Fin 2) : BetaReference.CountedNatural :=
  let weights := countedCenteredWeights squaredWidth center cutoff (bits+1)
  let tickets := PermutationProgram.powerTwo (windowTicketBits cutoff bits)
  let ticket := PermutationProgram.bitValue (windowTicketBits cutoff bits) word
  let floors := Vector.ofFn (fun i : Fin (2*cutoff+1) => ⌊(tickets.value : ℚ)*weights.value.get i⌋₊)
  let total := ∑ i,floors.get i
  let deficit := tickets.value-total
  let counts := List.ofFn (fun i : Fin (2*cutoff+1) => floors.get i+if i=0 then deficit else 0)
  let selected := PermutationProgram.countedBucket counts ticket.value
  ⟨selected.value,weights.work+tickets.work+ticket.work+5*(2*cutoff+1)+selected.work+1⟩

theorem countedCenteredIndex_value (squaredWidth center : ℚ) (cutoff bits : ℕ)
    (word : Fin (windowTicketBits cutoff bits) → Fin 2) :
    (countedCenteredIndex squaredWidth center cutoff bits word).value=
      ((windowIndexEquiv cutoff).symm (centeredGaussianDraw squaredWidth center cutoff bits word)).val := by
  simp only [countedCenteredIndex,countedCenteredWeights_value,Vector.get_ofFn,
    PermutationProgram.powerTwo_value,PermutationProgram.bitValue_value,PermutationProgram.countedBucket_value]
  simp only [centeredGaussianDraw,Equiv.symm_apply_apply]
  rfl

structure CountedGaussianInteger where
  value : ℤ
  work : ℕ

def countedCenteredInteger (squaredWidth center : ℚ) (cutoff bits : ℕ)
    (word : Fin (windowTicketBits cutoff bits) → Fin 2) : CountedGaussianInteger :=
  let index := countedCenteredIndex squaredWidth center cutoff bits word
  ⟨centeredGaussianAnchor center+(index.value : ℤ)-cutoff,index.work+3⟩

theorem countedCenteredInteger_value (squaredWidth center : ℚ) (cutoff bits : ℕ)
    (word : Fin (windowTicketBits cutoff bits) → Fin 2) :
    (countedCenteredInteger squaredWidth center cutoff bits word).value=
      centeredGaussianAnchor center+(centeredGaussianDraw squaredWidth center cutoff bits word : ℤ) := by
  simp only [countedCenteredInteger,countedCenteredIndex_value]
  have hh := congrArg (fun point : Window cutoff => (point : ℤ))
    ((windowIndexEquiv cutoff).apply_symm_apply (centeredGaussianDraw squaredWidth center cutoff bits word))
  change (↑((windowIndexEquiv cutoff).symm (centeredGaussianDraw squaredWidth center cutoff bits word)).val : ℤ)-cutoff=_ at hh
  dsimp only at hh
  omega

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

private theorem scalar_work_budget (budget piTerms taylorTerms scale : ℕ) (hb : 2≤budget)
    (hp : piTerms+3≤7*budget) (ht : taylorTerms≤16*budget) (hs : scale≤11*budget) :
    8*(piTerms+4)^2+taylorTerms*(2*taylorTerms+2)+scale+22≤2000*budget^2 := by
  have hp' : piTerms+4≤8*budget := by omega
  calc
    _ ≤ 8*(8*budget)^2+(16*budget)*(2*(16*budget)+2)+11*budget+22 := by gcongr
    _ ≤ _ := by nlinarith

theorem countedCenteredWeights_work (squaredWidth center : ℚ) (widthBits centerBits cutoff bits : ℕ)
    (hw : 1≤squaredWidth) :
    (countedCenteredWeights squaredWidth center cutoff bits).work≤
      (2*cutoff+1)*(2000*(centeredScalarBudget widthBits centerBits cutoff bits)^2+2) := by
  let budget := centeredScalarBudget widthBits centerBits cutoff bits
  have hb : 2≤budget := by dsimp [budget,centeredScalarBudget];omega
  have hs (point : Window cutoff) :
      (GaussianArithmetic.centered squaredWidth center (centeredGaussianAnchor center+point)
        (centeredWindowPrecision cutoff bits)).work≤2000*budget^2 := by
    have hr := centeredWindow_resources squaredWidth center widthBits centerBits cutoff bits hw point
    have hh := GaussianArithmetic.gaussian_work (centeredGaussianSquaredWidth squaredWidth center)
      (centeredGaussianNumerator center (centeredGaussianAnchor center+point)) (centeredWindowPrecision cutoff bits)
    apply le_trans (Nat.add_le_add_right hh 6)
    convert scalar_work_budget budget _ _ _ hb hr.2.1 hr.2.2.2 hr.2.2.1 using 1
  simp only [countedCenteredWeights,Vector.get_ofFn]
  have hh : (∑ i : Fin (2*cutoff+1),
      (GaussianArithmetic.centered squaredWidth center (centeredGaussianAnchor center+windowIndexEquiv cutoff i)
        (centeredWindowPrecision cutoff bits)).work)≤(2*cutoff+1)*(2000*budget^2) := by
    calc
      _ ≤ ∑ _i : Fin (2*cutoff+1),2000*budget^2 := Finset.sum_le_sum (fun i _ => hs (windowIndexEquiv cutoff i))
      _ = _ := by simp
  change _≤(2*cutoff+1)*(2000*budget^2+2)
  nlinarith

theorem countedCenteredInteger_work (squaredWidth center : ℚ) (widthBits centerBits cutoff bits : ℕ)
    (hw : 1≤squaredWidth) (word : Fin (windowTicketBits cutoff bits) → Fin 2) :
    (countedCenteredInteger squaredWidth center cutoff bits word).work≤
      (2*cutoff+1)*(2000*(centeredScalarBudget widthBits centerBits cutoff (bits+1))^2+10)+
        3*windowTicketBits cutoff bits+4 := by
  have hwts := countedCenteredWeights_work squaredWidth center widthBits centerBits cutoff (bits+1) hw
  have hbucket (counts : List ℕ) (ticket : ℕ) (hlen : counts.length=2*cutoff+1) :
      (PermutationProgram.countedBucket counts ticket).work≤3*(2*cutoff+1) := by
    simpa only [hlen] using PermutationProgram.countedBucket_work counts ticket
  simp only [countedCenteredInteger,countedCenteredIndex,PermutationProgram.powerTwo_work,
    PermutationProgram.bitValue_work]
  have hb := hbucket (List.ofFn (fun i : Fin (2*cutoff+1) =>
      (Vector.ofFn (fun j : Fin (2*cutoff+1) =>
        ⌊((PermutationProgram.powerTwo (windowTicketBits cutoff bits)).value : ℚ)*
          (countedCenteredWeights squaredWidth center cutoff (bits+1)).value.get j⌋₊)).get i+
      if i=0 then (PermutationProgram.powerTwo (windowTicketBits cutoff bits)).value-
        ∑ j,(Vector.ofFn (fun k : Fin (2*cutoff+1) =>
          ⌊((PermutationProgram.powerTwo (windowTicketBits cutoff bits)).value : ℚ)*
            (countedCenteredWeights squaredWidth center cutoff (bits+1)).value.get k⌋₊)).get j else 0))
      (PermutationProgram.bitValue (windowTicketBits cutoff bits) word).value (by simp)
  nlinarith

end
end AFT.RationalNumerics
