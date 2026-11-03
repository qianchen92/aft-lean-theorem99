import CurrentAFT.BinaryWeightProgram

/-! # Fixed-order polynomial bit work of the complete binary weight -/
namespace CurrentAFT.BinaryWeightResources
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits GradedControlAlgebra
open BinaryWeightLocal
open scoped BigOperators
set_option maxHeartbeats 2600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryWeightProgram.current

@[gcongr] theorem tupleHeight_mono {pool larger count first second : ℕ} (hp : pool ≤ larger) (hh : first ≤ second) :
    BinaryTupleSum.height pool count first ≤ BinaryTupleSum.height larger count second := by
  induction count with
  | zero => exact hh
  | succ count ih => exact Nat.mul_le_mul hp (Nat.add_le_add_right ih 1)

@[gcongr] theorem tupleWork_mono {pool larger count first second firstWork secondWork : ℕ}
    (hp : pool ≤ larger) (hh : first ≤ second) (hw : firstWork ≤ secondWork) :
    BinaryTupleSum.work pool count first firstWork ≤ BinaryTupleSum.work larger count second secondWork := by
  induction count generalizing firstWork secondWork with
  | zero => exact hw
  | succ count ih =>
    have ht := tupleHeight_mono (count := count) hp hh
    have hr := ih (Nat.add_le_add_right (Nat.add_le_add_left hw (BinaryTupleSum.prependWork count)) 1)
    simp only [BinaryTupleSum.work]
    exact Nat.add_le_add_right (Nat.mul_le_mul hp (Nat.add_le_add_right (Nat.add_le_add hr
      (primitiveWorkBound_mono (Nat.mul_le_mul (Nat.add_le_add_right hp 1) (Nat.add_le_add_right ht 1)))) 2)) 2

@[gcongr] theorem pairedHeight_mono {colors larger reference largerReference count first second : ℕ}
    (hc : colors ≤ larger) (hr : reference ≤ largerReference) (hh : first ≤ second) :
    BinaryPairedTensor.height colors reference count first ≤ BinaryPairedTensor.height larger largerReference count second := by
  induction count with
  | zero => exact hh
  | succ count ih =>
    simp only [BinaryPairedTensor.height, BinaryPairedScore.height]
    gcongr

@[gcongr] theorem pairedWork_mono {colors larger reference largerReference count first second firstWork secondWork : ℕ}
    (hc : colors ≤ larger) (hr : reference ≤ largerReference) (hh : first ≤ second) (hw : firstWork ≤ secondWork) :
    BinaryPairedTensor.work colors reference count first firstWork ≤ BinaryPairedTensor.work larger largerReference count second secondWork := by
  induction count generalizing firstWork secondWork with
  | zero => exact hw
  | succ count ih =>
    have ht := pairedHeight_mono (count := count) hc hr hh
    have hw' := ih (Nat.add_le_add_right (Nat.add_le_add_left hw (BinaryTupleSum.prependWork count)) 1)
    simp only [BinaryPairedTensor.work]
    unfold BinaryPairedScore.work BinaryPairedScore.height primitiveWorkBound
    gcongr

@[gcongr] theorem encodeWork_mono {base larger capacity largerCapacity count : ℕ}
    (hb : base ≤ larger) (hc : capacity ≤ largerCapacity) :
    BinaryWeightCoordinates.encodeWork base capacity count ≤ BinaryWeightCoordinates.encodeWork larger largerCapacity count := by
  induction count with
  | zero => exact le_refl _
  | succ count ih => simp only [BinaryWeightCoordinates.encodeWork]; gcongr

@[gcongr] theorem readWork_mono {base larger order r s : ℕ} (hb : base ≤ larger) :
    BinaryWeightCoordinates.readWork base order r s ≤ BinaryWeightCoordinates.readWork larger order r s := by
  have hp : base^order ≤ larger^order := Nat.pow_le_pow_left hb order
  have hr := encodeWork_mono (count := r) hb hp
  have hs := encodeWork_mono (count := s) hb hp
  have hw := powerCounterWork_mono hb s
  unfold BinaryWeightCoordinates.readWork BinaryWeightCoordinates.jointWork
  dsimp only
  gcongr

@[gcongr] theorem distinctWork_mono {pool larger count : ℕ} (hp : pool ≤ larger) :
    BinaryDistinctTuples.work pool count ≤ BinaryDistinctTuples.work larger count := by
  unfold BinaryDistinctTuples.work BinaryDistinctTuples.pairWork
  gcongr

@[gcongr] theorem averageHeight_mono {primary body largerPrimary largerBody r s first second : ℕ}
    (hp : primary ≤ largerPrimary) (hb : body ≤ largerBody) (hh : first ≤ second) :
    BinaryTwoPoolAverage.height primary body r s first ≤ BinaryTwoPoolAverage.height largerPrimary largerBody r s second := by
  unfold BinaryTwoPoolAverage.height BinaryTwoPoolAverage.numeratorHeight BinaryTwoPoolAverage.normalizerHeight
  gcongr

@[gcongr] theorem averageWork_mono {primary body largerPrimary largerBody r s first second firstWork secondWork : ℕ}
    (hp : primary ≤ largerPrimary) (hb : body ≤ largerBody) (hh : first ≤ second) (hw : firstWork ≤ secondWork) :
    BinaryTwoPoolAverage.work primary body r s first firstWork ≤ BinaryTwoPoolAverage.work largerPrimary largerBody r s second secondWork := by
  unfold BinaryTwoPoolAverage.work BinaryTwoPoolAverage.numeratorWork BinaryTwoPoolAverage.normalizerWork
  gcongr
  · exact primitiveWorkBound_mono (Nat.add_le_add
      (tupleHeight_mono (count := r) hp (le_refl 0)) (tupleHeight_mono (count := s) hb (le_refl 0)))
  · exact primitiveWorkBound_mono (averageHeight_mono hp hb hh)

noncomputable def distinctWorkPolynomial (pool : Polynomial ℕ) (count : ℕ) : Polynomial ℕ :=
  Polynomial.C count*(Polynomial.C count*(12*Polynomial.C count+12*pool+20+2)+3)+1
noncomputable def normalizerHeightPolynomial (pool : Polynomial ℕ) (count : ℕ) : Polynomial ℕ :=
  BinaryTupleSum.heightPolynomial pool count 0
noncomputable def normalizerWorkPolynomial (pool : Polynomial ℕ) (count : ℕ) : Polynomial ℕ :=
  BinaryTupleSum.workPolynomial pool count 0 (distinctWorkPolynomial pool count+3)
noncomputable def averageHeightPolynomial (primary body : Polynomial ℕ) (r s : ℕ) (leafHeight : Polynomial ℕ) : Polynomial ℕ :=
  BinaryTupleSum.heightPolynomial primary r (BinaryTupleSum.heightPolynomial body s leafHeight)+
    normalizerHeightPolynomial primary r+normalizerHeightPolynomial body s
noncomputable def averageWorkPolynomial (primary body : Polynomial ℕ) (r s : ℕ) (leafHeight leafWork : Polynomial ℕ) : Polynomial ℕ :=
  BinaryTupleSum.workPolynomial primary r (BinaryTupleSum.heightPolynomial body s leafHeight)
    (distinctWorkPolynomial primary r+BinaryTupleSum.workPolynomial body s leafHeight (distinctWorkPolynomial body s+leafWork+2)+2)+
    normalizerWorkPolynomial primary r+normalizerWorkPolynomial body s+
    primitiveWorkPolynomial (normalizerHeightPolynomial primary r+normalizerHeightPolynomial body s)+
    2*primitiveWorkPolynomial (averageHeightPolynomial primary body r s leafHeight)+7

theorem distinctWorkPolynomial_eval (pool : Polynomial ℕ) (count security : ℕ) :
    (distinctWorkPolynomial pool count).eval security = BinaryDistinctTuples.work (pool.eval security) count := by
  simp only [distinctWorkPolynomial, BinaryDistinctTuples.work, BinaryDistinctTuples.pairWork,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_ofNat, Polynomial.eval_one]

theorem averageHeightPolynomial_eval (primary body leafHeight : Polynomial ℕ) (r s security : ℕ) :
    (averageHeightPolynomial primary body r s leafHeight).eval security = BinaryTwoPoolAverage.height
      (primary.eval security) (body.eval security) r s (leafHeight.eval security) := by
  simp only [averageHeightPolynomial, normalizerHeightPolynomial, BinaryTupleSum.heightPolynomial_eval,
    BinaryTwoPoolAverage.height, BinaryTwoPoolAverage.numeratorHeight, BinaryTwoPoolAverage.normalizerHeight,
    Polynomial.eval_add, Polynomial.eval_zero]

theorem averageWorkPolynomial_eval (primary body leafHeight leafWork : Polynomial ℕ) (r s security : ℕ) :
    (averageWorkPolynomial primary body r s leafHeight leafWork).eval security = BinaryTwoPoolAverage.work
      (primary.eval security) (body.eval security) r s (leafHeight.eval security) (leafWork.eval security) := by
  simp only [averageWorkPolynomial, normalizerWorkPolynomial, normalizerHeightPolynomial, BinaryTupleSum.workPolynomial_eval,
    BinaryTupleSum.heightPolynomial_eval, distinctWorkPolynomial_eval, primitiveWorkPolynomial_eval, averageHeightPolynomial_eval,
    BinaryTwoPoolAverage.work, BinaryTwoPoolAverage.numeratorWork, BinaryTwoPoolAverage.normalizerWork,
    BinaryTwoPoolAverage.normalizerHeight, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_zero, Polynomial.eval_ofNat]

noncomputable def gatherWorkPolynomial (pool : Polynomial ℕ) (count : ℕ) : Polynomial ℕ :=
  Polynomial.C count*(3*Polynomial.C count+3*pool+10)+2
noncomputable def blockHeightPolynomial (colors primary body referenceHeight tableHeight : Polynomial ℕ) (r s : ℕ) : Polynomial ℕ :=
  averageHeightPolynomial primary body r s (BinaryPairedTensor.heightPolynomial colors referenceHeight r tableHeight)
noncomputable def blockWorkPolynomial (colors primary body referenceHeight tableHeight : Polynomial ℕ) (order r s : ℕ) : Polynomial ℕ :=
  averageWorkPolynomial primary body r s (BinaryPairedTensor.heightPolynomial colors referenceHeight r tableHeight)
    (gatherWorkPolynomial primary r+gatherWorkPolynomial body s+
      BinaryPairedTensor.workPolynomial colors referenceHeight r tableHeight
        (BinaryWeightCoordinates.readWorkPolynomial colors order r s)+3)

noncomputable def blockHeightSumPolynomial (colors primary body referenceHeight tableHeight : Polynomial ℕ) (order : ℕ) : Polynomial ℕ :=
  ∑ arity : TruncatedArity order, blockHeightPolynomial colors primary body referenceHeight tableHeight arity.val.1.val arity.val.2.val
noncomputable def blockWorkSumPolynomial (colors primary body referenceHeight tableHeight : Polynomial ℕ) (order : ℕ) : Polynomial ℕ :=
  ∑ arity : TruncatedArity order, blockWorkPolynomial colors primary body referenceHeight tableHeight order arity.val.1.val arity.val.2.val

theorem gatherWorkPolynomial_eval (pool : Polynomial ℕ) (count security : ℕ) :
    (gatherWorkPolynomial pool count).eval security = gatherWork (pool.eval security) count := by
  simp only [gatherWorkPolynomial, gatherWork, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_ofNat]

theorem block_polynomial_bounds (security order primaryPool bodyPool referenceHeight tableHeight r s : ℕ)
    (colorBound primaryBound bodyBound referenceBound tableBound : Polynomial ℕ)
    (hq : colors security ≤ colorBound.eval security) (hp : primaryPool ≤ primaryBound.eval security)
    (hb : bodyPool ≤ bodyBound.eval security) (hr : referenceHeight ≤ referenceBound.eval security)
    (ht : tableHeight ≤ tableBound.eval security) :
    BinaryWeightBlock.height security primaryPool bodyPool referenceHeight tableHeight r s ≤
      (blockHeightPolynomial colorBound primaryBound bodyBound referenceBound tableBound r s).eval security ∧
    BinaryWeightBlock.work security order primaryPool bodyPool referenceHeight tableHeight r s ≤
      (blockWorkPolynomial colorBound primaryBound bodyBound referenceBound tableBound order r s).eval security := by
  have hlh := pairedHeight_mono (count := r) hq hr ht
  have hlw : BinaryWeightBlock.localWork security order primaryPool bodyPool referenceHeight tableHeight r s ≤
      gatherWork (primaryBound.eval security) r+gatherWork (bodyBound.eval security) s+
        BinaryPairedTensor.work (colorBound.eval security) (referenceBound.eval security) r (tableBound.eval security)
          (BinaryWeightCoordinates.readWork (colorBound.eval security) order r s)+3 := by
    unfold BinaryWeightBlock.localWork gatherWork
    gcongr
  constructor
  · have hx := averageHeight_mono (r := r) (s := s) hp hb hlh
    apply hx.trans_eq
    simp only [blockHeightPolynomial, averageHeightPolynomial_eval, BinaryPairedTensor.heightPolynomial_eval]
  · have hx := averageWork_mono (r := r) (s := s) hp hb hlh hlw
    apply hx.trans_eq
    simp only [blockWorkPolynomial, averageWorkPolynomial_eval, BinaryPairedTensor.heightPolynomial_eval,
      gatherWorkPolynomial_eval, BinaryPairedTensor.workPolynomial_eval, BinaryWeightCoordinates.readWorkPolynomial_eval,
      Polynomial.eval_add, Polynomial.eval_ofNat]

noncomputable def outputHeightPolynomial (colors primary body precision tableHeight : Polynomial ℕ) (order : ℕ) : Polynomial ℕ :=
  let H := blockHeightSumPolynomial colors primary body (BinaryReferenceTables.heightPolynomial precision) tableHeight order
  Polynomial.C (order+1)*(Polynomial.C (order+1)*(H+1)+1)

noncomputable def evaluationWorkPolynomial (colors primary body precision tableHeight : Polynomial ℕ) (order : ℕ) : Polynomial ℕ :=
  let H := blockHeightSumPolynomial colors primary body (BinaryReferenceTables.heightPolynomial precision) tableHeight order
  let K := blockWorkSumPolynomial colors primary body (BinaryReferenceTables.heightPolynomial precision) tableHeight order+Polynomial.C (5*order+11)
  let innerH := Polynomial.C (order+1)*(H+1)
  let innerW := Polynomial.C (order+1)*(K+primitiveWorkPolynomial (Polynomial.C (order+2)*(H+1))+2)+2
  Polynomial.C (order+1)*(innerW+primitiveWorkPolynomial (Polynomial.C (order+2)*(innerH+1))+2)+2

noncomputable def currentWorkPolynomial (colors primary body precision tableHeight : Polynomial ℕ) (order : ℕ) : Polynomial ℕ :=
  BinaryReferenceTables.currentWorkPolynomial precision+evaluationWorkPolynomial colors primary body precision tableHeight order+2

theorem current_polynomial_bounds (security order primaryPool bodyPool : ℕ) (hp : 0 < primaryPool) (hb : 0 < bodyPool)
    (colorBound primaryBound bodyBound precision tableBound : Polynomial ℕ)
    (hq : colors security ≤ colorBound.eval security) (hpp : primaryPool ≤ primaryBound.eval security)
    (hbb : bodyPool ≤ bodyBound.eval security)
    (table : BinaryWeightCoordinates.Table (colors security) order)
    (groups : Vector (Fin (colors security) × Fin (colors security)) primaryPool)
    (centers : Vector (Fin (colors security)) bodyPool)
    (ht : ∀ block word, HeightBound ((table.get block).get word).decode (tableBound.eval security)) :
    HeightBound (BinaryWeightProgram.current security (precision.eval security) order primaryPool bodyPool hp hb table groups centers).data.decode
      ((outputHeightPolynomial colorBound primaryBound bodyBound precision tableBound order).eval security) ∧
    (BinaryWeightProgram.current security (precision.eval security) order primaryPool bodyPool hp hb table groups centers).work ≤
      (currentWorkPolynomial colorBound primaryBound bodyBound precision tableBound order).eval security := by
  have hx := BinaryWeightProgram.current_bounds security order primaryPool bodyPool hp hb precision table groups centers (tableBound.eval security) ht
  let HR := (BinaryReferenceTables.heightPolynomial precision).eval security
  let H := blockHeightSumPolynomial colorBound primaryBound bodyBound (BinaryReferenceTables.heightPolynomial precision) tableBound order
  let W := blockWorkSumPolynomial colorBound primaryBound bodyBound (BinaryReferenceTables.heightPolynomial precision) tableBound order
  have hH : BinaryWeightProgram.blockHeightSum security order primaryPool bodyPool HR (tableBound.eval security) ≤ H.eval security := by
    simp only [H, blockHeightSumPolynomial, Polynomial.eval_finset_sum]
    exact Finset.sum_le_sum (fun arity _ => (block_polynomial_bounds security order primaryPool bodyPool HR (tableBound.eval security)
      arity.val.1.val arity.val.2.val colorBound primaryBound bodyBound (BinaryReferenceTables.heightPolynomial precision) tableBound
      hq hpp hbb (le_refl HR) (le_refl _)).1)
  have hW : BinaryWeightProgram.blockWorkSum security order primaryPool bodyPool HR (tableBound.eval security) ≤ W.eval security := by
    simp only [W, blockWorkSumPolynomial, Polynomial.eval_finset_sum]
    exact Finset.sum_le_sum (fun arity _ => (block_polynomial_bounds security order primaryPool bodyPool HR (tableBound.eval security)
      arity.val.1.val arity.val.2.val colorBound primaryBound bodyBound (BinaryReferenceTables.heightPolynomial precision) tableBound
      hq hpp hbb (le_refl HR) (le_refl _)).2)
  constructor
  · apply hx.1.mono
    unfold BinaryWeightProgram.outputHeight
    simp only [outputHeightPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_one]
    change (order+1)*((order+1)*(BinaryWeightProgram.blockHeightSum security order primaryPool bodyPool HR (tableBound.eval security)+1)+1) ≤
      (order+1)*((order+1)*(H.eval security+1)+1)
    gcongr
  · apply hx.2.trans
    simp only [currentWorkPolynomial, Polynomial.eval_add, Polynomial.eval_ofNat]
    apply Nat.add_le_add_right (Nat.add_le_add_left ?_ _) 2
    unfold BinaryWeightProgram.evaluationWork BinaryWeightProgram.termWork
    simp only [evaluationWorkPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      primitiveWorkPolynomial_eval, Polynomial.eval_ofNat, Polynomial.eval_one]
    change (order+1)*((order+1)*(BinaryWeightProgram.blockWorkSum security order primaryPool bodyPool HR (tableBound.eval security)+5*order+11+
        primitiveWorkBound ((order+2)*(BinaryWeightProgram.blockHeightSum security order primaryPool bodyPool HR (tableBound.eval security)+1))+2)+2+
      primitiveWorkBound ((order+2)*((order+1)*(BinaryWeightProgram.blockHeightSum security order primaryPool bodyPool HR (tableBound.eval security)+1)+1))+2)+2 ≤
      (order+1)*((order+1)*(W.eval security+(5*order+11)+primitiveWorkBound ((order+2)*(H.eval security+1))+2)+2+
      primitiveWorkBound ((order+2)*((order+1)*(H.eval security+1)+1))+2)+2
    simp only [Nat.add_assoc]
    gcongr
    · exact primitiveWorkBound_mono (Nat.mul_le_mul_left _ (Nat.add_le_add_right hH 1))
    · exact primitiveWorkBound_mono (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right hH 1)) 1))

noncomputable def primaryPoolPolynomial : Polynomial ℕ := (Polynomial.X+2)^128

theorem primaryPool_pos (security : ℕ) : 0 < Parameters.legCount security := by
  rw [Parameters.legCount_eq]
  exact pow_pos (Parameters.base_pos security) 128

theorem current_parameters_polynomial_bounds (security order : ℕ) (precision tableBound : Polynomial ℕ)
    (table : BinaryWeightCoordinates.Table (colors security) order)
    (groups : Vector (Fin (colors security) × Fin (colors security)) (Parameters.legCount security))
    (centers : Vector (Fin (colors security)) (BackgroundRates.ordinaryPool security))
    (ht : ∀ block word, HeightBound ((table.get block).get word).decode (tableBound.eval security)) :
    HeightBound (BinaryWeightProgram.current security (precision.eval security) order (Parameters.legCount security)
      (BackgroundRates.ordinaryPool security) (primaryPool_pos security) (BackgroundRates.ordinaryPool_pos security) table groups centers).data.decode
      ((outputHeightPolynomial BinaryPrimaryTable.countPolynomial primaryPoolPolynomial BinaryProposalMetadata.sizePolynomial precision tableBound order).eval security) ∧
    (BinaryWeightProgram.current security (precision.eval security) order (Parameters.legCount security)
      (BackgroundRates.ordinaryPool security) (primaryPool_pos security) (BackgroundRates.ordinaryPool_pos security) table groups centers).work ≤
      (currentWorkPolynomial BinaryPrimaryTable.countPolynomial primaryPoolPolynomial BinaryProposalMetadata.sizePolynomial precision tableBound order).eval security := by
  have hp : Parameters.legCount security ≤ primaryPoolPolynomial.eval security := by
    simp only [Parameters.legCount_eq, Parameters.base, primaryPoolPolynomial, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_ofNat]
    exact le_refl _
  have hb : BackgroundRates.ordinaryPool security ≤ BinaryProposalMetadata.sizePolynomial.eval security := by
    have hpool : BackgroundRates.ordinaryPool security ≤ Parameters.bodySize security :=
      (Nat.sub_le _ _).trans (Nat.sub_le _ _)
    have hbody : Parameters.bodySize security ≤ BinaryProposalMetadata.sizeBound security := by
      have hp := (BinaryProposalMetadata.counts_bounds security).2.2
      rw [(BinaryProposalMetadata.counts_value security).2.2] at hp
      simpa only [Parameters.bodySize_eq, Parameters.base] using hp
    exact (hpool.trans hbody).trans_eq (BinaryProposalMetadata.sizePolynomial_eval security).symm
  exact current_polynomial_bounds security order _ _ (primaryPool_pos security) (BackgroundRates.ordinaryPool_pos security)
    BinaryPrimaryTable.countPolynomial primaryPoolPolynomial BinaryProposalMetadata.sizePolynomial precision tableBound
    (BinaryPrimaryTable.count_bound security) hp hb table groups centers ht

end CurrentAFT.BinaryWeightResources
