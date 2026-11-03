import CurrentAFT.CurrentProposalSamplerPolynomial
import CurrentAFT.BinaryRejectionCap

/-! Executed lengths and preparation of every current flat-tape leaf. The
native prime, safe interval, anchor width, edge window, placement dimensions,
and rejection cap are computed by their counted parameter programs. -/
namespace CurrentAFT.BinaryPublicBitSizes
open AFT BinaryArithmetic RationalRejectionProgram RationalNumerics
open scoped Polynomial
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false

structure Lengths where
  activation : ℕ
  control : ℕ
  safe : ℕ
  anchor : ℕ
  edge : ℕ
  chart : ℕ
  body : ℕ
  endpoint : ℕ
  work : ℕ

def assemble (security colors safeCount anchorWidth cutoff population dimension : ℕ) : Lengths :=
  let activation := addCounter security 3
  let controlFirst := addCounter security colors
  let control := addCounter controlFirst.count 1
  let safeFirst := addCounter security safeCount
  let safe := addCounter safeFirst.count 1
  let anchorFirst := addCounter security anchorWidth
  let anchor := addCounter anchorFirst.count 1
  let doubleCutoff := doubleCounter cutoff
  let interval := addCounter doubleCutoff.count 1
  let edgeFirst := addCounter security interval.count
  let edge := addCounter edgeFirst.count 2
  let square := multiplyCounter colors colors
  let cube := multiplyCounter colors square.count
  let chartFirst := addCounter security cube.count
  let chart := addCounter chartFirst.count 1
  let body := multiplyCounter population security
  let endpoint := multiplyCounter dimension security
  ⟨activation.count,control.count,safe.count,anchor.count,edge.count,chart.count,body.count,endpoint.count,
    activation.work+controlFirst.work+control.work+safeFirst.work+safe.work+anchorFirst.work+anchor.work+
      doubleCutoff.work+interval.work+edgeFirst.work+edge.work+square.work+cube.work+chartFirst.work+chart.work+
      body.work+endpoint.work+20⟩

structure Data extends Lengths where
  dimensions : CurrentProposalDimensions.Result
  retries : UnaryCounterResult

def current (security : ℕ) : Data :=
  let dimensions := CurrentProposalDimensions.current security
  let reference := CurrentReferenceDraw.counts security
  let anchor := CurrentAnchorIndexDraw.width security
  let cutoff := CurrentEdgeDrawProgram.cutoffProgram security
  let retry := BinaryRejectionCap.current security
  let result := assemble security dimensions.colors reference.safe anchor.count cutoff.quotient
    dimensions.body dimensions.dimension
  { toLengths := {result with work := dimensions.work+reference.work+anchor.work+cutoff.work+retry.work+result.work+6}
    dimensions := dimensions
    retries := retry }

theorem dimensions_value (security : ℕ) :
    (current security).dimensions = CurrentProposalDimensions.current security := rfl

theorem retries_value (security : ℕ) :
    (current security).retries = BinaryRejectionCap.current security := rfl

theorem activation_value (security : ℕ) : (current security).activation = security+3 := by
  simp only [current,assemble,addCounter_value]

theorem control_value (security : ℕ) :
    (current security).control = security+(PublicParameterProgram.modulus security).count+1 := by
  simp only [current,assemble,addCounter_value]
  rw [(CurrentProposalDimensions.current_values security).1,PublicParameterProgram.modulus_value]

theorem safe_value (security : ℕ) :
    (current security).safe = security+(CurrentReferenceDraw.counts security).safe+1 := by
  simp only [current,assemble,addCounter_value]

theorem anchor_value (security : ℕ) :
    (current security).anchor = security+(CurrentAnchorIndexDraw.width security).count+1 := by
  simp only [current,assemble,addCounter_value]

theorem edge_value (security : ℕ) :
    (current security).edge = windowTicketBits (DiffuseProfiles.edgeCutoff security) security := by
  simp only [current,assemble,addCounter_value,doubleCounter_value,CurrentEdgeDrawProgram.cutoff_value,
    windowTicketBits]

theorem chart_value (security : ℕ) :
    (current security).chart = security+Parameters.modulus security*(Parameters.modulus security*Parameters.modulus security)+1 := by
  simp only [current,assemble,addCounter_value,multiplyCounter_value,
    (CurrentProposalDimensions.current_values security).1]

theorem body_value (security : ℕ) :
    (current security).body = (CurrentProposalDimensions.current security).body*security := by
  simp only [current,assemble,multiplyCounter_value]

theorem endpoint_value (security : ℕ) :
    (current security).endpoint = (CurrentProposalDimensions.current security).dimension*security := by
  simp only [current,assemble,multiplyCounter_value]

/-- Polynomial expression for the work of the actual fixed arithmetic plan. -/
def formula {R : Type*} [Semiring R] (security colors safeCount anchorWidth cutoff population dimension : R) : R :=
  (2*security+1)+(2*security+1)+(2*(security+colors)+1)+
    (2*security+1)+(2*(security+safeCount)+1)+(2*security+1)+(2*(security+anchorWidth)+1)+
    (3*cutoff+1)+(2*(2*cutoff)+1)+(2*security+1)+(2*(security+(2*cutoff+1))+1)+
    (colors*(2*colors+3)+1)+(colors*(2*(colors*colors)+3)+1)+
    (2*security+1)+(2*(security+colors*(colors*colors))+1)+
    (population*(2*security+3)+1)+(dimension*(2*security+3)+1)+20

theorem assemble_work (security colors safeCount anchorWidth cutoff population dimension : ℕ) :
    (assemble security colors safeCount anchorWidth cutoff population dimension).work =
      formula security colors safeCount anchorWidth cutoff population dimension := by
  simp only [assemble,addCounter_value,multiplyCounter_value,doubleCounter_value,
    addCounter_work,multiplyCounter_work,doubleCounter_work,formula]

theorem formula_mono {security first second anchor cutoff population dimension
    colors safeCount width window body endpoints : ℕ}
    (hc : first≤colors) (hs : second≤safeCount) (ha : anchor≤width)
    (hw : cutoff≤window) (hb : population≤body) (hd : dimension≤endpoints) :
    formula security first second anchor cutoff population dimension ≤
      formula security colors safeCount width window body endpoints := by
  unfold formula
  gcongr

noncomputable section
open CurrentProposalResources CurrentProposalSamplerPolynomial CurrentReferenceCacheWork
attribute [local irreducible] CurrentProposalDimensions.current CurrentReferenceDraw.counts
  CurrentAnchorIndexDraw.width CurrentEdgeDrawProgram.cutoffProgram BinaryRejectionCap.current
  PublicParameterProgram.modulus

def workPolynomial : Polynomial ℕ :=
  metadataWorkPolynomial+countsWorkPolynomial+widthWorkPolynomial+edgeCutoffWorkPolynomial+
    BinaryRejectionCap.workPolynomial+
    formula Polynomial.X countPolynomial countPolynomial countPolynomial
      cutoffSizePolynomial countPolynomial countPolynomial+6

theorem current_work (security : ℕ) :
    (current security).work ≤ workPolynomial.eval security := by
  have hm := CurrentProposalResources.metadata_work security
  have hr := CurrentReferenceCacheWork.counts_work security
  have ha := CurrentProposalSamplerPolynomial.width_work security
  have he := CurrentEdgeDrawProgram.cutoff_work security
  rw [← edgeCutoffWorkPolynomial_eval] at he
  have ht := BinaryRejectionCap.current_work security
  have hc := (CurrentProposalResources.count_bounds security).2.2.1
  have hs := (CurrentReferenceCacheWork.native_bounds security).2.1
  have hw := CurrentProposalSamplerPolynomial.width_count security
  have hb := (CurrentProposalResources.count_bounds security).2.2.2.1
  have hd := (CurrentProposalResources.count_bounds security).2.2.2.2
  have hcut : (CurrentEdgeDrawProgram.cutoffProgram security).quotient ≤ cutoffSizePolynomial.eval security := by
    rw [CurrentEdgeDrawProgram.cutoff_value]
    simp only [cutoffSizePolynomial,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_ofNat]
    unfold DiffuseProfiles.edgeCutoff
    exact (Nat.div_le_self _ _).trans (by
      simpa only [Parameters.sourceCutoff,Parameters.base] using Nat.sub_le (Parameters.sourceCutoff security) 1)
  have hf := formula_mono (security:=security) hc hs hw hcut hb hd
  change (CurrentProposalDimensions.current security).work+(CurrentReferenceDraw.counts security).work+
    (CurrentAnchorIndexDraw.width security).work+(CurrentEdgeDrawProgram.cutoffProgram security).work+
    (BinaryRejectionCap.current security).work+_+6≤_
  rw [assemble_work]
  simp only [workPolynomial,formula,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one] at hf ⊢
  omega

end
end CurrentAFT.BinaryPublicBitSizes
