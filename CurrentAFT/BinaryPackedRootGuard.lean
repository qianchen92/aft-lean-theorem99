import CurrentAFT.BinaryPackedRootMetadata

/-! Actual binary safety and dummy-slot guards for packed group sources. -/
namespace CurrentAFT.BinaryPackedRootGuard
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
open BinaryPackedRootMetadata RationalRootGroupProgram
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus


def safe (colors margin output : ℕ) : CountedValue Bool :=
  let below := lessCounter output margin
  let translated := addCounter output margin
  let upper := lessCounter translated.count colors
  ⟨!below.value && upper.value,below.work+translated.work+upper.work+3⟩

 theorem safe_value (colors margin output : ℕ) :
    (safe colors margin output).value = true ↔ (margin:ℤ) ≤ output ∧ (output:ℤ) < (colors:ℤ)-margin := by
  simp only [safe,Bool.and_eq_true]
  rw [Bool.not_eq_true',Bool.eq_false_iff]
  have hlo : (lessCounter output margin).value ≠ true ↔ ¬output < margin := not_congr (lessCounter_value _ _)
  rw [hlo,lessCounter_value,addCounter_value]
  omega

 theorem safe_work (colors margin output : ℕ) (ho : output ≤ colors) : (safe colors margin output).work ≤ 11*colors+6*margin+10 := by
  have hl := lessCounter_work output margin
  have ha := addCounter_work output margin
  have hu : (lessCounter (addCounter output margin).count colors).work ≤ 3*(output+margin)+3*colors+2 := by
    exact (lessCounter_work _ _).trans_eq (by rw [addCounter_value];ring)
  change _+_+_+3 ≤ _
  omega



def group {r s kept tags : ℕ} (security colors margin : ℕ) (data : Data r s kept tags)
    (source : Vector (Color security) (((r+s)+kept)*3)) (index : Fin ((r+s)+kept)) : CountedValue Bool :=
  let role := readVector LocalRole.primary data.roles index
  let first := sourceEntry security source index 1
  let last := sourceEntry security source index 2
  let firstZero := equalCounter first.value.val 0
  let lastZero := equalCounter last.value.val 0
  let interior := safe colors margin first.value.val
  let answer := match role.value with
    | .primary => true
    | .ordinary => interior.value && lastZero.value
    | .leg | .center | .queue => firstZero.value && lastZero.value
  ⟨answer,role.work+first.work+last.work+firstZero.work+lastZero.work+interior.work+6⟩

 theorem group_value {r s kept tags : ℕ} (security colors margin : ℕ) (data : Data r s kept tags)
    (source : Vector (Color security) (((r+s)+kept)*3)) (index : Fin ((r+s)+kept))
    (hq : colors = RationalBackgroundProfiles.colors security) (hm : margin = RationalBackgroundProfiles.margin security) :
    (group security colors margin data source index).value = true ↔
      RationalPackedRootProgram.validGroup security (data.metadata.roles index) (word security source index) := by
  subst colors
  subst margin
  simp only [group,readVector_value,sourceEntry_value,Data.metadata]
  cases data.roles.get index <;>
    simp only [RationalPackedRootProgram.validGroup,Bool.and_eq_true,equalCounter_value,safe_value,RationalBackgroundProfiles.Safe,word]


def marginProgram (security : ℕ) : UnaryCounterResult :=
  let base := addCounter security 2
  let square := powerCounter base.count 2
  let result := multiplyCounter 3 square.count
  ⟨result.count,base.work+square.work+result.work+3⟩

 theorem marginProgram_value (security : ℕ) : (marginProgram security).count = RationalBackgroundProfiles.margin security := by
  simp only [marginProgram,multiplyCounter_value,powerCounter_value,addCounter_value,RationalBackgroundProfiles.margin]


def current {r s kept tags : ℕ} (security : ℕ) (data : Data r s kept tags)
    (source : Vector (Color security) (((r+s)+kept)*3)) : CountedValue Bool :=
  let colors := PublicParameterProgram.modulus security
  let margin := marginProgram security
  let result := BinaryProposalGuard.allFin ((r+s)+kept) (group security colors.count margin.count data source)
  ⟨result.value,colors.work+margin.work+result.work+3⟩

 theorem current_value {r s kept tags : ℕ} (security : ℕ) (data : Data r s kept tags)
    (source : Vector (Color security) (((r+s)+kept)*3)) :
    (current security data source).value = true ↔ RationalPackedRootProgram.Valid security data.metadata (word security source) := by
  change (BinaryProposalGuard.allFin _ _).value = true ↔ _
  rw [BinaryProposalGuard.allFin_value]
  apply forall_congr'
  intro index
  exact group_value security _ _ data source index rfl (marginProgram_value security)

 theorem group_work {r s kept tags : ℕ} (security colors margin : ℕ) (data : Data r s kept tags)
    (source : Vector (Color security) (((r+s)+kept)*3)) (index : Fin ((r+s)+kept))
    (hq : colors = (PublicParameterProgram.modulus security).count) :
    (group security colors margin data source index).work ≤ 100*((r+s)+kept)+30*colors+10*margin+100 := by
  let role := readVector LocalRole.primary data.roles index
  let first := sourceEntry security source index 1
  let last := sourceEntry security source index 2
  have wr := readVector_work LocalRole.primary data.roles index
  have wf := sourceEntry_work security source index 1
  have wl := sourceEntry_work security source index 2
  have wef := equalCounter_work first.value.val 0
  have wel := equalCounter_work last.value.val 0
  have hf : first.value.val ≤ colors := hq ▸ first.value.isLt.le
  have hl : last.value.val ≤ colors := hq ▸ last.value.isLt.le
  have ws := safe_work colors margin first.value.val hf
  change role.work+first.work+last.work+(equalCounter first.value.val 0).work+
    (equalCounter last.value.val 0).work+(safe colors margin first.value.val).work+6 ≤ _
  change role.work ≤ _ at wr
  change first.work ≤ _ at wf
  change last.work ≤ _ at wl
  omega

noncomputable section

def marginPolynomial : Polynomial ℕ := 3*(Polynomial.X+2)^2

def marginWorkPolynomial : Polynomial ℕ :=
  2*Polynomial.X+1+3*(6*(Polynomial.X+3)^4+4)+3*(2*(Polynomial.X+2)^2+3)+4

 theorem margin_work (security : ℕ) : (marginProgram security).work ≤ marginWorkPolynomial.eval security := by
  have hp : (powerCounter (addCounter security 2).count 2).work ≤ powerCounterWork (security+2) 2 := by
    simpa only [addCounter_value] using powerCounter_work (addCounter security 2).count 2
  change (addCounter security 2).work+(powerCounter (addCounter security 2).count 2).work+
    (multiplyCounter 3 (powerCounter (addCounter security 2).count 2).count).work+3 ≤ _
  rw [addCounter_work,multiplyCounter_work,powerCounter_value,addCounter_value]
  simp only [marginWorkPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one]
  simp only [addCounter_value] at hp
  unfold powerCounterWork at hp
  norm_num only at hp
  rw [show security+2+1=security+3 by omega] at hp
  omega


def workPolynomial (groups : ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+marginWorkPolynomial+
    Polynomial.C groups*(Polynomial.C (100*groups)+30*CurrentProposalResources.primeSizePolynomial+10*marginPolynomial+102)+4

 theorem current_work {r s kept tags : ℕ} (security : ℕ) (data : Data r s kept tags)
    (source : Vector (Color security) (((r+s)+kept)*3)) :
    (current security data source).work ≤ (workPolynomial ((r+s)+kept)).eval security := by
  have hg (index : Fin ((r+s)+kept)) := group_work security (PublicParameterProgram.modulus security).count
    (marginProgram security).count data source index rfl
  have hq := BinaryRootReferenceResources.colors_bound security
  have hm : (marginProgram security).count = marginPolynomial.eval security := by
    rw [marginProgram_value]
    simp only [RationalBackgroundProfiles.margin,marginPolynomial,Polynomial.eval_mul,Polynomial.eval_pow,
      Polynomial.eval_add,Polynomial.eval_ofNat,Polynomial.eval_X]
  have hh := BinaryProposalGuard.allFin_work ((r+s)+kept)
    (100*((r+s)+kept)+30*(CurrentProposalResources.primeSizePolynomial.eval security)+10*marginPolynomial.eval security+100)
    (group security (PublicParameterProgram.modulus security).count (marginProgram security).count data source) (by
      intro index
      exact (hg index).trans (by rw [hm];omega))
  have hh' : (BinaryProposalGuard.allFin ((r+s)+kept)
      (group security (PublicParameterProgram.modulus security).count (marginProgram security).count data source)).work ≤
      ((r+s)+kept)*(100*((r+s)+kept)+30*(CurrentProposalResources.primeSizePolynomial.eval security)+10*marginPolynomial.eval security+102)+1 :=
    hh.trans_eq (by ring)
  have wq := PublicParameterProgram.modulus_work security
  have wm := margin_work security
  change (PublicParameterProgram.modulus security).work+(marginProgram security).work+
    (BinaryProposalGuard.allFin _ _).work+3 ≤ _
  simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_ofNat,
    PublicParameterProgram.workPolynomial_eval]
  omega

end

end CurrentAFT.BinaryPackedRootGuard
