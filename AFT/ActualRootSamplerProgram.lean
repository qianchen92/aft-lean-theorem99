import AFT.ActualRootTicketRejection
import AFT.FiniteConditionProgram
import AFT.ParameterProgram

/-! # A standalone fair-bit program for the complete actual protected root source -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics FiniteDist FiniteConditionProgram
open scoped BigOperators

/-- The body population is computed by the bounded public prime search. -/
def actualRootPopulationProgram (n : ℕ) : ℕ :=
  (ParameterProgram.modulus n).value*(max 2 n)^20-2*(max 2 n)^30

theorem actualRootPopulationProgram_eq (n : ℕ) : actualRootPopulationProgram n=Parameters.bodies n := by
  unfold actualRootPopulationProgram
  rw [ParameterProgram.modulus_value]
  rfl

/-- One full independent root proposal from its flat fair-bit tape. -/
def actualRootWordDraw (n count : ℕ)
    (word : Fin (count*actualRootTicketBits n n) → Fin 2) : Fin count → Window (3*n^2-1) :=
  fun index => actualRootGaussianDraw n n (groupBits count (actualRootTicketBits n n) word index)

def actualRootWholeDraw (n count : ℕ)
    (word : Fin (n^33*(count*actualRootTicketBits n n)) → Fin 2) : Fin count → Window (3*n^2-1) :=
  draw (count*actualRootTicketBits n n) (n^33) (actualRootWordDraw n count)
    (fun roots => (∑ index,(roots index : ℤ))=0)
    (fun _ => ⟨0,Finset.mem_Icc.mpr ⟨by omega,by omega⟩⟩) word

/-- The complete parameter-free root-source program: only `n` and fair bits
are supplied, and its output is always in the protected zero-sum window. -/
def actualRootSampler (n : ℕ)
    (word : Fin (n^33*(actualRootPopulationProgram n*actualRootTicketBits n n)) → Fin 2) :
    Fin (actualRootPopulationProgram n) → Window (3*n^2-1) :=
  actualRootWholeDraw n (actualRootPopulationProgram n) word

theorem actualRootWholeDraw_zero_sum (n count : ℕ)
    (word : Fin (n^33*(count*actualRootTicketBits n n)) → Fin 2) :
    (∑ index,(actualRootWholeDraw n count word index : ℤ))=0 := by
  unfold actualRootWholeDraw draw firstAcceptedFrom
  exact firstAccepted_event (fun roots : Fin count → Window (3*n^2-1) =>
    (∑ index,(roots index : ℤ))=0) _ (by simp) _ _

theorem actualRootSampler_zero_sum (n : ℕ)
    (word : Fin (n^33*(actualRootPopulationProgram n*actualRootTicketBits n n)) → Fin 2) :
    (∑ index,(actualRootSampler n word index : ℤ))=0 := actualRootWholeDraw_zero_sum _ _ _

noncomputable section
open scoped Topology
set_option backward.isDefEq.respectTransparency false

theorem actualRootWordDraw_law (n count : ℕ) :
    (independent (fun _ : Fin (count*actualRootTicketBits n n) => uniform (Fin 2))).map
      (actualRootWordDraw n count)=independent (fun _ : Fin count => actualRootTicketLaw n n) := by
  have hg := groupBits_law count (actualRootTicketBits n n)
  have hh := congrArg (fun law => law.map (fun roots : Fin count → Fin (actualRootTicketBits n n) → Fin 2 =>
    fun index => actualRootGaussianDraw n n (roots index))) hg
  dsimp only at hh
  rw [FiniteDist.map_map] at hh
  apply hh.trans
  rw [FiniteConditionProgram.independent_decode]
  simp_rw [actualRootGaussianDraw_law]

theorem actualRootWholeDraw_law (n count : ℕ) :
    (independent (fun _ : Fin (n^33*(count*actualRootTicketBits n n)) => uniform (Fin 2))).map
      (actualRootWholeDraw n count)=
      cappedCondition (independent (fun _ : Fin count => actualRootTicketLaw n n))
        (fun roots => (∑ index,(roots index : ℤ))=0)
        (CanonicalMoments.pointLaw (fun _ => windowZero (v7RootCutoff n))) (n^33) := by
  unfold actualRootWholeDraw
  rw [draw_law,actualRootWordDraw_law]
  rfl

/-- The available random tape has a fixed polynomial length, including all
proposals that may be rejected. -/
theorem actualRootSampler_bits (n : ℕ) (hn : 2 ≤ n) :
    n^33*(actualRootPopulationProgram n*actualRootTicketBits n n) ≤ 16*n^95 := by
  have hN : actualRootPopulationProgram n ≤ 2*n^60 := by
    rw [actualRootPopulationProgram_eq]
    apply (Nat.sub_le _ _).trans
    simpa only [Parameters.security_eq n hn] using (Parameters.dimension_bounds n).2
  calc
    _ ≤ n^33*((2*n^60)*(8*n^2)) := by gcongr; exact actualRootTicketBits_bound n hn
    _ = _ := by rw [show n^95=n^33*n^60*n^2 by rw [← pow_add,← pow_add]]; ring

end
end AFT.V7Calibration
