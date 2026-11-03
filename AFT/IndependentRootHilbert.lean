import AFT.ActualIndependentPairedHilbert
import AFT.IndependentRootBlock
import AFT.HilbertAveraging

/-! # True independent-root channel on arbitrary joint input fibers -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance independentRootHilbertFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

theorem independentPairedDensity_hilbert_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
    ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    (∀ mark first second,publicChartRaw C n mark (charts mark) (fun _ => 1) first second =
      conditionalJointOutput C n mark (fun _ => 1) first second) →
    ∀ (Fiber : Type) [Fintype Fiber], ∀ fiber : FiniteDist Fiber,
    ∀ kernel : Fin (Parameters.modulus n) → Fiber → ℝ,
      (∀ rest,∑ color,(actualPrimaryLaw C n (beta n)).weight color*kernel color rest=0) →
    ∀ squareBound : ℝ,0 ≤ squareBound →
      (∀ color,fiber.l2Sq (kernel color) ≤ squareBound) →
    (fiber.expectation (fun rest =>
      (FiniteDist.independent (fun _ : Fin 4 => actualPrimaryLaw C n (beta n))).l2Sq
        (independentPairedDensity C n (beta n) charts
          (fun color => (actualPrimaryLaw C n (beta n)).weight color*kernel color rest))) ≤
      (26912768*(n : ℝ)^8)*fiber.expectation (fun rest =>
        (actualPrimaryLaw C n (beta n)).l2Sq (fun color => kernel color rest))) ∧
    (∀ (slot : Fin 4) values,fiber.expectation (fun rest => MixedKernel.fiberSq
      (fun _ : Fin 4 => actualPrimaryLaw C n (beta n))
      (independentPairedDensity C n (beta n) charts
        (fun color => (actualPrimaryLaw C n (beta n)).weight color*kernel color rest)) {slot} values) ≤
      (34816*2048*1191970)*(n : ℝ)^8*squareBound) ∧
    (∀ word,fiber.l2Sq (fun rest => independentPairedDensity C n (beta n) charts
      (fun color => (actualPrimaryLaw C n (beta n)).weight color*kernel color rest) word) ≤
      (34816^2*1191970)*(n : ℝ)^16*squareBound) := by
  filter_upwards [fixedPairedPrimaryDensity_hilbert_eventually C hC beta hbeta]
    with n hh charts hc Fiber inst fiber kernel hcanonical squareBound hbound hkernel
  have hr (root : Window (v7RootCutoff n)) : |(root : ℤ)| ≤ (v7RootCutoff n : ℤ) :=
    abs_le.mpr (Finset.mem_Icc.mp root.property)
  have hfixed (roots : Window (v7RootCutoff n) × Window (v7RootCutoff n)) :=
    hh charts hc roots.1 roots.2 0 (hr roots.1) (hr roots.2) (by simp)
      Fiber fiber kernel hcanonical squareBound hbound hkernel
  have heq (rest : Fiber) : independentPairedDensity C n (beta n) charts
      (fun color => (actualPrimaryLaw C n (beta n)).weight color*kernel color rest) =
      fun word => ∑ roots,(pairedRootReference n).weight roots*
        fixedPairedPrimaryDensity C n (beta n) charts roots.1 roots.2 0
          (fun color => (actualPrimaryLaw C n (beta n)).weight color*kernel color rest) word :=
    funext (independentPairedDensity_average _ _ _ _ _)
  simp_rw [heq]
  refine ⟨?_,?_,?_⟩
  · have hout := FiniteDist.expectation_l2Sq_average_le_bound (pairedRootReference n) fiber
      (FiniteDist.independent (fun _ : Fin 4 => actualPrimaryLaw C n (beta n)))
      (fun roots rest word => fixedPairedPrimaryDensity C n (beta n) charts roots.1 roots.2 0
        (fun color => (actualPrimaryLaw C n (beta n)).weight color*kernel color rest) word) _
      (fun roots => (hfixed roots).1)
    convert hout using 1
  · intro slot values
    apply FiniteDist.expectation_l2Sq_average_le_bound (pairedRootReference n) fiber
      (FiniteDist.independent (fun _ : Fin 4 => actualPrimaryLaw C n (beta n))) _ _
    intro roots
    change fiber.expectation (fun rest => MixedKernel.fiberSq
      (fun _ : Fin 4 => actualPrimaryLaw C n (beta n))
      (fixedPairedPrimaryDensity C n (beta n) charts roots.1 roots.2 0
        (fun color => (actualPrimaryLaw C n (beta n)).weight color*kernel color rest)) {slot} values) ≤ _
    simp_rw [MixedKernel.fiberSq_singleton_split]
    change fiber.expectation (fun rest =>
      (FiniteDist.independent (fun _ : {other : Fin 4 // other ≠ slot} => actualPrimaryLaw C n (beta n))).expectation
        (fun word => fixedPairedPrimaryDensity C n (beta n) charts roots.1 roots.2 0
          (fun color => (actualPrimaryLaw C n (beta n)).weight color*kernel color rest)
          ((Equiv.funSplitAt slot (Fin (Parameters.modulus n))).symm (values slot,word))^2)) ≤ _
    rw [FiniteDist.expectation_comm]
    exact (hfixed roots).2.1 slot (values slot)
  · intro word
    exact FiniteDist.l2Sq_average_le_bound (pairedRootReference n) fiber _ _
      (fun roots => (hfixed roots).2.2 word)

end
end AFT.V7Calibration
