import AFT.CountableFiniteChannel

/-! # Finite laws embedded into an arbitrary countable source space -/
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Input Source Output : Type*} [Fintype Input] [Fintype Output]

def massOn (law : FiniteDist Input) (map : Input → Source) (source : Source) : ℝ :=
  ∑ point,if map point=source then law.weight point else 0

omit [Fintype Output] in
theorem massOn_nonneg (law : FiniteDist Input) (map : Input → Source) (source : Source) :
    0 ≤ massOn law map source := Finset.sum_nonneg fun point _ => by
      split_ifs
      · exact law.nonneg point
      · exact le_rfl

omit [Fintype Output] in
theorem massOn_hasSum (law : FiniteDist Input) (map : Input → Source) : HasSum (massOn law map) 1 := by
  have hh := hasSum_sum (s := (Finset.univ : Finset Input))
    (fun point _ => hasSum_ite_eq (map point) (law.weight point))
  change HasSum (fun source => ∑ point,if map point=source then law.weight point else 0) 1
  simpa only [eq_comm,FiniteDist.sum_one] using hh

omit [Fintype Output] in
theorem massOn_summable (law : FiniteDist Input) (map : Input → Source) : Summable (massOn law map) :=
  (massOn_hasSum law map).summable

omit [Fintype Output] in
theorem massOn_sum (law : FiniteDist Input) (map : Input → Source) : (∑' source,massOn law map source)=1 :=
  (massOn_hasSum law map).tsum_eq

/-- Averaging a channel against the finite pushforward equals averaging it
against the original finite law, on all output coordinates. -/
theorem countableMix_massOn (law : FiniteDist Input) (map : Input → Source)
    (channel : Source → FiniteDist Output) :
    countableMix (massOn law map) (massOn_nonneg law map) (massOn_summable law map)
      (massOn_sum law map) channel=law.mix (fun point => channel (map point)) := by
  apply FiniteDist.ext
  intro output
  change (∑' source,(∑ point,if map point=source then law.weight point else 0)*(channel source).weight output)=_
  simp only [Finset.sum_mul,ite_mul,zero_mul]
  have hsum (point : Input) : Summable (fun source =>
      if map point=source then law.weight point*(channel source).weight output else 0) := by
    have hh := (hasSum_ite_eq (map point) (law.weight point*(channel (map point)).weight output)).summable
    apply hh.congr
    intro source
    by_cases he : source=map point <;> simp [he,eq_comm]
  rw [Summable.tsum_finsetSum (fun point (_ : point∈Finset.univ) => hsum point)]
  simp only [eq_comm,tsum_ite_eq]
  rfl

theorem countableMix_massOn_tvBound (mass : Source → ℝ)
    (hnonneg : ∀ source,0 ≤ mass source) (hsum : Summable mass) (hone : ∑' source,mass source=1)
    (law : FiniteDist Input) (map : Input → Source) (channel : Source → FiniteDist Output)
    (error : ℝ) (herror : (∑' source,|mass source-massOn law map source|)/2≤error) :
    TVBound (countableMix mass hnonneg hsum hone channel) (law.mix (fun point => channel (map point))) error := by
  have hh := countableMix_tvBound mass (massOn law map) hnonneg (massOn_nonneg law map)
    hsum (massOn_summable law map) hone (massOn_sum law map) channel error herror
  rw [countableMix_massOn] at hh
  exact hh

end
end AFT.FiniteDist
