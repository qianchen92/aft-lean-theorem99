import AFT.ReferenceChargeConditioning

namespace AFT.HistogramGenerating
open scoped Classical
noncomputable section

def uniformZeroSumHistogram (N : ℕ) (G : Type*) [Fintype G] [AddCommGroup G] :
    FiniteDist (Histogram N G) := (uniformZeroSum N G).map histogram

variable {G : Type*} [Fintype G] [AddCommGroup G]

theorem uniform_histogram_charge_decidable (N : ℕ) [d : DecidableEq (Fin N)] (hN : 0 < N) (required : G) :
    ((FiniteDist.independent (fun _ : Fin N => FiniteDist.uniform G)).map histogram).eventMass
      (fun hist => histogramCharge N hist=required)=(Fintype.card G : ℝ)⁻¹ := by
  have hd : d=instDecidableEqFin N := Subsingleton.elim _ _
  cases hd
  exact uniform_histogram_charge N hN required

theorem uniform_histogram_condition_decidable (N : ℕ) [d : DecidableEq (Fin N)] (hN : 0 < N)
    (hpos : 0 < ((FiniteDist.independent (fun _ : Fin N => FiniteDist.uniform G)).map histogram).eventMass
      (fun hist => histogramCharge N hist=0)) :
    (((FiniteDist.independent (fun _ : Fin N => FiniteDist.uniform G)).map histogram).condition
      (fun hist => histogramCharge N hist=0) hpos)=uniformZeroSumHistogram N G := by
  have hd : d=instDecidableEqFin N := Subsingleton.elim _ _
  cases hd
  exact uniform_histogram_condition_zero N hN

end
end AFT.HistogramGenerating
