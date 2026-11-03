import AFT.IndependentPolynomialAction
import AFT.CanonicalColumnOperator
import AFT.KernelPolynomialTruncation

/-! # The actual canonical cutoff U preserves complete role-polynomial semantics -/
namespace AFT.V7Calibration
open GaussianSource RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance independentUpperPolynomialFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {Output : Type*}
variable (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (cutoff depth : ℕ)

theorem independentUpperLinear_eq_truncate_raw
    (table : Table (InputSeed (Fin (Parameters.modulus n))))
    (hc : InputTableCanonical (actualPrimaryLaw C n beta) (actualBodyLaw C n beta) table)
    (ht : truncate (fun seed => seed.primaryOrder+seed.bodyOrder) cutoff table=table) :
    independentUpperLinear C n beta operator charts cutoff depth table=
      truncate (fun seed => seed.primaryOrder+seed.bodyOrder) cutoff
        (independentRawColumnLinear C n beta operator charts depth table) := by
  have hcolumns : (∑ powers∈table.support,MvPolynomial.coeff powers table •
      independentUpperColumn C n beta operator charts cutoff depth powers)=
      ∑ powers∈table.support,MvPolynomial.coeff powers table •
        truncate (fun seed => seed.primaryOrder+seed.bodyOrder) cutoff
          (independentGlobalQuotient C n beta operator charts (mixedMonomialSeed powers) depth-
            MvPolynomial.X (mixedMonomialSeed powers)) := by
    apply Finset.sum_congr rfl
    intro powers hp
    have hd : weightedOrder (fun seed => seed.primaryOrder+seed.bodyOrder) powers ≤ cutoff := by
      have hm : powers∈(truncate (fun seed => seed.primaryOrder+seed.bodyOrder) cutoff table).support := by
        rw [ht]
        exact hp
      exact (Finset.mem_filter.mp hm).2
    simp only [independentUpperColumn,if_pos (And.intro hd (hc powers hp))]
  change (∑ powers∈table.support,MvPolynomial.coeff powers table •
    independentUpperColumn C n beta operator charts cutoff depth powers)=_
  rw [hcolumns]
  change _ = truncate _ _ (∑ powers∈table.support,MvPolynomial.coeff powers table •
    (independentGlobalQuotient C n beta operator charts (mixedMonomialSeed powers) depth-
      MvPolynomial.X (mixedMonomialSeed powers)))
  ext powers
  simp only [MvPolynomial.coeff_sum,MvPolynomial.coeff_smul,coeff_truncate]
  split_ifs <;> simp

/-- This is the original restricted and truncated response operator, not an
unrestricted replacement.  The domain hypotheses are its genuine invariant. -/
theorem independentUpperLinear_polynomial_congr
    (first second : Table (InputSeed (Fin (Parameters.modulus n))))
    (hcfirst : InputTableCanonical (actualPrimaryLaw C n beta) (actualBodyLaw C n beta) first)
    (hcsecond : InputTableCanonical (actualPrimaryLaw C n beta) (actualBodyLaw C n beta) second)
    (htfirst : truncate (fun seed => seed.primaryOrder+seed.bodyOrder) cutoff first=first)
    (htsecond : truncate (fun seed => seed.primaryOrder+seed.bodyOrder) cutoff second=second)
    (heq : ∀ primary body : Fin (Parameters.modulus n) → Table (Fin (Parameters.modulus n)⊕Fin (Parameters.modulus n)),
      inputKernelPolynomialHom primary body first=inputKernelPolynomialHom primary body second)
    (primary body : Fin (Parameters.modulus n) → Table Output) :
    inputKernelPolynomialHom primary body (independentUpperLinear C n beta operator charts cutoff depth first)=
      inputKernelPolynomialHom primary body (independentUpperLinear C n beta operator charts cutoff depth second) := by
  rw [independentUpperLinear_eq_truncate_raw C n beta operator charts cutoff depth first hcfirst htfirst,
    independentUpperLinear_eq_truncate_raw C n beta operator charts cutoff depth second hcsecond htsecond]
  apply inputKernelPolynomialHom_truncate_congr
  exact independentRawColumnLinear_polynomial_congr C n beta operator charts first second heq _ _ depth

end
end AFT.V7Calibration
