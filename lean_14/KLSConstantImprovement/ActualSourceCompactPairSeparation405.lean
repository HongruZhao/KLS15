import KLSConstantImprovement.ActualSourceLimitFluxPairing405
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! Compact continuous source pairings separate genuine locally
integrable functions.  The source weight is cancelled explicitly. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff NNReal ENNReal
namespace KLSConstantImprovement.ActualSourceCompactPairSeparation405
open KLS ActualBoundedCanonicalSource
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem integral_source_exp_pair_cancel {φ : Space n → ℝ}
    (hφ : Continuous φ) (f ψ : Space n → ℝ) :
    (∫ x, f x * (ψ x * Real.exp (φ x)) ∂potentialMeasure φ) = ∫ x, f x * ψ x := by
  rw [integral_potentialMeasure hφ.measurable]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    calc
      _ = (f x * ψ x) * (Real.exp (φ x) * Real.exp (-φ x)) := by ring
      _ = _ := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

theorem ae_eq_of_source_compact_pairs {φ f g : Space n → ℝ}
    (hφ : Continuous φ) (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume)
    (hpair : ∀ ψ : Space n → ℝ, Continuous ψ → HasCompactSupport ψ →
      (∫ x, f x * ψ x ∂potentialMeasure φ) = ∫ x, g x * ψ x ∂potentialMeasure φ) :
    f =ᵐ[volume] g := by
  apply ae_eq_of_integral_contDiff_smul_eq hf hg
  intro ψ hψ hc
  have he := hpair (fun x => ψ x * Real.exp (φ x))
    (hψ.continuous.mul (Real.continuous_exp.comp hφ)) hc.mul_right
  rw [integral_source_exp_pair_cancel hφ, integral_source_exp_pair_cancel hφ] at he
  simpa only [smul_eq_mul, mul_comm] using he

end KLSConstantImprovement.ActualSourceCompactPairSeparation405
#print axioms KLSConstantImprovement.ActualSourceCompactPairSeparation405.integral_source_exp_pair_cancel
#print axioms KLSConstantImprovement.ActualSourceCompactPairSeparation405.ae_eq_of_source_compact_pairs
