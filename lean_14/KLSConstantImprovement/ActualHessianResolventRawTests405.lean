import KLSConstantImprovement.ActualSourceMatrixResolvent405
import KLSConstantImprovement.ActualSourceLocalWeakCalculus405
import KLSConstantImprovement.ActualSourceResolventPoisson405
import KLSConstantImprovement.ActualLocalBoundedWeakAlgebra405

/-! Actual bounded raw weak tests representing the conservative Hessian
resolvent. The mean is restored explicitly, while its derivative comes
from the genuine ordinary graph embedding of the centered resolvent. -/
noncomputable section
open MeasureTheory Matrix Filter Set
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualHessianResolventRawTests405
open KLS ActualBoundedCanonicalSource ActualSourceMatrixResolvent405 ActualSourceConservativeResolvent405
open ActualCanonicalMetricResolvent ActualCanonicalMetricEnergyGraph ActualSourceLocalWeakCalculus405
open ActualLocalBoundedWeakAlgebra405 ActualWeakCanonicalMetricOrdinaryGraph
open ActualSourceResolventPoisson405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {n : ℕ} {μ : Measure (Space n)}

def actualHessianResolventForm (d : SourceData μ) (i j : Fin n) : CanonicalMetricH1 d.potential :=
  canonicalResolventH1 d.potential (t := 1) zero_lt_one (sourceHessianLp d i j)

def actualHessianResolventValue (d : SourceData μ) (i j : Fin n) (x : Space n) : ℝ :=
  (∫ y, sourceHessianLp d i j y ∂potentialMeasure d.potential) +
    canonicalMetricValue d.potential (actualHessianResolventForm d i j) x

theorem actualHessianResolventValue_ae (d : SourceData μ) (i j : Fin n) :
    actualHessianResolventValue d i j =ᵐ[potentialMeasure d.potential]
      (sourceMatrixResolvent d (sourceHessianLp d) i j : Space n → ℝ) :=
  (sourceConservativeResolvent_ae d (t := 1) zero_lt_one (sourceHessianLp d i j)).symm

theorem actualHessianResolventValue_memLp_top (d : SourceData μ) (i j : Fin n) :
    MemLp (actualHessianResolventValue d i j) ∞ (potentialMeasure d.potential) := by
  have hk : MemLp (sourceMatrixResolvent d (sourceHessianLp d) i j : Space n → ℝ) ∞
      (potentialMeasure d.potential) :=
    memLp_top_of_bound (Lp.memLp _).aestronglyMeasurable (16 / d.targetConvexityConstant)
      (actualHessianResolvent_entry_bound d i j)
  exact (memLp_congr_ae (actualHessianResolventValue_ae d i j)).mpr hk

def actualHessianResolventLocalTest (d : SourceData μ) (i j : Fin n) : LocalRawTest n where
  value := actualHessianResolventValue d i j
  derivative := sourceWeakGradient d (actualHessianResolventForm d i j)
  value_local_top := fun E hE => KLS.MemLp.restrict_volume_of_potentialMeasure
    (actualHessianResolventValue_memLp_top d i j) d.source_C1.continuous hE
  derivative_local := fun a E hE => KLS.MemLp.restrict_volume_of_potentialMeasure
    (show MemLp (sourceWeakGradient d (actualHessianResolventForm d i j) a) 2
      (potentialMeasure d.potential) from Lp.memLp _) d.source_C1.continuous hE
  weak_derivative := by
    intro a
    let U := actualHessianResolventForm d i j
    let m := ∫ y, sourceHessianLp d i j y ∂potentialMeasure d.potential
    have hu : LocallyIntegrable (canonicalMetricValue d.potential U) volume :=
      locallyIntegrable_of_memLp_two_on_compacts fun E hE => KLS.MemLp.restrict_volume_of_potentialMeasure
        (Lp.memLp _) d.source_C1.continuous hE
    have hp : LocallyIntegrable (sourceWeakGradient d U a) volume :=
      locallyIntegrable_of_memLp_two_on_compacts fun E hE => KLS.MemLp.restrict_volume_of_potentialMeasure
        (show MemLp (sourceWeakGradient d U a) 2 (potentialMeasure d.potential) from Lp.memLp _)
          d.source_C1.continuous hE
    have hh := (hasLocalWeakCoordinateDerivative_const m a).add
      (sourceWeakGradient_hasLocalWeakDerivative d U a)
      (continuous_const.locallyIntegrable : LocallyIntegrable (fun _ : Space n => m) volume)
      hu (continuous_const.locallyIntegrable : LocallyIntegrable (fun _ : Space n => (0 : ℝ)) volume) hp
    have hh' : HasLocalWeakCoordinateDerivative (fun x => m + canonicalMetricValue d.potential U x)
        (sourceWeakGradient d U a) a :=
      hh.congr_ae EventuallyEq.rfl (Eventually.of_forall fun x => zero_add _)
    convert hh' using 1
    all_goals rfl

theorem actualHessianResolventLocalTest_metric_memLp (d : SourceData μ) (i j r : Fin n) :
    MemLp (ActualCompactRawMetricGraph.rawCanonicalMetricDerivative d.potential
      (actualHessianResolventLocalTest d i j).derivative r) 2 (potentialMeasure d.potential) :=
  (memLp_congr_ae (raw_metric_sourceWeakGradient_ae d (actualHessianResolventForm d i j) r)).mpr (Lp.memLp _)

end KLSConstantImprovement.ActualHessianResolventRawTests405

#print axioms KLSConstantImprovement.ActualHessianResolventRawTests405.actualHessianResolventLocalTest
#print axioms KLSConstantImprovement.ActualHessianResolventRawTests405.actualHessianResolventLocalTest_metric_memLp
